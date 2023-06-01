/* Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
 *
 * This source code is licensed under the Apache 2.0 license found in
 * the LICENSE file in the root directory of this source tree.
 */
use std::cmp::Eq;
use std::fmt;

use num_bigint::BigInt;
use rand::distributions::DistString;
use rand::prelude::IteratorRandom;
use rand::Rng;
use rand::SeedableRng;
use rand_distr::Binomial;
use rand_distr::Distribution;
use rand_distr::WeightedIndex;

use crate::ast::BinaryOperator::*;
use crate::ast::UnaryOperator::*;
use crate::ast::*;
use crate::context::*;
use crate::core_types::*;
use crate::environment::CallLocality::*;
use crate::environment::Determinism::*;
use crate::environment::GuardContext::*;
use crate::environment::ReuseSafety::*;
use crate::environment::ScopeClosureBehavior::*;
use crate::environment::Shadowing::*;
use crate::environment::*;
use crate::types::TypeApproximation::*;
use crate::types::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, clap::ValueEnum)]
pub enum WrapperMode {
    Default,
    ForInfer,
    Printing,
}
impl fmt::Display for WrapperMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WrapperMode::Default => write!(f, "default"),
            WrapperMode::ForInfer => write!(f, "for-infer"),
            WrapperMode::Printing => write!(f, "printing"),
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Config {
    pub wrapper_mode: WrapperMode,
    pub max_size: ASTSize,
    pub max_recursion_depth: u16,
    pub disable_shadowing: bool,
    pub disable_maybe: bool,
    pub disable_map_comprehensions: bool,
    pub deterministic: bool,
}

fn choose_arity<RngType: rand::Rng>(rng: &mut RngType) -> usize {
    let bin = Binomial::new(100, 0.03).unwrap();
    bin.sample(rng).try_into().unwrap()
}

pub fn gen_module(module_name: &str, seed: u64, config: Config) -> Module {
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(seed);

    // We choose the number of functions to generate ahead of time to allow the generation of recursive cycles.
    // For the same reason, we choose ahead of time their arities, argument types and return types.
    let num_functions: usize = if config.wrapper_mode == WrapperMode::Printing {
        1
    } else {
        rng.gen_range(1..=10)
    };
    let mut bound_functions: Vec<FunctionDeclaration> = Vec::new();
    for i in 0..num_functions {
        let fun_num = i + 1;
        let name = "f".to_string() + &fun_num.to_string();
        let num_arity_variants = if config.wrapper_mode == WrapperMode::Printing {
            1
        } else {
            rng.gen_range(1..=3)
        };
        let mut arities = make_vec(num_arity_variants, || choose_arity(&mut rng));
        arities.sort_unstable();
        arities.dedup();
        for arity in arities {
            let num_clauses: usize = if arity > 0 { rng.gen_range(1..=5) } else { 1 };
            let clause_types = make_vec(num_clauses, || gen_clause_type(&mut rng, arity));
            let function_type = join_function_types(&clause_types);
            bound_functions.push(FunctionDeclaration {
                name: name.clone(),
                arity,
                clauses: Vec::new(),
                clause_types,
                function_type,
                exported: rng.gen::<bool>(),
                visible_spec: rng.gen::<bool>(),
            });
        }
    }

    let num_function_decls = bound_functions.len();
    let mut module = Module::new(module_name, seed, config, bound_functions);
    let ctx = Context::from_config(&config);
    let mut env = Environment::new(&module, config.disable_shadowing);
    for i in 0..num_function_decls {
        gen_function(&mut rng, &mut module, ctx, &mut env, i);
    }

    match config.wrapper_mode {
        WrapperMode::Default => {
            let start_function = gen_start_function(&mut rng, &mut module, &mut env);
            module.functions.push(start_function);
        }
        WrapperMode::ForInfer => {
            for i in 0..num_function_decls {
                if module.functions[i].arity == 0 {
                    continue;
                }
                let wrapper_function =
                    gen_wrapper_function(&mut rng, &mut module, &mut env, i, config.wrapper_mode);
                module.functions.push(wrapper_function);
            }
        }
        WrapperMode::Printing => {
            assert!(num_function_decls == 1);
            let wrapper_function =
                gen_wrapper_function(&mut rng, &mut module, &mut env, 0, config.wrapper_mode);
            module.functions.push(wrapper_function);
        }
    }

    module
}

fn gen_clause_type<RngType: rand::Rng>(
    rng: &mut RngType,
    arity: usize,
) -> FunctionTypeApproximation {
    let return_type = choose_type(rng);
    let arg_types = make_vec(arity, || choose_type(rng));
    FunctionTypeApproximation {
        return_type,
        arg_types,
    }
}

// Calls every function exactly once, with the call protected by a catch expression.
fn gen_start_function<RngType: rand::Rng>(
    rng: &mut RngType,
    module: &mut Module,
    env: &mut Environment,
) -> FunctionDeclaration {
    let mut exprs = Vec::new();
    let num_func_decl = module.functions.len();
    for func_decl_index in 0..num_func_decl {
        let arity = module.functions[func_decl_index].arity;
        let name = module.functions[func_decl_index].name.clone();
        let ctx = Context::new();
        let mut size = 1;
        let args = make_vec(arity, || {
            recurse_any_expr(Any, rng, module, ctx, env, &mut size)
        });
        let call = module.add_expr(Expr::LocalCall(name, args), Any);
        exprs.push(module.add_expr(Expr::Catch(call), Any));
    }
    let body = module.add_body(Body { exprs });
    let name = "start".to_owned();
    make_trivial_function_from_body(module, body, name)
}

// Calls a given function exactly once
// ForInfer => nothing around the call, e.g. f0(a, b)
// Printing => io:write + catch + some code to remove details of exceptions
//   e.g. io:write(case catch f0(a, b) of
//     {'EXIT', _} -> 'EXIT';
//     _V1 -> _V1
//   end)
//   This removal of stacktraces is required because they are imprecise in interpreter mode for badarith
//   , see https://github.com/erlang/otp/issues/6697#issuecomment-1385608959
//   I've also found exceptions imprecise in other cases, for example in case of <<3.14/integer, 0.123/utf8>>,
//   the (invalid) bitstring elements will be checked either left-to-right or right-to-left depending on the execution mode,
//   resulting in slightly different errors.
fn gen_wrapper_function<RngType: rand::Rng>(
    rng: &mut RngType,
    module: &mut Module,
    env: &mut Environment,
    func_decl_index: usize,
    wrapper: WrapperMode,
) -> FunctionDeclaration {
    let arity = module.functions[func_decl_index].arity;
    let name = module.functions[func_decl_index].name.clone();
    let ctx = Context::new();
    let mut size = 1;
    let args = make_vec(arity, || {
        recurse_any_expr(Any, rng, module, ctx, env, &mut size)
    });
    let inner_call = module.add_expr(Expr::LocalCall(name, args), Any);
    let outer_call = match wrapper {
        WrapperMode::ForInfer => inner_call,
        WrapperMode::Printing => {
            let catch_expr = module.add_expr(Expr::Catch(inner_call), Any);
            let p_exit = module.add_pattern(Pattern::Atom("'EXIT'".to_string()));
            let p_underscore = module.add_pattern(Pattern::Underscore());
            let p1 = module.add_pattern(Pattern::Tuple(vec![p_exit, p_underscore]));
            let g1 = module.add_guard_seq(GuardSeq::default());
            let e1 = module.add_expr(Expr::Atom("'EXIT'".to_string()), Atom);
            let b1 = module.add_body(Body { exprs: vec![e1] });
            let p_default = module.add_pattern(Pattern::NamedVar(1));
            let g2 = module.add_guard_seq(GuardSeq::default());
            let e_default = module.add_expr(Expr::Var(1), Any);
            let b2 = module.add_body(Body {
                exprs: vec![e_default],
            });
            let case_expr = module.add_expr(
                Expr::Case(catch_expr, vec![(p1, g1, b1), (p_default, g2, b2)]),
                Any,
            );
            module.add_expr(
                Expr::RemoteCall("io".to_string(), "write".to_string(), vec![case_expr]),
                Any,
            )
        }
        _ => unreachable!(),
    };
    let body = module.add_body(Body {
        exprs: vec![outer_call],
    });
    let name = format!("wrapper{}", func_decl_index);
    make_trivial_function_from_body(module, body, name)
}

fn make_trivial_function_from_body(
    module: &mut Module,
    body: BodyId,
    name: String,
) -> FunctionDeclaration {
    let guard = module.add_guard_seq(GuardSeq { guards: Vec::new() });
    let clause_id = module.add_function_clause(FunctionClause {
        name: name.clone(),
        args: Vec::new(),
        guard,
        body,
    });
    let function_type = FunctionTypeApproximation {
        return_type: Any,
        arg_types: Vec::new(),
    };
    FunctionDeclaration {
        clauses: vec![clause_id],
        name,
        arity: 0,
        clause_types: vec![function_type.clone()],
        function_type,
        exported: true,
        visible_spec: false,
    }
}

pub fn make_vec<T, F>(n: usize, mut f: F) -> Vec<T>
where
    F: FnMut() -> T,
{
    let mut v = Vec::with_capacity(n);
    for _i in 0..n {
        v.push(f());
    }
    v
}

pub fn choose_type<RngType: rand::Rng>(rng: &mut RngType) -> TypeApproximation {
    [
        Any, Integer, Float, Number, Tuple, Atom, List, Boolean, Map, Bitstring, Fun, Pid, Port,
        Ref, Bottom,
    ]
    .into_iter()
    .choose(rng)
    .unwrap()
}

fn gen_function<RngType: rand::Rng>(
    rng: &mut RngType,
    module: &mut Module,
    ctx: Context,
    env: &mut Environment,
    func_decl_index: usize,
) {
    let arity = module.functions[func_decl_index].arity;
    let name = module.functions[func_decl_index].name.clone();
    let num_clauses: usize = module.functions[func_decl_index].clause_types.len();
    module.functions[func_decl_index]
        .clauses
        .reserve_exact(num_clauses);
    for i in 0..num_clauses {
        env.with_single_scope(NoShadowing, Discard(SafeToReuse), |env| {
            let clause_type = module.functions[func_decl_index].clause_types[i].clone();
            let clause_id =
                gen_function_clause(rng, module, ctx, env, name.clone(), arity, &clause_type);
            module.functions[func_decl_index].clauses.push(clause_id);
        });
    }
}

fn gen_function_clause<RngType: rand::Rng>(
    rng: &mut RngType,
    module: &mut Module,
    ctx: Context,
    env: &mut Environment,
    name: String,
    arity: usize,
    clause_type: &FunctionTypeApproximation,
) -> FunctionClauseId {
    let mut size = 1;
    // These two scopes go together, and are a trick to easily have Overwrite/Union with a multi-scope (not supported otherwise)
    let args = env.with_single_scope(Shadowing, Overwrite, |env| {
        env.with_multi_scope_auto(
            MultiScopeKind::Pattern,
            NoShadowing,
            SafeToReuse,
            KeepUnion,
            arity,
            |env, i| {
                let ctx = if env.disable_shadowing {
                    ctx.ban_bound_vars()
                } else {
                    ctx
                };
                recurse_any_pattern(clause_type.arg_types[i], rng, module, ctx, env, &mut size)
            },
        )
    });

    let guard = gen_guard_seq(
        rng,
        module,
        ctx.for_recursion_with_spent_size(size).with_type(Boolean),
        env,
        &mut size,
    );

    let body = gen_body(
        rng,
        module,
        ctx.for_recursion_with_spent_size(size)
            .with_type(clause_type.return_type),
        env,
        &mut size,
    );
    module.add_function_clause(FunctionClause {
        name,
        args,
        guard,
        body,
    })
}

fn choose_weighted<T: Copy, F: Fn(T) -> u32, RngType: rand::Rng>(
    rng: &mut RngType,
    choices: &[T],
    f: F,
) -> Option<T> {
    let weights = choices.iter().copied().map(f);
    let dist = WeightedIndex::new(weights).ok()?;
    let index = dist.sample(rng);
    Some(choices[index])
}

#[derive(Debug, Copy, Clone)]
enum PatternKind {
    Nil,
    Atom,
    Boolean,
    Integer,
    Float,
    Underscore,
    UnboundVariable,
    // fully bound variables, but also those that are only bound in a parallel pattern
    UsedVariable,
    EqualPatterns,
    Tuple,
    List,
    Bitstring,
    Map,
}

const ALL_PATTERN_KINDS: &[PatternKind] = &[
    PatternKind::Nil,
    PatternKind::Atom,
    PatternKind::Boolean,
    PatternKind::Integer,
    PatternKind::Float,
    PatternKind::Underscore,
    PatternKind::UnboundVariable,
    PatternKind::UsedVariable,
    PatternKind::EqualPatterns,
    PatternKind::Tuple,
    PatternKind::List,
    PatternKind::Bitstring,
    PatternKind::Map,
];

fn pattern_kind_weight(kind: PatternKind) -> u32 {
    match kind {
        PatternKind::Nil => 1,
        PatternKind::Atom => 1,
        PatternKind::Boolean => 1,
        PatternKind::Integer => 1,
        PatternKind::Float => 1,
        PatternKind::Underscore => 1,
        PatternKind::UnboundVariable => 3,
        PatternKind::UsedVariable => 2,
        PatternKind::EqualPatterns => 1,
        PatternKind::Tuple => 1,
        PatternKind::List => 1,
        PatternKind::Bitstring => 1,
        PatternKind::Map => 1,
    }
}

fn is_pattern_kind_allowed_by_context(kind: PatternKind, ctx: Context) -> bool {
    match kind {
        PatternKind::Nil => ctx.allows_type(List),
        PatternKind::Atom => ctx.allows_type(Atom),
        PatternKind::Boolean => ctx.allows_type(Boolean),
        PatternKind::Integer => ctx.allows_type(Integer),
        PatternKind::Float => ctx.allows_type(Float),
        PatternKind::Underscore => true,
        PatternKind::UnboundVariable => !ctx.is_in_guard,
        PatternKind::UsedVariable => !ctx.no_bound_vars,
        PatternKind::EqualPatterns => ctx.may_recurse(),
        PatternKind::Tuple => ctx.may_recurse() && ctx.allows_type(Tuple),
        PatternKind::List => ctx.may_recurse() && ctx.allows_type(List),
        PatternKind::Bitstring => ctx.allows_type(Bitstring),
        PatternKind::Map => ctx.allows_type(Map),
    }
}

fn pick_pattern_kind<RngType: rand::Rng>(
    rng: &mut RngType,
    ctx: Context,
    kinds: &[PatternKind],
) -> PatternKind {
    choose_weighted(rng, kinds, |kind| {
        if is_pattern_kind_allowed_by_context(kind, ctx) {
            pattern_kind_weight(kind)
        } else {
            0
        }
    })
    .unwrap()
}

fn recurse_any_pattern<RngType: rand::Rng>(
    wanted_type: TypeApproximation,
    rng: &mut RngType,
    module: &mut Module,
    ctx: Context,
    env: &mut Environment,
    size_to_incr: &mut ASTSize,
) -> PatternId {
    // Occasionally generate completely/trivially ill-typed patterns on purpose.
    let wanted_type = if rng.gen_bool(0.01) { Any } else { wanted_type };
    let ctx = ctx
        .with_type(wanted_type)
        .for_recursion_with_spent_size(*size_to_incr);
    let kind = pick_pattern_kind(rng, ctx, ALL_PATTERN_KINDS);
    gen_pattern(rng, module, ctx, env, size_to_incr, kind)
}

fn gen_pattern<RngType: rand::Rng>(
    rng: &mut RngType,
    m: &mut Module,
    ctx: Context,
    env: &mut Environment,
    size_to_incr: &mut ASTSize,
    kind: PatternKind,
) -> PatternId {
    let mut size = 1;
    let pattern = match kind {
        PatternKind::Nil => Pattern::Nil(),
        PatternKind::Boolean => Pattern::Atom(if rng.gen::<bool>() {
            "true".to_string()
        } else {
            "false".to_string()
        }),
        PatternKind::Atom => Pattern::Atom(choose_random_atom(rng)),
        PatternKind::Integer => Pattern::Integer(choose_random_integer(rng)),
        PatternKind::Float => Pattern::Float(choose_random_double(rng)),
        PatternKind::Underscore => Pattern::Underscore(),
        PatternKind::UsedVariable => match env.pick_used_var_for_pattern(rng, &ctx.expected_type) {
            Some((v, _t)) => Pattern::NamedVar(v),
            None => Pattern::Underscore(),
        },
        PatternKind::UnboundVariable => {
            Pattern::NamedVar(env.make_fresh_var(rng, ctx.expected_type))
        }
        PatternKind::EqualPatterns => {
            env.with_multi_scope_manual(MultiScopeKind::Pattern, NoShadowing, KeepUnion, |env| {
                let p1 = recurse_any_pattern(ctx.expected_type, rng, m, ctx, env, &mut size);
                env.shift_to_sibling(SafeToReuse);
                let p2 = recurse_any_pattern(ctx.expected_type, rng, m, ctx, env, &mut size);
                Pattern::EqualPatterns(p1, p2)
            })
        }
        PatternKind::Tuple => {
            let arity = choose_arity(rng);
            let elements = env.with_multi_scope_auto(
                MultiScopeKind::Pattern,
                NoShadowing,
                SafeToReuse,
                KeepUnion,
                arity,
                |env, _| recurse_any_pattern(Any, rng, m, ctx, env, &mut size),
            );
            Pattern::Tuple(elements)
        }
        PatternKind::List => {
            env.with_multi_scope_manual(MultiScopeKind::Pattern, NoShadowing, KeepUnion, |env| {
                let head = recurse_any_pattern(Any, rng, m, ctx, env, &mut size);
                env.shift_to_sibling(SafeToReuse);
                let tail = recurse_any_pattern(List, rng, m, ctx, env, &mut size);
                Pattern::List(head, tail)
            })
        }
        PatternKind::Bitstring => {
            let arity = choose_arity(rng);
            let mut elements = Vec::new();
            for i in 0..arity {
                let kind = pick_type_specifier_kind(rng);
                // We choose the size expression before the pattern, to avoid using variables bound in the pattern
                let size_expr = match kind {
                    TypeSpecifierKind::Utf8
                    | TypeSpecifierKind::Utf16
                    | TypeSpecifierKind::Utf32 => None,
                    _ if i == arity - 1 && !ctx.is_in_bitstring_generator && rng.gen::<bool>() => {
                        None
                    }
                    _ => Some(recurse_any_expr(
                        Integer,
                        rng,
                        m,
                        ctx.in_guard(),
                        env,
                        &mut size,
                    )),
                };

                // "When matching Value, value must be either a variable or an integer, or a floating point literal. Expressions are not allowed."
                // Underscore counts as a special kind of variable and is valid in this context.
                let value_ctx = ctx.with_type(type_specifier_kind_to_type_approximation(kind));
                let value_kind = pick_pattern_kind(
                    rng,
                    value_ctx,
                    &[
                        PatternKind::Integer,
                        PatternKind::Underscore,
                        PatternKind::UnboundVariable,
                        PatternKind::UsedVariable,
                    ],
                );
                let sub_pattern = gen_pattern(rng, m, value_ctx, env, &mut size, value_kind);
                let type_specifiers =
                    gen_type_specifier(rng, kind, &size_expr, /* signedness_allowed = */ true);
                elements.push((sub_pattern, size_expr, type_specifiers));
                if size_expr.is_none() {
                    // "In matching, this default value is only valid for the last element.
                    //  All other bit string or binary elements in the matching must have a size specification."
                    break;
                }
            }
            Pattern::Bitstring(elements)
        }
        PatternKind::Map => {
            let arity = choose_arity(rng);
            let pairs = env.with_multi_scope_auto(
                MultiScopeKind::Pattern,
                NoShadowing,
                SafeToReuse,
                KeepUnion,
                arity,
                |env, _| {
                    let k = recurse_any_expr(Any, rng, m, ctx.in_guard(), env, &mut size);
                    let v = recurse_any_pattern(Any, rng, m, ctx, env, &mut size);
                    (k, v)
                },
            );
            Pattern::Map(pairs)
        }
    };
    *size_to_incr += pattern.size(m);
    m.add_pattern(pattern)
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum ExprKind {
    Nil,
    Var,
    Integer,
    Float,
    String,
    BooleanLiteral,
    AtomFunctionName,
    AtomOther,
    LocalCall,
    RemoteCall,
    Tuple,
    Catch,
    Comparison,
    UnaryIntegerBNot,
    UnaryBooleanNot,
    UnaryNumberOp,
    BinaryIntegerOp,
    BinaryNumberOp,
    BinaryBooleanOp,
    BinaryListOp,
    ShortCircuitOp,
    Case,
    Assignment,
    MapLiteral,
    MapInsertion,
    MapUpdate,
    BitstringConstruction,
    ListComprehension,
    BitstringComprehension,
    MapComprehension,
    Fun,
    Try,
    Maybe,
    Block,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum ComprehensionElementKind {
    Filter,
    ListGenerator,
    BitstringGenerator,
    MapGenerator,
}

const ALL_EXPR_KINDS: &[ExprKind] = &[
    ExprKind::Nil,
    ExprKind::Integer,
    ExprKind::Float,
    ExprKind::String,
    ExprKind::BooleanLiteral,
    ExprKind::AtomFunctionName,
    ExprKind::AtomOther,
    ExprKind::Var,
    ExprKind::LocalCall,
    ExprKind::RemoteCall,
    ExprKind::Tuple,
    ExprKind::Catch,
    ExprKind::Comparison,
    ExprKind::UnaryIntegerBNot,
    ExprKind::UnaryBooleanNot,
    ExprKind::UnaryNumberOp,
    ExprKind::BinaryNumberOp,
    ExprKind::BinaryIntegerOp,
    ExprKind::BinaryBooleanOp,
    ExprKind::BinaryListOp,
    ExprKind::ShortCircuitOp,
    ExprKind::Case,
    ExprKind::Assignment,
    ExprKind::MapLiteral,
    ExprKind::MapInsertion,
    ExprKind::MapUpdate,
    ExprKind::BitstringConstruction,
    ExprKind::ListComprehension,
    ExprKind::BitstringComprehension,
    ExprKind::MapComprehension,
    ExprKind::Fun,
    ExprKind::Try,
    ExprKind::Maybe,
    ExprKind::Block,
];

fn expr_kind_weight(kind: ExprKind) -> u32 {
    match kind {
        ExprKind::Nil => 2,
        ExprKind::Integer => 2,
        ExprKind::Float => 1,
        ExprKind::String => 2,
        ExprKind::BooleanLiteral => 1,
        ExprKind::AtomFunctionName => 1,
        ExprKind::AtomOther => 2,
        ExprKind::Var => 10,
        ExprKind::LocalCall => 3,
        ExprKind::RemoteCall => 2,
        ExprKind::Tuple => 3,
        ExprKind::Catch => 1,
        ExprKind::Comparison => 3,
        ExprKind::UnaryIntegerBNot => 1,
        ExprKind::UnaryBooleanNot => 1,
        ExprKind::UnaryNumberOp => 1,
        ExprKind::BinaryNumberOp => 2,
        ExprKind::BinaryIntegerOp => 2,
        ExprKind::BinaryBooleanOp => 1,
        ExprKind::BinaryListOp => 1,
        ExprKind::ShortCircuitOp => 1,
        ExprKind::Case => 1,
        ExprKind::Assignment => 2,
        ExprKind::MapLiteral => 1,
        ExprKind::MapInsertion => 1,
        ExprKind::MapUpdate => 1,
        ExprKind::BitstringConstruction => 1,
        ExprKind::ListComprehension => 1,
        ExprKind::BitstringComprehension => 1,
        ExprKind::MapComprehension => 1,
        ExprKind::Fun => 1,
        ExprKind::Try => 1,
        ExprKind::Maybe => 1,
        ExprKind::Block => 1,
    }
}

fn is_expr_kind_allowed_by_context(kind: ExprKind, ctx: Context) -> bool {
    match kind {
        ExprKind::Nil => ctx.allows_type(List),
        ExprKind::Integer => ctx.allows_type(Integer),
        ExprKind::Float => ctx.allows_type(Float),
        ExprKind::String => ctx.allows_type(List),
        ExprKind::BooleanLiteral => ctx.allows_type(Boolean),
        ExprKind::AtomFunctionName => ctx.allows_type(Atom),
        ExprKind::AtomOther => ctx.allows_type(Atom),
        ExprKind::Var => true,
        ExprKind::LocalCall => ctx.may_recurse(), // allowed in guards because of bifs
        ExprKind::RemoteCall => ctx.may_recurse() && !ctx.is_in_guard,
        ExprKind::Tuple => ctx.may_recurse() && ctx.allows_type(Tuple),
        // stacktraces are imprecise in interpreter mode, and captured by catch
        ExprKind::Catch => ctx.may_recurse() && !ctx.is_in_guard && !ctx.deterministic,
        ExprKind::Comparison => ctx.may_recurse() && ctx.allows_type(Boolean),
        ExprKind::UnaryIntegerBNot => ctx.may_recurse() && ctx.allows_type(Integer),
        ExprKind::UnaryBooleanNot => ctx.may_recurse() && ctx.allows_type(Boolean),
        ExprKind::UnaryNumberOp => ctx.may_recurse() && ctx.allows_type(Number),
        ExprKind::BinaryNumberOp => ctx.may_recurse() && ctx.allows_type(Number),
        ExprKind::BinaryIntegerOp => ctx.may_recurse() && ctx.allows_type(Integer),
        ExprKind::BinaryBooleanOp => ctx.may_recurse() && ctx.allows_type(Boolean),
        ExprKind::BinaryListOp => ctx.may_recurse() && ctx.allows_type(List) && !ctx.is_in_guard,
        ExprKind::ShortCircuitOp => ctx.may_recurse(),
        ExprKind::Case => ctx.may_recurse() && !ctx.is_in_guard,
        ExprKind::Assignment => ctx.may_recurse() && !ctx.is_in_guard,
        ExprKind::MapLiteral => ctx.allows_type(Map),
        ExprKind::MapInsertion => ctx.may_recurse() && ctx.allows_type(Map),
        ExprKind::MapUpdate => ctx.may_recurse() && ctx.allows_type(Map),
        ExprKind::BitstringConstruction => ctx.allows_type(Bitstring), // may_recurse is not required, as it can be empty
        ExprKind::ListComprehension => {
            ctx.may_recurse() && !ctx.is_in_guard && ctx.allows_type(List)
        }
        ExprKind::BitstringComprehension => {
            ctx.may_recurse() && !ctx.is_in_guard && ctx.allows_type(Bitstring)
        }
        ExprKind::MapComprehension => {
            ctx.may_recurse()
                && !ctx.is_in_guard
                && ctx.allows_type(Map)
                && ctx.map_comprehensions_are_allowed
        }
        ExprKind::Fun => ctx.may_recurse() && !ctx.is_in_guard && ctx.allows_type(Fun),
        ExprKind::Try => ctx.may_recurse() && !ctx.is_in_guard,
        ExprKind::Maybe => ctx.may_recurse() && !ctx.is_in_guard && ctx.maybe_is_allowed,
        ExprKind::Block => ctx.may_recurse() && !ctx.is_in_guard,
    }
}

fn pick_expr_kind<RngType: rand::Rng>(
    rng: &mut RngType,
    ctx: Context,
    kinds: &[ExprKind],
) -> ExprKind {
    let maybe_kind = choose_weighted(rng, kinds, |kind| {
        if is_expr_kind_allowed_by_context(kind, ctx) {
            expr_kind_weight(kind)
        } else {
            0
        }
    });
    match maybe_kind {
        Some(kind) => kind,
        // This case can happen if we pick a type like Pid while in a guard
        None => pick_expr_kind(rng, ctx.with_type(Any), kinds),
    }
}

fn recurse_any_expr<RngType: rand::Rng>(
    wanted_type: TypeApproximation,
    rng: &mut RngType,
    module: &mut Module,
    ctx: Context,
    env: &mut Environment,
    size_to_incr: &mut ASTSize,
) -> ExprId {
    // Occasionally generate completely/trivially ill-typed expressions on purpose.
    let wanted_type = if rng.gen_bool(0.01) { Any } else { wanted_type };
    let ctx = ctx
        .with_type(wanted_type)
        .for_recursion_with_spent_size(*size_to_incr);
    let mut available_kinds = Vec::from(ALL_EXPR_KINDS);
    loop {
        let kind = pick_expr_kind(rng, ctx, &available_kinds);
        match gen_expr(rng, module, ctx, env, size_to_incr, kind) {
            Some(e_id) => return e_id,
            None => remove_element(&mut available_kinds, &kind),
        }
    }
}

fn remove_element<T: Eq>(vec: &mut Vec<T>, element: &T) {
    for (index, e) in vec.iter().enumerate() {
        if e == element {
            vec.swap_remove(index);
            return;
        }
    }
    unreachable!();
}

// May fail for some expr kinds depending on the environment
fn gen_expr<RngType: rand::Rng>(
    rng: &mut RngType,
    m: &mut Module,
    ctx: Context,
    env: &mut Environment,
    size_to_incr: &mut ASTSize,
    choice: ExprKind,
) -> Option<ExprId> {
    let mut size = 1;
    let expr_id = match choice {
        ExprKind::Nil => m.add_expr(Expr::Nil(), List),
        ExprKind::Var => match env.pick_bound_var(rng, &ctx.expected_type) {
            Some((v, t)) => m.add_expr(Expr::Var(v), t),
            None => return None,
        },
        ExprKind::Integer => m.add_expr(Expr::Integer(choose_random_integer(rng)), Integer),
        ExprKind::Float => m.add_expr(Expr::Float(choose_random_double(rng)), Float),
        ExprKind::String => {
            let length = rand_distr::Geometric::new(0.1).unwrap().sample(rng);
            // Standard distribution generates all valid unicode code points, which turns out to create strings rejected by the compiler.
            // See https://github.com/erlang/otp/issues/6952 for what this can of worms looks like.
            // So for now, I'm sticking with [a-zA-Z0-9]*, rather than try anything smarter.
            let s = rand_distr::Alphanumeric.sample_string(rng, length.try_into().unwrap());
            m.add_expr(Expr::String(s), List)
        }
        ExprKind::AtomFunctionName => {
            let name = m.functions.iter().choose(rng).unwrap().name.clone();
            m.add_expr(Expr::Atom(name), Atom)
        }
        ExprKind::AtomOther => m.add_expr(Expr::Atom(choose_random_atom(rng)), Atom),
        ExprKind::BooleanLiteral => {
            let boolean = ["true", "false"].iter().choose(rng).unwrap();
            m.add_expr(Expr::Atom(boolean.to_string()), Boolean)
        }
        ExprKind::LocalCall => {
            let in_guard = match ctx.is_in_guard {
                true => InGuard,
                false => NotInGuard,
            };
            let determinism = match ctx.deterministic {
                true => DeterministicOnly,
                false => AnyDeterminism,
            };
            let maybe_fun_information =
                env.pick_function(rng, &ctx.expected_type, determinism, in_guard, Local);
            let (name, function_type) = match maybe_fun_information {
                None => return None,
                Some(FunctionInformation { name, t, .. }) => (name.clone(), t.clone()),
            };
            let arity = function_type.arg_types.len();
            let args = env.with_multi_scope_auto(
                MultiScopeKind::Expr,
                NoShadowing,
                NotSafeToReuse,
                KeepUnion,
                arity,
                |env, i| recurse_any_expr(function_type.arg_types[i], rng, m, ctx, env, &mut size),
            );
            m.add_expr(Expr::LocalCall(name, args), function_type.return_type)
        }
        ExprKind::RemoteCall => {
            let determinism = match ctx.deterministic {
                true => DeterministicOnly,
                false => AnyDeterminism,
            };
            let maybe_fun_information =
                env.pick_function(rng, &ctx.expected_type, determinism, NotInGuard, Remote);
            let (module_name, name, function_type) = match maybe_fun_information {
                None => return None,
                Some(FunctionInformation {
                    module_name,
                    name,
                    t,
                    ..
                }) => (module_name.clone(), name.clone(), t.clone()),
            };
            let arity = function_type.arg_types.len();
            let args = env.with_multi_scope_auto(
                MultiScopeKind::Expr,
                NoShadowing,
                NotSafeToReuse,
                KeepUnion,
                arity,
                |env, i| recurse_any_expr(function_type.arg_types[i], rng, m, ctx, env, &mut size),
            );
            m.add_expr(
                Expr::RemoteCall(module_name, name, args),
                function_type.return_type,
            )
        }
        ExprKind::Tuple => {
            let arity = choose_arity(rng);
            let args = env.with_multi_scope_auto(
                MultiScopeKind::Expr,
                NoShadowing,
                NotSafeToReuse,
                KeepUnion,
                arity,
                |env, _| recurse_any_expr(Any, rng, m, ctx, env, &mut size),
            );
            m.add_expr(Expr::Tuple(args), Tuple)
        }
        ExprKind::Case => {
            let e = recurse_any_expr(Any, rng, m, ctx, env, &mut size);
            let cases = gen_cases(*m.expr_type(e), rng, m, ctx, env, &mut size);
            m.add_expr(Expr::Case(e, cases), Any)
        }
        ExprKind::Try => {
            // See https://github.com/erlang/otp/issues/6598 for the scoping rules involved in this construct.
            // The most tricky is the combination of these things:
            //   1) variables bound in the `try` section are bound in the `of` section
            //   2) variables bound in the `of` section are free in the `catch` section.
            //   3)   but they are unsafe afterwards!
            // I cannot think of a way to have 1 and 2, or to have 2 and 3.
            // So I give up on 2 to have 1 and 3.
            let (exprs, of) = env.with_single_scope(NoShadowing, Discard(NotSafeToReuse), |env| {
                let exprs = gen_body(
                    rng,
                    m,
                    ctx.for_recursion_with_spent_size(size),
                    env,
                    &mut size,
                );

                let of = if rng.gen::<bool>() {
                    Some(gen_cases(*m.body_type(exprs), rng, m, ctx, env, &mut size))
                } else {
                    None
                };
                (exprs, of)
            });

            // "The of, catch, and after sections are all optional, as long as there is at least a catch or an after section."
            let (emit_catch, emit_after) = [(true, true), (true, false), (false, true)]
                .into_iter()
                .choose(rng)
                .unwrap();

            let catch = if emit_catch {
                // FIXME: this is not perfect, it should also sometimes generate classes and stacktraces
                Some(
                    env.with_single_scope(NoShadowing, Discard(NotSafeToReuse), |env| {
                        gen_cases(Any, rng, m, ctx, env, &mut size)
                    }),
                )
            } else {
                None
            };

            let after = if emit_after {
                Some(
                    env.with_single_scope(NoShadowing, Discard(NotSafeToReuse), |env| {
                        gen_body(
                            rng,
                            m,
                            ctx.for_recursion_with_spent_size(size),
                            env,
                            &mut size,
                        )
                    }),
                )
            } else {
                None
            };

            m.add_expr(Expr::Try(exprs, of, catch, after), Any)
        }
        ExprKind::Maybe => {
            // "None of the variables bound in a maybe block must be used in the else clauses.
            //  None of the variables bound in the else clauses must be used in the code that follows the maybe block."
            // and "None of the variables bound in a maybe block must be used in the code that follows the block."
            let arity = choose_arity(rng) + 1;
            let exprs = env.with_single_scope(NoShadowing, Discard(NotSafeToReuse), |env| {
                make_vec(arity, || {
                    if rng.gen::<bool>() {
                        let e = recurse_any_expr(Any, rng, m, ctx, env, &mut size);
                        // TODO: should be the type of e instead
                        let p = recurse_any_pattern(Any, rng, m, ctx, env, &mut size);
                        MaybeExpr::MaybeAssignment(p, e)
                    } else {
                        let e = recurse_any_expr(Any, rng, m, ctx, env, &mut size);
                        MaybeExpr::Normal(e)
                    }
                })
            });

            let else_section = if rng.gen::<bool>() {
                Some(
                    env.with_single_scope(NoShadowing, Discard(NotSafeToReuse), |env| {
                        gen_cases(Any, rng, m, ctx, env, &mut size)
                    }),
                )
            } else {
                None
            };
            m.add_expr(Expr::Maybe(exprs, else_section), Any)
        }
        ExprKind::Catch => {
            // Bindings in a catch expression are always unsafe to use out of it
            env.with_single_scope(NoShadowing, Discard(NotSafeToReuse), |env| {
                let arg = recurse_any_expr(ctx.expected_type, rng, m, ctx, env, &mut size);
                m.add_expr(Expr::Catch(arg), *m.expr_type(arg))
            })
        }
        ExprKind::Comparison => {
            let op = [Eq, NEq, LTE, LT, GTE, GT, ExactlyEq, ExactlyNEq]
                .into_iter()
                .choose(rng)
                .unwrap();
            env.with_multi_scope_manual(MultiScopeKind::Expr, NoShadowing, KeepUnion, |env| {
                let e1 = recurse_any_expr(Any, rng, m, ctx, env, &mut size);
                env.shift_to_sibling(NotSafeToReuse);
                let e2 = recurse_any_expr(Any, rng, m, ctx, env, &mut size);
                m.add_expr(Expr::BinaryOperation(op, e1, e2), Boolean)
            })
        }
        ExprKind::BinaryIntegerOp => {
            let op = [Div, Rem, BAnd, BOr, BXor, BSl, BSr]
                .into_iter()
                .choose(rng)
                .unwrap();
            env.with_multi_scope_manual(MultiScopeKind::Expr, NoShadowing, KeepUnion, |env| {
                let e1 = recurse_any_expr(Integer, rng, m, ctx, env, &mut size);
                env.shift_to_sibling(NotSafeToReuse);
                let e2 = recurse_any_expr(Integer, rng, m, ctx, env, &mut size);
                m.add_expr(Expr::BinaryOperation(op, e1, e2), Integer)
            })
        }
        ExprKind::BinaryNumberOp => {
            let op = [BinaryPlus, BinaryMinus, Mult, Slash]
                .into_iter()
                .choose(rng)
                .unwrap();
            env.with_multi_scope_manual(MultiScopeKind::Expr, NoShadowing, KeepUnion, |env| {
                let e1 = recurse_any_expr(Number, rng, m, ctx, env, &mut size);
                env.shift_to_sibling(NotSafeToReuse);
                let e2 = recurse_any_expr(Number, rng, m, ctx, env, &mut size);
                m.add_expr(Expr::BinaryOperation(op, e1, e2), Number)
            })
        }
        ExprKind::BinaryBooleanOp => {
            let op = [And, Or, Xor].into_iter().choose(rng).unwrap();
            env.with_multi_scope_manual(MultiScopeKind::Expr, NoShadowing, KeepUnion, |env| {
                let e1 = recurse_any_expr(Boolean, rng, m, ctx, env, &mut size);
                env.shift_to_sibling(NotSafeToReuse);
                let e2 = recurse_any_expr(Boolean, rng, m, ctx, env, &mut size);
                m.add_expr(Expr::BinaryOperation(op, e1, e2), Boolean)
            })
        }
        ExprKind::BinaryListOp => {
            let op = [PlusPlus, MinusMinus].into_iter().choose(rng).unwrap();
            env.with_multi_scope_manual(MultiScopeKind::Expr, NoShadowing, KeepUnion, |env| {
                let e1 = recurse_any_expr(List, rng, m, ctx, env, &mut size);
                env.shift_to_sibling(NotSafeToReuse);
                let e2 = recurse_any_expr(List, rng, m, ctx, env, &mut size);
                m.add_expr(Expr::BinaryOperation(op, e1, e2), List)
            })
        }
        ExprKind::ShortCircuitOp => {
            let e1 = recurse_any_expr(Boolean, rng, m, ctx, env, &mut size);
            // Important: after `false orelse (X = 42)`, X is not set !
            let e2 = env.with_single_scope(NoShadowing, Discard(NotSafeToReuse), |env| {
                recurse_any_expr(ctx.expected_type, rng, m, ctx, env, &mut size)
            });
            let op = [AndAlso, OrElse].iter().choose(rng).unwrap();
            m.add_expr(
                Expr::BinaryOperation(*op, e1, e2),
                type_union(&Boolean, &ctx.expected_type),
            )
        }
        ExprKind::UnaryIntegerBNot => {
            let e = recurse_any_expr(Integer, rng, m, ctx, env, &mut size);
            m.add_expr(Expr::UnaryOperation(BitwiseNot, e), Integer)
        }
        ExprKind::UnaryBooleanNot => {
            let e = recurse_any_expr(Boolean, rng, m, ctx, env, &mut size);
            m.add_expr(Expr::UnaryOperation(BooleanNot, e), Boolean)
        }
        ExprKind::UnaryNumberOp => {
            let e = recurse_any_expr(Number, rng, m, ctx, env, &mut size);
            let op = [UnaryPlus, UnaryMinus].iter().choose(rng).unwrap();
            m.add_expr(Expr::UnaryOperation(*op, e), Number)
        }
        ExprKind::Assignment => {
            // Note that we build the expression before the pattern to match the order in which variables are assigned
            // In particular, `<<A:B>> = begin B = 8, <<42:8>> end` works.
            let e = recurse_any_expr(ctx.expected_type, rng, m, ctx, env, &mut size);
            let t = m.expr_type(e).clone();
            let p = recurse_any_pattern(t, rng, m, ctx, env, &mut size);
            m.add_expr(Expr::Assignment(p, e), t)
        }
        ExprKind::MapLiteral => {
            let arity = if ctx.may_recurse() {
                choose_arity(rng)
            } else {
                0
            };
            let mappings = env.with_multi_scope_auto(
                MultiScopeKind::Expr,
                NoShadowing,
                NotSafeToReuse,
                KeepUnion,
                arity,
                |env, _| {
                    let k = recurse_any_expr(Any, rng, m, ctx, env, &mut size);
                    env.shift_to_sibling(NotSafeToReuse);
                    let v = recurse_any_expr(Any, rng, m, ctx, env, &mut size);
                    (k, v)
                },
            );
            m.add_expr(Expr::MapLiteral(mappings), Map)
        }
        ExprKind::MapInsertion => {
            env.with_multi_scope_manual(MultiScopeKind::Expr, NoShadowing, KeepUnion, |env| {
                let map = recurse_any_expr(Map, rng, m, ctx, env, &mut size);
                env.shift_to_sibling(NotSafeToReuse);
                let k = recurse_any_expr(Any, rng, m, ctx, env, &mut size);
                env.shift_to_sibling(NotSafeToReuse);
                let v = recurse_any_expr(Any, rng, m, ctx, env, &mut size);
                m.add_expr(Expr::MapInsertion(map, k, v), Map)
            })
        }
        ExprKind::MapUpdate => {
            env.with_multi_scope_manual(MultiScopeKind::Expr, NoShadowing, KeepUnion, |env| {
                let map = recurse_any_expr(Map, rng, m, ctx, env, &mut size);
                env.shift_to_sibling(NotSafeToReuse);
                let k = recurse_any_expr(Any, rng, m, ctx, env, &mut size);
                env.shift_to_sibling(NotSafeToReuse);
                let v = recurse_any_expr(Any, rng, m, ctx, env, &mut size);
                m.add_expr(Expr::MapUpdate(map, k, v), Map)
            })
        }
        ExprKind::BitstringConstruction => {
            // FIXME: abstract away this pattern
            let arity = if ctx.may_recurse() {
                choose_arity(rng)
            } else {
                0
            };
            let elements = env.with_multi_scope_auto(
                MultiScopeKind::Expr,
                NoShadowing,
                NotSafeToReuse,
                KeepUnion,
                arity,
                |env, _| {
                    let kind = pick_type_specifier_kind(rng);
                    let t = type_specifier_kind_to_type_approximation(kind);
                    let value = recurse_any_expr(t, rng, m, ctx, env, size_to_incr);
                    env.shift_to_sibling(NotSafeToReuse);
                    let size_expr = match kind {
                        TypeSpecifierKind::Utf8
                        | TypeSpecifierKind::Utf16
                        | TypeSpecifierKind::Utf32 => None,
                        _ if rng.gen::<bool>() => None,
                        _ => Some(recurse_any_expr(Integer, rng, m, ctx, env, size_to_incr)),
                    };
                    let specifier = gen_type_specifier(
                        rng, kind, &size_expr, /* signedness_allowed = */ false,
                    );
                    (value, size_expr, specifier)
                },
            );
            m.add_expr(Expr::BitstringConstruction(elements), Bitstring)
        }
        ExprKind::ListComprehension | ExprKind::BitstringComprehension => {
            // Note: the scoping rules for comprehensions are both subtle and poorly documented
            // See https://github.com/erlang/otp/issues/6454 for an example
            // Here are the rules as I've been able to find from tests and the documentation:
            // - Variables bound in a generator expression are only available in that expression
            // - Variables bound by a generator pattern shadow any previously existing variable,
            //     and are scoped until the end of the whole comprehension.
            // - Variables bound in the final expression are also only usable within it
            // Note that a pattern on the right-side of "<-" is not allowed to shadow existing variables,
            //   only patterns on the left side are allowed to do so!
            // Also note that while expressions in generators have special rules, expressions in filters follow the normal rules !
            let arity = choose_arity(rng) + 1;
            let mut elements = Vec::new();
            let value = env.with_single_scope(NoShadowing, Discard(SafeToReuse), |env| {
                for _i in 0..arity {
                    elements.push(gen_comprehension_element(rng, m, ctx, env, &mut size));
                }
                // TODO: for Bitstring kind, type should be one of Number or Bitstring
                recurse_any_expr(Any, rng, m, ctx, env, &mut size)
            });

            match choice {
                ExprKind::ListComprehension => m.add_expr(
                    Expr::Comprehension(ComprehensionKind::List, value, elements),
                    List,
                ),
                ExprKind::BitstringComprehension => m.add_expr(
                    Expr::Comprehension(ComprehensionKind::Bitstring, value, elements),
                    Bitstring,
                ),
                _ => unreachable!(),
            }
        }
        ExprKind::MapComprehension => {
            let arity = choose_arity(rng) + 1;
            let mut elements = Vec::new();
            let (key, value) = env.with_single_scope(NoShadowing, Discard(SafeToReuse), |env| {
                for _i in 0..arity {
                    elements.push(gen_comprehension_element(rng, m, ctx, env, &mut size));
                }
                env.with_multi_scope_manual(MultiScopeKind::Expr, NoShadowing, KeepUnion, |env| {
                    let k = recurse_any_expr(Any, rng, m, ctx, env, &mut size);
                    env.shift_to_sibling(NotSafeToReuse);
                    let v = recurse_any_expr(Any, rng, m, ctx, env, &mut size);
                    (k, v)
                })
            });
            m.add_expr(Expr::MapComprehension(key, value, elements), Map)
        }
        ExprKind::Fun => {
            // NoShadowing is important because the function bodies are not allowed to shadow variables from outside the function.
            // Consider the following:
            // ```
            //   catch (X = 42),
            //   fun () -> (X = 43) end
            // ```
            // This is illegal, because X is unsafe to use after the catch, including in the function body
            // .. but it would be safe to match X in the function head/arguments as they are uniquely allowed to shadow previous variables.
            // which is achieved by having a scope with Shadowing in the relevant part of gen_function_clause.
            env.with_single_scope(NoShadowing, Discard(SafeToReuse), |env| {
                // "Variables in a fun head shadow the function name and both shadow variables in the function clause surrounding the fun expression.
                // Variables bound in a fun body are local to the fun body."
                // "the function name is optional and is to be a variable, if any"
                let fun_var_name = env.with_single_scope(Shadowing, Overwrite, |env| {
                    rng.gen::<bool>().then(|| env.make_fresh_var(rng, Fun))
                });
                let fun_name = if let Some(v) = fun_var_name {
                    format!("_V{}", v)
                } else {
                    "".to_string()
                };
                let arity = choose_arity(rng);
                let mut clauses = Vec::new();
                loop {
                    let clause_type = gen_clause_type(rng, arity);
                    clauses.push(
                        // See previous comment for why NoShadowing is important here
                        env.with_single_scope(NoShadowing, Discard(SafeToReuse), |env| {
                            gen_function_clause(
                                rng,
                                m,
                                ctx.for_recursion_with_spent_size(size),
                                env,
                                fun_name.clone(),
                                arity,
                                &clause_type,
                            )
                        }),
                    );
                    if rng.gen::<bool>() {
                        break;
                    }
                }
                m.add_expr(Expr::Fun(fun_var_name, clauses), Fun)
            })
        }
        ExprKind::Block => {
            let b = gen_body(rng, m, ctx, env, &mut size);
            m.add_expr(Expr::Block(b), *m.body_type(b))
        }
    };
    *size_to_incr += expr_id.size(m);
    Some(expr_id)
}

fn choose_random_integer<RngType: rand::Rng>(rng: &mut RngType) -> BigInt {
    [
        BigInt::from(0i32),
        BigInt::from(1i32),
        BigInt::from(-1i32),
        BigInt::from(i32::MIN),
        BigInt::from(i32::MAX),
        BigInt::from(i64::MIN),
        BigInt::from(i64::MAX),
        BigInt::from(u64::MAX),
    ]
    .into_iter()
    .choose(rng)
    .unwrap()
}

fn choose_random_double<RngType: rand::Rng>(rng: &mut RngType) -> f64 {
    let largest_precise_double_integer = (53f64).exp2();
    assert!(
        (largest_precise_double_integer as u64)
            == ((largest_precise_double_integer + 1.0f64) as u64)
    );
    assert!(
        (largest_precise_double_integer as u64)
            > ((largest_precise_double_integer - 1.0f64) as u64)
    );
    // We generate none of +Infinity, -Infinity, NaN, because they are banned in Erlang.
    // See http://erlang.org/pipermail/erlang-questions/2012-February/064728.html
    [
        0.0f64,
        -0.0f64,
        1.0f64,
        -1.0f64,
        largest_precise_double_integer,
        u32::MAX as f64,
        i32::MAX as f64,
        f64::MAX,
        f64::EPSILON,
    ]
    .into_iter()
    .choose(rng)
    .unwrap()
}

fn choose_random_atom<RngType: rand::Rng>(rng: &mut RngType) -> String {
    [
        "ok",
        "error",
        "undefined",
        "foo",
        "'bar'",
        "'foo bar'",
        "' baz '",
        "'làtîn1'",
        "'原子'",
    ]
    .iter()
    .choose(rng)
    .unwrap()
    .to_string()
}

fn gen_cases<RngType: rand::Rng>(
    t: TypeApproximation,
    rng: &mut RngType,
    m: &mut Module,
    ctx: Context,
    env: &mut Environment,
    current_node_size: &mut ASTSize,
) -> Vec<(PatternId, GuardSeqId, BodyId)> {
    let random_arity = choose_arity(rng);
    let arity = if random_arity > 0 { random_arity } else { 1 };
    let cases = env.with_multi_scope_auto(
        MultiScopeKind::Expr,
        NoShadowing,
        SafeToReuse,
        KeepIntersection,
        arity,
        |env, _| {
            let pattern = recurse_any_pattern(t, rng, m, ctx, env, current_node_size);
            let guard_seq = gen_guard_seq(
                rng,
                m,
                ctx.with_type(Boolean)
                    .for_recursion_with_spent_size(*current_node_size),
                env,
                current_node_size,
            );
            let body = gen_body(
                rng,
                m,
                ctx.for_recursion_with_spent_size(*current_node_size),
                env,
                current_node_size,
            );
            (pattern, guard_seq, body)
        },
    );
    cases
}

fn gen_body<RngType: rand::Rng>(
    rng: &mut RngType,
    module: &mut Module,
    ctx: Context,
    env: &mut Environment,
    size_to_incr: &mut ASTSize,
) -> BodyId {
    let mut es = Vec::new();
    let mut size = 1;
    while size < ctx.allowed_size && rng.gen::<bool>() {
        let e = recurse_any_expr(Any, rng, module, ctx, env, &mut size);
        es.push(e);
    }
    let e = recurse_any_expr(ctx.expected_type, rng, module, ctx, env, &mut size);
    es.push(e);
    *size_to_incr += size;
    module.add_body(Body { exprs: es })
}

fn gen_guard_seq<RngType: rand::Rng>(
    rng: &mut RngType,
    module: &mut Module,
    ctx_arg: Context,
    env: &mut Environment,
    size_to_incr: &mut ASTSize,
) -> GuardSeqId {
    assert!(ctx_arg.expected_type == Boolean);
    let ctx = ctx_arg.in_guard();
    let mut guards = Vec::new();
    let mut size = 1;
    while size < ctx.allowed_size && rng.gen::<bool>() {
        let e = recurse_any_expr(Boolean, rng, module, ctx, env, &mut size);
        guards.push(e);
    }
    *size_to_incr += size;
    module.add_guard_seq(GuardSeq { guards })
}

#[derive(Copy, Clone, Debug)]
enum TypeSpecifierKind {
    Default,
    Integer,
    Float,
    Binary,
    Bytes,
    Bitstring,
    Bits,
    Utf8,
    Utf16,
    Utf32,
}

fn pick_type_specifier_kind<RngType: rand::Rng>(rng: &mut RngType) -> TypeSpecifierKind {
    [
        TypeSpecifierKind::Default,
        TypeSpecifierKind::Integer,
        TypeSpecifierKind::Float,
        TypeSpecifierKind::Binary,
        TypeSpecifierKind::Bytes,
        TypeSpecifierKind::Bitstring,
        TypeSpecifierKind::Bits,
        TypeSpecifierKind::Utf8,
        TypeSpecifierKind::Utf16,
        TypeSpecifierKind::Utf32,
    ]
    .into_iter()
    .choose(rng)
    .unwrap()
}

fn type_specifier_kind_to_type_approximation(kind: TypeSpecifierKind) -> TypeApproximation {
    match kind {
        TypeSpecifierKind::Default
        | TypeSpecifierKind::Integer
        | TypeSpecifierKind::Utf8
        | TypeSpecifierKind::Utf16
        | TypeSpecifierKind::Utf32 => Integer,
        TypeSpecifierKind::Float => Float,
        TypeSpecifierKind::Binary
        | TypeSpecifierKind::Bytes
        | TypeSpecifierKind::Bitstring
        | TypeSpecifierKind::Bits => Bitstring,
    }
}

fn gen_type_specifier<RngType: rand::Rng>(
    rng: &mut RngType,
    kind: TypeSpecifierKind,
    size_expr: &Option<ExprId>,
    signedness_allowed: bool,
) -> TypeSpecifier {
    let signedness = if signedness_allowed {
        [Some(Signedness::Signed), Some(Signedness::Unsigned), None]
            .into_iter()
            .choose(rng)
            .unwrap()
    } else {
        None
    };
    let endianness = if rng.gen::<bool>() {
        [Endianness::Big, Endianness::Little, Endianness::Native]
            .into_iter()
            .choose(rng)
    } else {
        None
    };
    let unit = if size_expr.is_some() && rng.gen::<bool>() {
        Some(rng.gen::<u8>())
    } else {
        None
    };
    match kind {
        TypeSpecifierKind::Default => TypeSpecifier::Default {
            signedness,
            endianness,
            unit,
        },
        TypeSpecifierKind::Integer => TypeSpecifier::Integer {
            signedness,
            endianness,
            unit,
        },
        TypeSpecifierKind::Float => TypeSpecifier::Float { endianness, unit },
        TypeSpecifierKind::Binary => TypeSpecifier::Binary,
        TypeSpecifierKind::Bytes => TypeSpecifier::Bytes,
        TypeSpecifierKind::Bitstring => TypeSpecifier::Bitstring,
        TypeSpecifierKind::Bits => TypeSpecifier::Bits,
        TypeSpecifierKind::Utf8 => TypeSpecifier::Utf8,
        TypeSpecifierKind::Utf16 => TypeSpecifier::Utf16 { endianness },
        TypeSpecifierKind::Utf32 => TypeSpecifier::Utf32 { endianness },
    }
}

fn gen_comprehension_element<RngType: rand::Rng>(
    rng: &mut RngType,
    m: &mut Module,
    ctx: Context,
    env: &mut Environment,
    size_to_incr: &mut ASTSize,
) -> ComprehensionElement {
    let mut kinds = vec![
        ComprehensionElementKind::Filter,
        ComprehensionElementKind::ListGenerator,
        ComprehensionElementKind::BitstringGenerator,
    ];
    if ctx.map_comprehensions_are_allowed {
        kinds.push(ComprehensionElementKind::MapGenerator);
    }
    let comprehension_element_kind = kinds.into_iter().choose(rng).unwrap();
    match comprehension_element_kind {
        ComprehensionElementKind::Filter => {
            let e = recurse_any_expr(Boolean, rng, m, ctx, env, size_to_incr);
            ComprehensionElement::Filter(e)
        }
        ComprehensionElementKind::ListGenerator => {
            let e = env.with_single_scope(NoShadowing, Discard(SafeToReuse), |env| {
                recurse_any_expr(List, rng, m, ctx, env, size_to_incr)
            });
            let ctx = if env.disable_shadowing {
                ctx.ban_bound_vars()
            } else {
                ctx
            };
            let p = env.with_single_scope(Shadowing, Overwrite, |env| {
                recurse_any_pattern(Any, rng, m, ctx, env, size_to_incr)
            });
            ComprehensionElement::ListGenerator(p, e)
        }
        ComprehensionElementKind::BitstringGenerator => {
            let e = env.with_single_scope(NoShadowing, Discard(SafeToReuse), |env| {
                recurse_any_expr(Bitstring, rng, m, ctx, env, size_to_incr)
            });
            let ctx = if env.disable_shadowing {
                ctx.ban_bound_vars()
            } else {
                ctx
            };
            let p = env.with_single_scope(Shadowing, Overwrite, |env| {
                gen_pattern(
                    rng,
                    m,
                    ctx.for_recursion_with_spent_size(*size_to_incr)
                        .in_bitstring_generator(),
                    env,
                    size_to_incr,
                    PatternKind::Bitstring,
                )
            });
            ComprehensionElement::BitstringGenerator(p, e)
        }
        ComprehensionElementKind::MapGenerator => {
            let e = env.with_single_scope(NoShadowing, Discard(SafeToReuse), |env| {
                recurse_any_expr(Map, rng, m, ctx, env, size_to_incr)
            });
            let ctx = if env.disable_shadowing {
                ctx.ban_bound_vars()
            } else {
                ctx
            };
            let (k, v) = env.with_single_scope(Shadowing, Overwrite, |env| {
                env.with_multi_scope_manual(
                    MultiScopeKind::Pattern,
                    NoShadowing,
                    KeepUnion,
                    |env| {
                        let k = recurse_any_pattern(Any, rng, m, ctx, env, size_to_incr);
                        env.shift_to_sibling(SafeToReuse);
                        let v = recurse_any_pattern(Any, rng, m, ctx, env, size_to_incr);
                        (k, v)
                    },
                )
            });
            ComprehensionElement::MapGenerator(k, v, e)
        }
    }
}

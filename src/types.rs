/* Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
 *
 * This source code is licensed under the Apache 2.0 license found in
 * the LICENSE file in the root directory of this source tree.
 */

use std::fmt;
use std::iter::zip;

use TypeApproximation::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeApproximation {
    Any,
    Integer,
    Float,
    Number,
    AnyTuple,
    Tuple(Vec<TypeApproximation>),
    Atom,
    List(Box<TypeApproximation>),
    Boolean,
    Map,
    Bitstring,
    Fun,
    Pid,
    Port,
    Ref,
    Bottom,
    EtsTableName,
    EtsTableId,
    EtsTable,
    SpecificAtom(String),
}
impl TypeApproximation {
    pub fn is_subtype_of(&self, other: &Self) -> bool {
        if self == other {
            return true;
        }
        match (self, other) {
            (Bottom, _) => true,
            (_, Any) => true,
            (Integer, Number) => true,
            (Float, Number) => true,
            (Boolean, Atom) => true,
            (Tuple(_), AnyTuple) => true,
            (EtsTableId, EtsTable) => true,
            (EtsTableName, EtsTable) => true,
            (EtsTableName, Atom) => true,
            (SpecificAtom(s), Boolean) if s == "true" || s == "false" => true,
            (SpecificAtom(_), Atom) => true,
            (Tuple(ts1), Tuple(ts2)) if ts1.len() == ts2.len() => ts1
                .iter()
                .zip(ts2.iter())
                .all(|(t1, t2)| t1.is_subtype_of(t2)),
            (List(t1), List(t2)) => t1.is_subtype_of(t2),
            _ => false,
        }
    }
    pub fn refine(&mut self, other: &Self) {
        if self.is_subtype_of(other) {
            return;
        }
        if other.is_subtype_of(self) {
            *self = other.clone();
            return;
        }
        match (self, other) {
            (List(ref mut t1), List(t2)) => {
                t1.refine(t2);
            }
            (Tuple(ref mut ts1), Tuple(ts2)) if ts1.len() == ts2.len() => {
                ts1.iter_mut()
                    .zip(ts2.iter())
                    .for_each(|(t1, t2)| t1.refine(t2));
            }
            (ref mut t @ EtsTable, Atom) | (ref mut t @ Atom, EtsTable) => {
                **t = EtsTableName;
            }
            (ref mut t, _) => {
                **t = Bottom;
            }
        }
    }
}

pub fn write_list_strings<I: Iterator<Item = String>>(
    f: &mut fmt::Formatter<'_>,
    l: I,
    separator: &str,
) -> fmt::Result {
    let mut is_first = true;
    for x in l {
        if !is_first {
            write!(f, "{}", separator)?;
        }
        is_first = false;
        write!(f, "{}", x)?;
    }
    Ok(())
}

impl fmt::Display for TypeApproximation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            List(t) if **t == Any => write!(f, "list()"),
            List(t) => write!(f, "[{}]", t),
            Tuple(ts) => {
                write!(f, "{{")?;
                write_list_strings(f, ts.iter().map(|t| t.to_string()), ", ")?;
                write!(f, "}}")
            }
            Any => write!(f, "term()"),
            Integer => write!(f, "integer()"),
            Float => write!(f, "float()"),
            Number => write!(f, "number()"),
            AnyTuple => write!(f, "tuple()"),
            Atom => write!(f, "atom()"),
            Boolean => write!(f, "boolean()"),
            Map => write!(f, "map()"),
            Bitstring => write!(f, "bitstring()"),
            Fun => write!(f, "fun()"),
            Pid => write!(f, "pid()"),
            Port => write!(f, "port()"),
            Ref => write!(f, "reference()"),
            Bottom => write!(f, "none()"),
            EtsTableName => write!(f, "atom()"),
            EtsTableId => write!(f, "ets:tid()"),
            EtsTable => write!(f, "ets:table()"),
            SpecificAtom(a) => write!(f, "'{}'", a),
        }
    }
}

pub fn type_union(left: &TypeApproximation, right: &TypeApproximation) -> TypeApproximation {
    match (left, right) {
        _ if left.is_subtype_of(right) => right.clone(),
        _ if right.is_subtype_of(left) => left.clone(),
        (Float, Integer) | (Integer, Float) => Number,
        (EtsTableId, EtsTableName) | (EtsTableName, EtsTableId) => EtsTable,
        (List(t1), List(t2)) => List(Box::new(type_union(t1, t2))),
        (Tuple(ts1), Tuple(ts2)) if ts1.len() == ts2.len() => Tuple(
            ts1.iter()
                .zip(ts2.iter())
                .map(|(t1, t2)| type_union(t1, t2))
                .collect::<Vec<_>>(),
        ),
        (Tuple(_ts1), Tuple(_ts2)) => AnyTuple,
        (SpecificAtom(_), SpecificAtom(_))
            if left.is_subtype_of(&Boolean) && right.is_subtype_of(&Boolean) =>
        {
            Boolean
        }
        (SpecificAtom(_), SpecificAtom(_)) => Atom,
        _ => Any,
    }
}

#[derive(Debug, Clone)]
pub struct FunctionTypeApproximation {
    pub return_type: TypeApproximation,
    pub arg_types: Vec<TypeApproximation>,
}

pub fn join_function_types(types: &[FunctionTypeApproximation]) -> FunctionTypeApproximation {
    types
        .iter()
        .cloned()
        .reduce(
            |ft1: FunctionTypeApproximation, ft2: FunctionTypeApproximation| {
                assert!(ft1.arg_types.len() == ft2.arg_types.len());
                FunctionTypeApproximation {
                    return_type: type_union(&ft1.return_type, &ft2.return_type),
                    arg_types: zip(ft1.arg_types.iter(), ft2.arg_types.iter())
                        .map(|(t1, t2)| type_union(t1, t2))
                        .collect::<Vec<_>>(),
                }
            },
        )
        .unwrap()
}

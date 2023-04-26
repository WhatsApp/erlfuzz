/* Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
 *
 * This source code is licensed under the Apache 2.0 license found in
 * the LICENSE file in the root directory of this source tree.
 */

use std::iter::zip;

use TypeApproximation::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum TypeApproximation {
    Any,
    Integer,
    Float,
    Number,
    Tuple,
    Atom,
    List,
    Boolean,
    Map,
    Bitstring,
    Fun,
    Pid,
    Reference,
    Bottom,
}
impl TypeApproximation {
    pub fn is_subtype_of(&self, other: &Self) -> bool {
        (*other == Any)
            || (*self == Integer && *other == Number)
            || (*self == Float && *other == Number)
            || (*self == Boolean && *other == Atom)
            || (self == other)
            || (*self == Bottom)
    }
    pub fn refine(&mut self, other: &Self) {
        if self.is_subtype_of(other) {
            return;
        }
        if other.is_subtype_of(self) {
            *self = *other;
        } else {
            *self = Bottom;
        }
    }
}

pub fn type_union(left: &TypeApproximation, right: &TypeApproximation) -> TypeApproximation {
    match (left, right) {
        _ if left.is_subtype_of(right) => *right,
        _ if right.is_subtype_of(left) => *left,
        (Float, Integer) | (Integer, Float) => Number,
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

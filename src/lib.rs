/* Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
 *
 * This source code is licensed under the Apache 2.0 license found in
 * the LICENSE file in the root directory of this source tree.
 */
#![feature(iter_zip)]

mod ast;
mod context;
mod core_types;
mod environment;
mod generator;
mod reducer;
mod types;

pub use ast::Module;
pub use core_types::ASTSize;
pub use generator::gen_module;
pub use generator::Config;
pub use generator::WrapperMode;
pub use reducer::reduce_module;

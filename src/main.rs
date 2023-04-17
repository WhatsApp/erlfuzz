/* Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
 *
 * This source code is licensed under the Apache 2.0 license found in
 * the LICENSE file in the root directory of this source tree.
 */
use std::fs;
use std::path::PathBuf;
use std::process;

use clap::Parser;
use log::error;
use log::info;
use log::trace;
use log::warn;

const DEFAULT_MAX_SIZE_PER_CLAUSE: erlfuzz::ASTSize = 200;
const DEFAULT_LINES_TO_COMPARE: usize = 3;
const DEFAULT_MAX_OUTPUT_DISTANCE: u32 = 4;
const DEFAULT_MAX_RECURSION_ALLOWED: u16 = 50;

#[derive(clap::Args)]
struct GenerateArgs {
    #[clap(value_parser)]
    module_name: Option<String>,
    #[clap(long, value_parser)]
    seed: Option<u64>,
}

#[derive(clap::Args)]
struct FuzzArgs {
    #[clap(value_parser)]
    module_name: String,
    #[clap(long, value_parser)]
    seed: Option<u64>,
    #[clap(short, long, value_parser)]
    command: String,
    #[clap(long, value_parser)]
    tmp_directory: String,
    #[clap(long, value_parser)]
    interesting_directory: String,
}

#[derive(clap::Args)]
struct ReduceArgs {
    #[clap(value_parser)]
    module_name: String,
    #[clap(short, long, value_parser)]
    seed: u64,
    #[clap(long, value_parser, default_value_t = DEFAULT_LINES_TO_COMPARE)]
    num_lines: usize,
    #[clap(long, value_parser, default_value_t = DEFAULT_MAX_OUTPUT_DISTANCE)]
    max_distance: u32,
    /// Should take the .erl file as argument, and fail on it.
    #[clap(short, long, value_parser)]
    command: String,
    #[clap(long, value_parser)]
    tmp_directory: String,
    #[clap(long, value_parser)]
    minimized_directory: String,
}

#[derive(clap::Subcommand)]
enum Command {
    Generate(GenerateArgs),
    Fuzz(FuzzArgs),
    Reduce(ReduceArgs),
}

#[derive(clap::Parser)]
#[clap(author, version, about, long_about = None)]
#[clap(propagate_version = true)]
struct Cli {
    #[clap(subcommand)]
    command: Command,
    #[clap(long, value_enum, default_value_t = erlfuzz::WrapperMode::Default)]
    wrapper: erlfuzz::WrapperMode,
    #[clap(long, value_parser, default_value_t = DEFAULT_MAX_SIZE_PER_CLAUSE)]
    max_size: erlfuzz::ASTSize,
    #[clap(long, value_parser, default_value_t = DEFAULT_MAX_RECURSION_ALLOWED)]
    max_recursion_depth: u16,
    #[clap(long, value_parser, default_value_t = false)]
    disable_shadowing: bool,
    #[clap(long, value_parser, default_value_t = false)]
    disable_maybe: bool,
    #[clap(long, value_parser, default_value_t = false)]
    disable_map_comprehensions: bool,
    #[clap(long, value_parser, default_value_t = false)]
    deterministic: bool,
}
impl Cli {
    fn to_config(&self) -> erlfuzz::Config {
        let Cli {
            wrapper,
            max_size,
            max_recursion_depth,
            disable_shadowing,
            disable_maybe,
            disable_map_comprehensions,
            deterministic,
            ..
        } = self;
        erlfuzz::Config {
            wrapper_mode: *wrapper,
            max_size: *max_size,
            max_recursion_depth: *max_recursion_depth,
            disable_shadowing: *disable_shadowing,
            disable_maybe: *disable_maybe,
            disable_map_comprehensions: *disable_map_comprehensions,
            deterministic: *deterministic,
        }
    }
}

// Write the module to the given filepath, then run the command on that file.
fn run_command_on_module(
    command: &str,
    module: &erlfuzz::Module,
    filepath: &PathBuf,
) -> std::process::Output {
    match fs::write(&filepath, module.to_string()) {
        Ok(_) => (),
        Err(err) => {
            eprintln!(
                "Error: \"{}\" while attempting to write to {}",
                err,
                filepath.display()
            );
            process::exit(1)
        }
    }
    let result = std::process::Command::new(command)
        .arg(&filepath)
        .stderr(process::Stdio::piped())
        .stdout(process::Stdio::piped())
        .output();
    match result {
        Err(err) => {
            error!(
                "Failed to launch the command on {}, error is {}",
                &filepath.display(),
                err
            );
            process::exit(2);
        }
        Ok(output) => {
            trace!(
                "command stdout:{}",
                std::str::from_utf8(&output.stdout).unwrap()
            );
            trace!(
                "command stderr:{}",
                std::str::from_utf8(&output.stderr).unwrap()
            );
            output
        }
    }
}

fn is_string_prefix_similar(
    content1: &[u8],
    content2: &[u8],
    num_lines: usize,
    distance: u32,
) -> bool {
    let short1 = content1
        .split_inclusive(|c| *c == '\n' as u8)
        .take(num_lines)
        .collect::<Vec<_>>()
        .concat();
    let short2 = content2
        .split_inclusive(|c| *c == '\n' as u8)
        .take(num_lines)
        .collect::<Vec<_>>()
        .concat();
    triple_accel::levenshtein::levenshtein_simd_k(&short1, &short2, distance).is_some()
}

fn is_output_similar(
    output1: &std::process::Output,
    output2: &std::process::Output,
    num_lines: usize,
    distance: u32,
) -> bool {
    // This function is a hacky heuristic.
    // If it returns true even for very different outputs, we'll reduce one compiler failure into another, potentially even from one crash to a harmless compilation error.
    // If it returns false too aggressively, we'll fail to reduce code whenever the error message includes line numbers or the like.
    // What I found to work decently well so far for erlc is to cut everything but the first three lines of output, and check that the edit distance is < 4.
    // But I fully expect that reducing testcases for software with differently formatted error messages will require tweaking this heuristic.
    output1.status == output2.status
        && is_string_prefix_similar(&output1.stdout, &output2.stdout, num_lines, distance)
        && is_string_prefix_similar(&output1.stderr, &output2.stderr, num_lines, distance)
}

fn main() {
    env_logger::init();
    let args = Cli::parse();
    let config = Cli::to_config(&args);
    match args.command {
        Command::Generate(generate_args) => {
            let seed = generate_args.seed.unwrap_or_else(rand::random::<u64>);
            let module_name = generate_args
                .module_name
                .unwrap_or_else(|| "fuzztest".to_string());
            let module = erlfuzz::gen_module(&module_name, seed, config);
            println!("{}", module);
            process::exit(0);
        }
        Command::Fuzz(fuzz_args) => {
            let seed = fuzz_args.seed.unwrap_or_else(rand::random::<u64>);
            let module = erlfuzz::gen_module(&fuzz_args.module_name, seed, config);
            let filename = fuzz_args.module_name.clone() + ".erl";
            let filepath: PathBuf = [&fuzz_args.tmp_directory, &filename].iter().collect();
            let output = run_command_on_module(&fuzz_args.command, &module, &filepath);
            if output.status.success() {
                info!(
                    "{}  judged not interesting, deleted",
                    fuzz_args.module_name.clone()
                );
                std::process::Command::new("rm")
                    .arg(&filepath)
                    .output()
                    .unwrap();
            } else {
                let new_filepath: PathBuf = [&fuzz_args.interesting_directory, &filename]
                    .iter()
                    .collect();
                warn!(
                    "INTERESTING: storing this test case as {}",
                    new_filepath.display()
                );
                std::process::Command::new("mv")
                    .args([&filepath, &new_filepath])
                    .output()
                    .unwrap();
                let stderr_filename = fuzz_args.module_name.clone() + ".stderr";
                let stdout_filename = fuzz_args.module_name.clone() + ".stdout";
                let stderr_filepath = [&fuzz_args.interesting_directory, &stderr_filename]
                    .iter()
                    .collect::<PathBuf>();
                let stdout_filepath = [&fuzz_args.interesting_directory, &stdout_filename]
                    .iter()
                    .collect::<PathBuf>();
                let _ = fs::write(
                    &stderr_filepath,
                    std::str::from_utf8(&output.stderr).unwrap(),
                );
                let _ = fs::write(
                    &stdout_filepath,
                    std::str::from_utf8(&output.stdout).unwrap(),
                );
            }
        }
        Command::Reduce(reduce_args) => {
            let mut module =
                erlfuzz::gen_module(&reduce_args.module_name, reduce_args.seed, config);
            let filename = reduce_args.module_name.clone() + ".erl";
            let filepath: PathBuf = [&reduce_args.tmp_directory, &filename].iter().collect();
            let expected_output = run_command_on_module(&reduce_args.command, &module, &filepath);
            if expected_output.status.success() {
                error!("Error: the command does not fail on the initial module! ");
                process::exit(1);
            }
            erlfuzz::reduce_module(&mut module, &|m| {
                let output = run_command_on_module(&reduce_args.command, m, &filepath);
                std::process::Command::new("rm")
                    .arg(&filepath)
                    .output()
                    .unwrap();
                is_output_similar(
                    &output,
                    &expected_output,
                    reduce_args.num_lines,
                    reduce_args.max_distance,
                )
            });
            let new_filepath: PathBuf = [&reduce_args.minimized_directory, &filename]
                .iter()
                .collect();
            match fs::write(&new_filepath, module.to_string()) {
                Ok(_) => (),
                Err(err) => {
                    error!(
                        "Error: \"{}\" while attempting to write to {}",
                        err,
                        new_filepath.display()
                    );
                    process::exit(3)
                }
            }
        }
    }
}

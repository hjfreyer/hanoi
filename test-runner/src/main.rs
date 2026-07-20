use std::fs;
use std::process;
use std::io::{self, Write};
use clap::Parser;

/// Hanoi Test Runner
#[derive(Parser, Debug)]
#[command(version, about = "Hanoi integration test runner", long_about = None)]
struct Args {
    /// Directory containing main.hana and test files
    directory: String,

    /// Substring filter for test names
    #[arg(long = "test-filter")]
    test_filter: Option<String>,

    /// Enable detailed operation-by-operation tracing
    #[arg(short = 't', long = "trace")]
    trace: bool,
}

fn main() {
    let args = Args::parse();
    
    let path = &args.directory;
    let filter = args.test_filter;
    let trace = args.trace;

    let file_path = std::path::Path::new(&path).join("main.hana");
    if !file_path.exists() {
        eprintln!("Error: Directory '{}' does not contain 'main.hana'", path);
        process::exit(1);
    }

    let code = match fs::read_to_string(&file_path) {
        Ok(content) => content,
        Err(err) => {
            eprintln!("Error reading file '{}': {}", file_path.display(), err);
            process::exit(1);
        }
    };

    let base_dir = file_path.parent();
    let res = match bytecode::assemble_with_path(&code, base_dir) {
        Ok(result) => result,
        Err(err) => {
            eprintln!("Assembly Error:\n{}", err);
            process::exit(1);
        }
    };

    if res.tests.is_empty() {
        println!("No tests found in '{}'.", file_path.display());
        return;
    }

    let total_tests = res.tests.len();

    // Stable sort tests by name for consistent output
    let mut tests: Vec<(&String, &bytecode::SentenceIndex)> = res.tests.iter().collect();
    tests.sort_by_key(|(name, _)| *name);

    if let Some(ref pattern) = filter {
        tests.retain(|(name, _)| name.contains(pattern));
    }

    if tests.is_empty() {
        if let Some(ref pattern) = filter {
            println!("No tests matched the filter '{}'.", pattern);
        } else {
            println!("No tests found in '{}'.", file_path.display());
        }
        return;
    }

    let tests_run = tests.len();
    let filtered_out = total_tests - tests_run;
    println!("Running {} tests...", tests_run);
    let mut failed = 0;

    for (name, &index) in tests {
        if trace {
            println!("test {}", name);
        } else {
            print!("test {} ... ", name);
            io::stdout().flush().unwrap();
        }

        // Each test runs in its own fresh VM instance
        let mut vm = vm::VM::new(res.library.clone());
        vm.set_tracing(trace);
        match vm.execute(index) {
            Ok(()) => {
                if vm.stack().is_empty() {
                    if trace {
                        println!("result: ok");
                    } else {
                        println!("ok");
                    }
                } else {
                    if trace {
                        println!("result: FAILED (stack was not empty: {:?})", vm.stack());
                    } else {
                        println!("FAILED (stack was not empty: {:?})", vm.stack());
                    }
                    failed += 1;
                }
            }
            Err(err) => {
                if trace {
                    println!("result: FAILED ({})", err);
                } else {
                    println!("FAILED ({})", err);
                }
                failed += 1;
            }
        }
    }

    println!();
    if failed > 0 {
        println!(
            "test result: FAILED. {} passed; {} failed; {} filtered out",
            tests_run - failed,
            failed,
            filtered_out
        );
        process::exit(1);
    } else {
        println!(
            "test result: ok. {} passed; 0 failed; {} filtered out",
            tests_run,
            filtered_out
        );
    }
}

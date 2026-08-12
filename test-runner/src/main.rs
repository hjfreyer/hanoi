use clap::Parser;
use std::fs;
use std::io::{self, Write};
use std::process;

/// Hanoi Test Runner
#[derive(Parser, Debug)]
#[command(version, about = "Hanoi integration test runner", long_about = None)]
struct Args {
    /// Directory containing main.hana and test files
    directory: String,

    /// Substring filter for test names
    #[arg(long = "test-filter")]
    test_filter: Option<String>,

    /// Maximum number of VM steps per test case
    #[arg(long = "test-gas", default_value = "10000000")]
    test_gas: u64,

    /// Enable detailed operation-by-operation tracing
    #[arg(short = 't', long = "trace")]
    trace: bool,
}

#[tokio::main]
async fn main() {
    let args = Args::parse();

    let path = &args.directory;
    let filter = args.test_filter;
    let trace = args.trace;
    let gas_limit = args.test_gas;

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
    let mut sources = bytecode::SourceMap::new();
    let root = sources.add_path(&file_path, code);
    let res = match bytecode::assemble_source(&mut sources, root, base_dir) {
        Ok(result) => result,
        Err(err) => {
            eprint!("{}", sources.render(&err));
            process::exit(1);
        }
    };

    let mut all_tests = Vec::new();
    for (name, &idx) in &res.tests {
        all_tests.push((name.clone(), idx, false));
    }
    for name in &res.test_machines {
        all_tests.push((name.clone(), bytecode::SentenceIndex::from(0), true));
    }

    if all_tests.is_empty() {
        println!("No tests found in '{}'.", file_path.display());
        return;
    }

    let total_tests = all_tests.len();

    // Stable sort tests by name for consistent output
    all_tests.sort_by(|a, b| a.0.cmp(&b.0));

    if let Some(ref pattern) = filter {
        all_tests.retain(|(name, _, _)| name.contains(pattern));
    }

    if all_tests.is_empty() {
        if let Some(ref pattern) = filter {
            println!("No tests matched the filter '{}'.", pattern);
        } else {
            println!("No tests found in '{}'.", file_path.display());
        }
        return;
    }

    // Every test reports its verdict with the prelude's symbols: a sentence
    // ends by pushing `pass`, and a machine emits `pass` or `fail`. Resolving
    // them once, up front, keeps a missing prelude from being reported once per
    // test when it is really one problem with the suite.
    let symbol = |name: &str| match res.symbols.get(name).cloned() {
        Some(v) => v,
        None => {
            eprintln!("Error: '{}' symbol not found in '{}'", name, path);
            process::exit(1);
        }
    };
    let start_val = symbol("prelude::start");
    let pass_val = symbol("prelude::pass");
    let fail_val = symbol("prelude::fail");

    let tests_run = all_tests.len();
    let filtered_out = total_tests - tests_run;
    println!("Running {} tests...", tests_run);
    let mut failed = 0;

    for (name, index, is_machine) in all_tests {
        if trace {
            println!("test {}", name);
        } else {
            print!("test {} ... ", name);
            io::stdout().flush().unwrap();
        }

        if is_machine {
            let env = vm::DefaultEnvironment::new(&res);
            let mut runtime = match vm::Runtime::new(res.clone(), &name, env) {
                Ok(rt) => rt,
                Err(err) => {
                    if trace {
                        println!("result: FAILED ({})", err);
                    } else {
                        println!("FAILED ({})", err);
                    }
                    failed += 1;
                    continue;
                }
            };
            runtime.vm_mut().set_tracing(trace);
            runtime.vm_mut().set_gas_limit(Some(gas_limit));

            match runtime.run_test(&start_val, &pass_val, &fail_val).await {
                Ok(()) => {
                    if runtime.vm().stack().is_empty() {
                        if trace {
                            println!("result: ok ({} steps)", runtime.vm().steps_executed());
                        } else {
                            println!("ok ({} steps)", runtime.vm().steps_executed());
                        }
                    } else {
                        if trace {
                            println!(
                                "result: FAILED (stack was not empty: {:?}) ({} steps)",
                                runtime.vm().stack(),
                                runtime.vm().steps_executed()
                            );
                        } else {
                            println!(
                                "FAILED (stack was not empty: {:?}) ({} steps)",
                                runtime.vm().stack(),
                                runtime.vm().steps_executed()
                            );
                        }
                        failed += 1;
                    }
                }
                Err(err) => {
                    if trace {
                        println!(
                            "result: FAILED ({}) ({} steps)",
                            err,
                            runtime.vm().steps_executed()
                        );
                    } else {
                        println!("FAILED ({}) ({} steps)", err, runtime.vm().steps_executed());
                    }
                    failed += 1;
                }
            }
        } else {
            // Each test runs in its own fresh VM instance
            let mut vm = vm::VM::new(res.clone());
            vm.set_tracing(trace);
            vm.set_gas_limit(Some(gas_limit));
            match vm.execute(index) {
                Ok(()) => {
                    // A sentence test says it passed the way a machine test
                    // does: by producing `prelude::pass`. Running to the end
                    // without a verdict is not a pass — a test whose last
                    // assertion was never reached would otherwise be
                    // indistinguishable from one that ran clean.
                    if vm.stack() == std::slice::from_ref(&pass_val) {
                        if trace {
                            println!("result: ok ({} steps)", vm.steps_executed());
                        } else {
                            println!("ok ({} steps)", vm.steps_executed());
                        }
                    } else {
                        if trace {
                            println!(
                                "result: FAILED (stack was not exactly [prelude::pass]: {:?}) ({} steps)",
                                vm.stack(),
                                vm.steps_executed()
                            );
                        } else {
                            println!(
                                "FAILED (stack was not exactly [prelude::pass]: {:?}) ({} steps)",
                                vm.stack(),
                                vm.steps_executed()
                            );
                        }
                        failed += 1;
                    }
                }
                Err(err) => {
                    if trace {
                        println!("result: FAILED ({}) ({} steps)", err, vm.steps_executed());
                    } else {
                        println!("FAILED ({}) ({} steps)", err, vm.steps_executed());
                    }
                    failed += 1;
                }
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
            tests_run, filtered_out
        );
    }
}

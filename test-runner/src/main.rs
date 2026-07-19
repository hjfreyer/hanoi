use std::env;
use std::fs;
use std::process;
use std::io::{self, Write};

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} <directory>", args[0]);
        process::exit(1);
    }

    let path = &args[1];
    let file_path = std::path::Path::new(path).join("main.hana");
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

    println!("Running {} tests...", res.tests.len());
    let mut failed = 0;

    // Stable sort tests by name for consistent output
    let mut tests: Vec<(&String, &bytecode::SentenceIndex)> = res.tests.iter().collect();
    tests.sort_by_key(|(name, _)| *name);

    for (name, &index) in tests {
        print!("test {} ... ", name);
        io::stdout().flush().unwrap();

        // Each test runs in its own fresh VM instance
        let mut vm = vm::VM::new(res.library.clone());
        match vm.execute(index) {
            Ok(()) => {
                if vm.stack().is_empty() {
                    println!("ok");
                } else {
                    println!("FAILED (stack was not empty: {:?})", vm.stack());
                    failed += 1;
                }
            }
            Err(err) => {
                println!("FAILED ({})", err);
                failed += 1;
            }
        }
    }

    println!();
    if failed > 0 {
        println!("test result: FAILED. {} passed; {} failed", res.tests.len() - failed, failed);
        process::exit(1);
    } else {
        println!("test result: ok. {} passed; 0 failed", res.tests.len());
    }
}

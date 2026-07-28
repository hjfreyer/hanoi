use std::env;
use std::fs;
use std::path::Path;
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} <directory>", args[0]);
        process::exit(1);
    }

    let path_arg = &args[1];
    let path = Path::new(path_arg);

    if !path.exists() {
        eprintln!("Error: Path '{}' does not exist", path_arg);
        process::exit(1);
    }

    if !path.is_dir() {
        eprintln!("Error: Path '{}' is not a directory. z3ify only supports directories containing 'main.hana'", path_arg);
        process::exit(1);
    }

    let file_path = path.join("main.hana");

    if !file_path.exists() {
        eprintln!("Error: Directory '{}' does not contain 'main.hana'", path_arg);
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
    let library = match bytecode::assemble_with_path(&code, base_dir) {
        Ok(lib) => lib,
        Err(err) => {
            eprintln!("Assembly FAILED for '{}':\n{}", file_path.display(), err);
            process::exit(1);
        }
    };

    match bytecode::safety::z3ify::generate_z3ify(&library) {
        Ok(smt_script) => {
            print!("{}", smt_script);
            process::exit(0);
        }
        Err(err) => {
            eprintln!("z3ify translation FAILED for '{}':\n{}", file_path.display(), err);
            process::exit(1);
        }
    }
}

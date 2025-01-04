#![allow(unused)]

mod ast;
mod debugger;
mod flat;
mod vm;

use std::{path::PathBuf, process::exit};

use clap::{Parser, Subcommand};
use flat::{Builtin, Closure, Entry, InnerWord, Library, SentenceBuilder, SentenceIndex, Value};
use itertools::Itertools;
use vm::{EvalError, ProgramCounter, Vm};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    Run {
        base_dir: PathBuf,
        module: String,
    },
    Debug {
        base_dir: PathBuf,
        module: String,
        #[arg(long)]
        stdin: Option<PathBuf>,
    },
    Test {
        base_dir: PathBuf,
        module: String,
    },
}

fn run(base_dir: PathBuf, module: String) -> anyhow::Result<()> {
    let mut loader = ast::Loader {
        base: base_dir,
        cache: Default::default(),
    };

    let mut lib = Library::load(&mut loader, &module)?;
    let &Entry::Value(Value::Pointer(Closure(_, main))) = lib.root_namespace().get("main").unwrap()
    else {
        panic!("not code")
    };

    let code = lib.code;
    let mut vm = Vm::new(lib, main);

    vm.jump_to(Closure(
        vec![Value::Pointer(Closure(vec![], SentenceIndex::TRAP))],
        main,
    ));

    let mut res = match vm.run() {
        Ok(res) => res,
        Err(e) => {
            eprintln!("Error: {}\n", e);
            eprintln!("Stack:");
            for v in vm.stack.iter() {
                eprintln!("  {:?}", v)
            }
            exit(1);
        }
    };

    Ok(())
}

fn debug(base_dir: PathBuf, module: String, stdin: Option<PathBuf>) -> anyhow::Result<()> {
    let mut loader = ast::Loader {
        base: base_dir,
        cache: Default::default(),
    };

    let mut lib = Library::load(&mut loader, &module)?;
    let &Entry::Value(Value::Pointer(Closure(_, main))) = lib.root_namespace().get("main").unwrap()
    else {
        panic!("not code")
    };

    let code = lib.code;
    let mut vm = Vm::new(lib, main);

    if let Some(stdin_path) = stdin {
        let stdin = std::fs::File::open(stdin_path)?;
        vm = vm.with_stdin(Box::new(stdin));
    }

    vm.jump_to(Closure(
        vec![Value::Pointer(Closure(vec![], SentenceIndex::TRAP))],
        main,
    ));

    let debugger = debugger::Debugger::new(code, vm);

    let mut terminal = ratatui::init();
    terminal.clear()?;
    let app_result = debugger::run(terminal, debugger);
    ratatui::restore();
    app_result?;
    Ok(())
}

struct IterReader<'a, 't> {
    vm: &'a mut Vm<'t>,
    done: bool,
}

impl<'a, 't> Iterator for IterReader<'a, 't> {
    type Item = Result<Value, EvalError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        let mut res = match self.vm.run_to_trap() {
            Ok(res) => res,
            Err(e) => {
                self.done = true;
                return Some(Err(e));
            }
        };

        let Some(Value::Pointer(mut closure)) = self.vm.stack.pop() else {
            panic!();
        };

        let Some(Value::Symbol(result)) = self.vm.stack.pop() else {
            panic!();
        };

        match result.as_str() {
            "yield" => {
                let item = self.vm.stack.pop().unwrap();
                closure
                    .0
                    .insert(0, Value::Pointer(Closure(vec![], SentenceIndex::TRAP)));
                closure.0.insert(0, Value::Symbol("next".to_owned()));
                self.vm.jump_to(closure);

                Some(Ok(item))
            }
            "eos" => None,
            _ => panic!(),
        }
    }
}

fn test(base_dir: PathBuf, module: String) -> anyhow::Result<()> {
    let mut loader = ast::Loader {
        base: base_dir,
        cache: Default::default(),
    };

    let lib = Library::load(&mut loader, &module)?;
    let code = lib.code;

    let Some(Entry::Namespace(tests_ns)) = lib.namespaces.first().unwrap().get("tests") else {
        panic!("no namespace named tests")
    };
    let Some(Entry::Value(Value::Pointer(enumerate))) = lib.namespaces[*tests_ns].get("enumerate")
    else {
        panic!("no procedure named enumerate")
    };
    assert_eq!(enumerate.0, vec![]);
    let enumerate = enumerate.1;

    let Some(Entry::Value(Value::Pointer(run))) = lib.namespaces[*tests_ns].get("run") else {
        panic!("no procedure named run")
    };
    assert_eq!(run.0, vec![]);
    let run = run.1;

    let mut vm = Vm::new(lib, enumerate);
    vm.jump_to(Closure(
        vec![
            Value::Symbol("next".to_owned()),
            Value::Pointer(Closure(vec![], SentenceIndex::TRAP)),
        ],
        enumerate,
    ));

    for tc in (IterReader {
        vm: &mut vm,
        done: false,
    })
    .collect_vec()
    {
        let value = match tc {
            Ok(value) => value,
            Err(e) => {
                println!("Error enumerating tests: {}", e);
                return Ok(());
            }
        };
        let Value::Symbol(tc_name) = value else {
            panic!()
        };

        println!("Running test: {}", tc_name);

        vm.jump_to(Closure(
            vec![
                Value::Pointer(Closure(vec![], SentenceIndex::TRAP)),
                Value::Symbol(tc_name.clone()),
            ],
            run,
        ));

        let mut res = match vm.run_to_trap() {
            Ok(res) => res,
            Err(e) => {
                eprintln!("Error while running test {}: {}\n", tc_name, e);
                eprintln!("Stack:");
                for v in vm.stack.iter() {
                    eprintln!("  {:?}", v)
                }
                exit(1);
            }
        };

        let Value::Pointer(_) = vm.stack.pop().unwrap() else {
            panic!()
        };

        let Value::Symbol(result) = vm.stack.pop().unwrap() else {
            panic!()
        };

        match result.as_str() {
            "pass" => println!("PASS!"),
            "fail" => {
                println!("FAIL!");
                exit(1);
            }
            _ => panic!(),
        }
    }

    Ok(())
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    match args.command {
        Commands::Run { base_dir, module } => run(base_dir, module),
        Commands::Debug {
            base_dir,
            module,
            stdin,
        } => debug(base_dir, module, stdin),
        Commands::Test { base_dir, module } => test(base_dir, module),
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    // #[test]
    // fn basic_assert() {
    //     let mut vm = Vm::new(lib! {
    //         let true_test = { #true *assert };
    //     });

    //     while vm.step() {}

    //     assert_eq!(vm.stack, vec![Value::Bool(true)])
    // }

    // #[test]
    // fn concrete_generator() {
    //     let mut vm = Vm::new(lib! {
    //         let count = {
    //             // (caller next)
    //             #1 *yield
    //             // (caller next 1 *yield)
    //             mv(3)
    //             // (next 1 caller)
    //             *exec;
    //             #2 *yield mv(3) *exec;
    //             #3 *yield mv(3) *exec;
    //             *ok mv(1) *exec
    //         };

    //         let is_generator_rec = {
    //             // (caller generator self)
    //             copy(1) is_code if {
    //                 // (caller generator self mynext)
    //                 mv(2) *exec;
    //                 // (caller self (iternext X *yield)|(*ok))
    //                 copy(0) *yield eq if {
    //                     // (caller self iternext X *yield)
    //                     drop(0) drop(0) mv(1)
    //                     // (caller iternext self)
    //                     copy(0) *exec
    //                 } else {
    //                     // (caller self *ok)
    //                     *ok eq drop(1) mv(1) *exec
    //                 }
    //             } else {
    //                 // (caller generator self)
    //                 drop(0) drop(0) #false *exec
    //             }
    //         };

    //         let is_generator = {
    //             is_generator_rec is_generator_rec *exec
    //         };

    //         let true_test = {
    //             count is_generator *exec;
    //             *assert
    //         };
    //     });

    //     while vm.step() {
    //         // println!("{:?}", vm.stack)
    //     }

    //     assert_eq!(vm.stack, vec![Value::Bool(true)])
    // }

    // #[test]
    // fn basic_type() {
    //     let mut vm = Vm::new(lib! {
    //         let count_rec = {
    //             // (caller self i)
    //             #1 add
    //             // (caller self (i+1))
    //             copy(0)
    //             // (caller self (i+1) (i+1))
    //             mv(2)
    //             // (caller (i+1) (i+1) self)
    //             mv(2)
    //             // (caller (i+1) self (i+1))
    //             copy(1)
    //             // (caller (i+1) self (i+1) self)
    //             curry
    //             // (caller (i+1) self [(i+1)](self))
    //             curry
    //             // (caller (i+1) [self, (i+1)](self))
    //             mv(1)
    //             // (caller nextiter (i+1))
    //             *yield
    //             // (caller nextiter (i+1) *yield)
    //             mv(3) *exec
    //         };

    //         let count = {
    //             count_rec #0 count_rec *exec
    //         };
    //     });

    //     let mut count_type = vm.lib.decls().last().unwrap().code().eventual_type();

    //     assert_eq!(
    //         count_type,
    //         Type {
    //             arity_in: 1,
    //             arity_out: 5,
    //             judgements: vec![
    //                 Judgement::Eq(0, 1),
    //                 Judgement::OutExact(2, Value::Symbol("yield")),
    //                 Judgement::OutExact(0, Value::Symbol("exec")),
    //             ]
    //         }
    //     )
    // }
}

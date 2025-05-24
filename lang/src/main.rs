#![allow(unused)]

mod ast;
mod compiler;
mod debugger;
#[macro_use]
mod flat;
mod linker;
mod source;
mod vm;

use std::{path::PathBuf, process::exit};

use clap::{Parser, Subcommand};
use flat::{Library, Value};
use itertools::Itertools;

use vm::{EvalError, Vm};

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
    },
    Debug {
        base_dir: PathBuf,
        #[arg(long)]
        stdin: Option<PathBuf>,
    },
    Test {
        base_dir: PathBuf,
    },
}

fn compile_library(base_dir: PathBuf) -> anyhow::Result<(source::Sources, Library)> {
    let loader = source::Loader { base_dir };
    let sources = source::Sources::fully_load(&loader)?;

    let crt = compiler::Crate::from_sources(&sources)?;

    let lib = linker::compile(&sources, crt)?;
    Ok((sources, lib))
}

fn run(base_dir: PathBuf) -> anyhow::Result<()> {
    let (sources, lib) = compile_library(base_dir)?;
    let mut vm = Vm::new(lib);

    vm.load_label("main");

    match vm.run() {
        Ok(res) => res,
        Err(e) => {
            eprintln!("Error: {}\n", e.into_user(&sources));
            eprintln!("Stack:");
            for v in vm.stack.iter() {
                eprintln!("  {:?}", v)
            }
            exit(1);
        }
    };

    Ok(())
}

fn debug(base_dir: PathBuf, stdin: Option<PathBuf>) -> anyhow::Result<()> {
    let (sources, lib) = compile_library(base_dir)?;
    let mut vm = Vm::new(lib);

    if let Some(stdin_path) = stdin {
        let stdin = std::fs::File::open(stdin_path)?;
        vm = vm.with_stdin(Box::new(stdin));
    }

    vm.load_label("main");

    let debugger = debugger::Debugger::new(sources, vm);

    let mut terminal = ratatui::init();
    terminal.clear()?;
    let app_result = debugger::run(terminal, debugger);
    ratatui::restore();
    app_result?;
    Ok(())
}

struct IterReader<'a> {
    vm: &'a mut Vm,
    label: &'a str,
    iter_value: Option<Value>,
    done: bool,
}

impl<'a> Iterator for IterReader<'a> {
    type Item = Result<Value, EvalError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        self.vm
            .push_value(tuple![self.iter_value.take().unwrap(), tagged![next {}]]);
        self.vm.load_label(self.label);
        match self.vm.run() {
            Ok(res) => res,
            Err(e) => {
                self.done = true;
                return Some(Err(e));
            }
        };

        let Some(Value::Tuple(mut t)) = self.vm.stack.pop() else {
            panic!()
        };
        let iter = t.pop().unwrap();
        let Value::Tuple(mut item) = t.pop().unwrap() else {
            panic!()
        };
        assert!(t.is_empty());

        self.iter_value = Some(iter);

        let arg = item.pop().unwrap();
        let Some(Value::Symbol(tag)) = item.pop() else {
            panic!()
        };
        assert!(t.is_empty());

        match tag.as_str() {
            "none" => None,
            "some" => {
                let Value::Tuple(t) = arg else { panic!() };
                Some(Ok(t.into_iter().exactly_one().unwrap()))
            }
            _ => panic!(),
        }
    }
}

fn test(base_dir: PathBuf) -> anyhow::Result<()> {
    let (sources, lib) = compile_library(base_dir)?;
    let mut vm = Vm::new(lib);

    fn run(vm: &mut Vm) -> Result<(), vm::EvalError> {
        vm.push_value(tuple![tagged![nil {}], tagged![enumerate {}]]);
        vm.load_label("test");
        vm.run()?;

        let Some(Value::Tuple(mut t)) = vm.stack.pop() else {
            panic!()
        };
        let iter = t.pop().unwrap();

        let iter = IterReader {
            vm: vm,
            label: "test",
            iter_value: Some(iter),
            done: false,
        };

        let cases = iter.collect::<Result<Vec<Value>, EvalError>>()?;

        for tc in cases {
            let Value::Symbol(tc_name) = &tc else {
                panic!()
            };

            println!("Running test: {}", tc_name);

            vm.push_value(tuple![tagged![nil {}], tagged![run { tc }]]);
            vm.load_label("test");
            vm.run()?;

            let Value::Tuple(t) = vm.stack.pop().unwrap() else {
                panic!()
            };
            assert!(t.is_empty());
            println!("PASS!");
        }
        assert!(vm.stack.is_empty());

        Ok(())
    }
    match run(&mut vm) {
        Ok(_) => Ok(()),
        Err(e) => {
            eprintln!("Error: {}", e.into_user(&sources));
            exit(1);
        }
    }
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    match args.command {
        Commands::Run { base_dir } => run(base_dir),
        Commands::Debug { base_dir, stdin } => debug(base_dir, stdin),
        Commands::Test { base_dir } => test(base_dir),
    }
}

#[cfg(test)]
mod tests {

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

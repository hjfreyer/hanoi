#![allow(unused)]

mod ast;
mod compiler;
mod debugger;
#[macro_use]
mod flat;
mod linker;
mod runtime;
mod source;
mod vm;

use std::{path::PathBuf, process::exit};

use clap::{Parser, Subcommand};
use flat::{Library, Value};
use itertools::Itertools;

use runtime::Runtime;
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
    let main_symbol = lib.export("main").unwrap();
    let mut vm = Vm::new(lib, Runtime {}, main_symbol);
    vm.init();

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
    let main_symbol = lib.export("main").unwrap();
    let mut vm = Vm::new(lib, Runtime {}, main_symbol);

    if let Some(stdin_path) = stdin {
        let stdin = std::fs::File::open(stdin_path)?;
        vm = vm.with_stdin(Box::new(stdin));
    }

    // vm.load_label("main");

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
        // self.vm.load_label(self.label);
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
    let main_symbol = lib.export("test").unwrap();
    let mut vm = Vm::new(lib, Runtime {}, main_symbol);

    fn run(vm: &mut Vm) -> Result<(), vm::EvalError> {
        vm.push_value(tuple![tagged![nil {}], tagged![enumerate {}]]);
        // vm.load_label("test");
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
            // vm.load_label("test");
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

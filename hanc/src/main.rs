use std::path::PathBuf;

use clap::{Parser, Subcommand};
use hanoi::parser::{self, source};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    Compile { base_dir: PathBuf },
}

fn compile(base_dir: PathBuf) -> anyhow::Result<()> {
    let loader = source::Loader { base_dir };
    // let mut sources = source::Sources::default();
    // let main_file_idx = loader.load(PathBuf::from(""), &mut sources)?;
    let sources = parser::load_all(&loader)?;

    // let crt = compiler::Crate::from_sources(&sources)?;

    // let lib = linker::link(&sources, crt)?;

    Ok(())
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    match args.command {
        Commands::Compile { base_dir } => compile(base_dir),
    }
}

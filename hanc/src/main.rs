use std::path::PathBuf;

use anyhow::Context;
use clap::{Parser, Subcommand};
use hanoi::{
    compiler2::{self},
    parser::source,
};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    Compile {
        #[arg(long)]
        base_dir: PathBuf,
        #[arg(long)]
        out_dir: PathBuf,
    },
}

fn compile(base_dir: PathBuf, output_dir: PathBuf) -> anyhow::Result<()> {
    let loader = source::Loader { base_dir };
    let bytecode = compiler2::compile(&loader)?;

    let bytecode_path = output_dir.join("main.hanb.json");
    std::fs::write(bytecode_path, serde_json::to_string_pretty(&bytecode)?)
        .context("Failed to write bytecode")?;

    Ok(())
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    match args.command {
        Commands::Compile {
            base_dir,
            out_dir: output_dir,
        } => compile(base_dir, output_dir),
    }?;

    Ok(())
}

//! Achates: reads C through clang into a typed intermediate representation.

mod clang;
mod compdb;
mod convert;
mod dump;
mod frontend;
mod ir;
mod probe;
mod scan;
mod survey;
mod target;
mod types;

#[cfg(test)]
mod tests;

use std::path::PathBuf;
use std::process::ExitCode;

use anyhow::{Result, bail};
use clap::{Parser, Subcommand};

#[derive(Debug, Parser)]
#[command(version, about)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// One line per function defined in the selected files: fully
    /// represented, or which constructs are not.
    Survey {
        #[arg(long)]
        compile_commands: PathBuf,
        /// Path prefix such as `misc/`, or a glob such as `misc/b*.c`.
        #[arg(long)]
        select: String,
    },
    /// Print one function's IR.
    Dump {
        #[arg(long)]
        compile_commands: PathBuf,
        #[arg(long)]
        select: String,
        #[arg(long)]
        function: String,
        /// Print JSON for programs instead of text for people.
        #[arg(long)]
        json: bool,
    },
}

fn run(cli: Cli) -> Result<String> {
    match cli.command {
        Command::Survey {
            compile_commands,
            select,
        } => {
            let entries = compdb::load(&compile_commands)?;
            let picked = compdb::select(&entries, &select)?;
            Ok(survey::render(&survey::run(&picked)?))
        }
        Command::Dump {
            compile_commands,
            select,
            function,
            json,
        } => {
            let entries = compdb::load(&compile_commands)?;
            let picked = compdb::select(&entries, &select)?;
            let mut out = String::new();
            for e in picked {
                let loaded = frontend::load(e)?;
                for f in loaded.tu.functions.iter().filter(|f| f.name == function) {
                    if json {
                        out.push_str(&dump::json(f, &loaded.tu)?);
                    } else {
                        out.push_str(&dump::function(f, &loaded.tu));
                    }
                }
            }
            if out.is_empty() {
                bail!("no function named `{function}` is defined in the selected files");
            }
            Ok(out)
        }
    }
}

fn main() -> ExitCode {
    match run(Cli::parse()) {
        Ok(out) => {
            print!("{out}");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("achates: {e:#}");
            ExitCode::FAILURE
        }
    }
}

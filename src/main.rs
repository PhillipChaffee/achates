//! Achates: reads C through clang into a typed intermediate representation.

mod clang;
mod compdb;
mod convert;
mod dump;
mod emit;
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
        #[command(flatten)]
        inlines: Inlines,
    },
    /// Write Lean definitions for the selected functions as a Lake project,
    /// and say for each function whether it was emitted and why not.
    Emit {
        #[arg(long)]
        compile_commands: PathBuf,
        #[arg(long)]
        select: String,
        /// Directory of the Lake project to write.
        #[arg(long)]
        out: PathBuf,
        /// Root namespace of the emitted Lean.
        #[arg(long, default_value = "Emitted")]
        name: String,
        /// The Lean runtime the project depends on; defaults to the one in
        /// the Achates source tree this binary was built from.
        #[arg(long)]
        runtime: Option<PathBuf>,
    },
    /// Print one function's IR.
    Dump {
        #[arg(long)]
        compile_commands: PathBuf,
        #[arg(long)]
        select: String,
        #[arg(long)]
        function: String,
        #[command(flatten)]
        inlines: Inlines,
        /// Print JSON for programs instead of text for people.
        #[arg(long)]
        json: bool,
    },
}

#[derive(Debug, clap::Args)]
struct Inlines {
    /// Leave out the header functions with a body that the selected
    /// functions reach through calls; by default they are added.
    #[arg(long)]
    no_reachable_inlines: bool,
}

fn run(cli: Cli) -> Result<String> {
    match cli.command {
        Command::Survey {
            compile_commands,
            select,
            inlines,
        } => {
            let entries = compdb::load(&compile_commands)?;
            let picked = compdb::select(&entries, &select)?;
            let with = !inlines.no_reachable_inlines;
            Ok(survey::render(&survey::run(&picked, with)?))
        }
        Command::Emit {
            compile_commands,
            select,
            out,
            name,
            runtime,
        } => {
            let entries = compdb::load(&compile_commands)?;
            let picked = compdb::select(&entries, &select)?;
            let runtime =
                runtime.unwrap_or_else(|| PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/lean")));
            emit::run(&picked, &emit::Options { out, name, runtime })
        }
        Command::Dump {
            compile_commands,
            select,
            function,
            inlines,
            json,
        } => {
            let entries = compdb::load(&compile_commands)?;
            let picked = compdb::select(&entries, &select)?;
            let mut out = String::new();
            // A header function reached from several files is printed once.
            let mut printed = std::collections::BTreeSet::new();
            for e in picked {
                let loaded = frontend::load(e, !inlines.no_reachable_inlines)?;
                for f in loaded.tu.functions.iter().filter(|f| f.name == function) {
                    if !printed.insert((f.def_file.clone(), f.name.clone())) {
                        continue;
                    }
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

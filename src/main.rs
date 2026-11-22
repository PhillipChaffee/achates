//! Achates: reads C through clang into a typed intermediate representation.

mod check;
mod clang;
mod compdb;
mod convert;
mod dump;
mod emit;
mod equiv;
mod frontend;
mod ir;
mod probe;
mod scan;
mod survey;
mod target;
mod tools;
mod types;

#[cfg(test)]
mod tests;

use std::path::PathBuf;
use std::process::ExitCode;

use anyhow::{Context as _, Result, bail};
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
    /// Write, for each C function with a Rust counterpart in the Aeneas
    /// output, the Lean theorem that the two are equal, and try to prove
    /// each by fixed tactic tiers.
    Equiv(EquivArgs),
    /// Run emitted definitions against the compiled C they came from, on
    /// generated inputs, and say for each function whether they agree.
    Check {
        #[arg(long)]
        compile_commands: PathBuf,
        #[arg(long)]
        select: String,
        /// Root namespace of the emitted Lean.
        #[arg(long, default_value = "Emitted")]
        name: String,
        #[arg(long)]
        runtime: Option<PathBuf>,
        /// Directory for the emitted project, the drivers and their builds.
        #[arg(long, default_value = "target/check")]
        work: PathBuf,
        /// Check only this function; may be given several times.
        #[arg(long = "function")]
        functions: Vec<String>,
        /// Inputs generated per function.
        #[arg(long, default_value_t = 10_000)]
        count: usize,
        #[arg(long, default_value_t = 1)]
        seed: u64,
        /// Most planted bugs tried per function; 0 skips them.
        #[arg(long, default_value_t = 24)]
        mutants: usize,
        /// Functions checked at the same time; defaults to the number of cores.
        #[arg(long)]
        jobs: Option<usize>,
        /// A file with the compiler arguments for the C harness, one per
        /// line, in place of each function's own compile command.
        #[arg(long)]
        cflags_file: Option<PathBuf>,
        /// A file with the linker arguments, one per line: the library
        /// that holds the rest of the program.
        #[arg(long)]
        link_file: Option<PathBuf>,
        /// Where to write the result as JSON.
        #[arg(long)]
        json: Option<PathBuf>,
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
struct EquivArgs {
    #[arg(long)]
    compile_commands: PathBuf,
    #[arg(long)]
    select: String,
    /// The project `achates emit` wrote for the selection.
    #[arg(long)]
    c_project: PathBuf,
    /// The Lean file Aeneas wrote for the port.
    #[arg(long)]
    rust_lean: PathBuf,
    /// The bridge Lake project that builds both sides.
    #[arg(long)]
    lake_dir: PathBuf,
    /// Search for proofs; without it only the statements are written.
    #[arg(long)]
    prove: bool,
    /// Lean processes to run at once.
    #[arg(long, default_value_t = 4)]
    jobs: usize,
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
            let runtime = runtime
                .unwrap_or_else(|| PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/lean")));
            emit::run(&picked, &emit::Options { out, name, runtime })
        }
        Command::Equiv(args) => run_equiv(args),
        Command::Check {
            compile_commands,
            select,
            name,
            runtime,
            work,
            functions,
            count,
            seed,
            mutants,
            jobs,
            cflags_file,
            link_file,
            json,
        } => {
            let entries = compdb::load(&compile_commands)?;
            let picked = compdb::select(&entries, &select)?;
            let opts = check::Options {
                name,
                runtime: runtime
                    .unwrap_or_else(|| PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/lean"))),
                work,
                functions,
                count,
                seed,
                mutants,
                jobs: jobs.unwrap_or_else(|| {
                    std::thread::available_parallelism().map_or(1, std::num::NonZero::get)
                }),
                cflags_file,
                link_file,
            };
            let report = check::run(&picked, &opts, None)?;
            if let Some(path) = json {
                std::fs::write(&path, report.json()?)
                    .with_context(|| format!("writing {}", path.display()))?;
            }
            let summary = report.summary();
            if report.any_disagreement() {
                print!("{summary}");
                bail!("the emitted Lean and the compiled C disagree; see above");
            }
            Ok(summary)
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

fn run_equiv(a: EquivArgs) -> Result<String> {
    let entries = compdb::load(&a.compile_commands)?;
    let picked = compdb::select(&entries, &a.select)?;
    equiv::run(
        &picked,
        &equiv::Options {
            c_project: a.c_project,
            rust_lean: a.rust_lean,
            lake_dir: a.lake_dir,
            prove: a.prove,
            jobs: a.jobs,
        },
    )
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

//! `achates check`: runs every emitted definition against the compiled C
//! function it was emitted from, on generated inputs, and then checks that
//! the comparison notices planted bugs.

mod compare;
mod harness;
mod input;
mod mutate;
mod report;
mod shape;

#[cfg(test)]
mod tests;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs::File;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use anyhow::{Context as _, Result, bail};

use crate::compdb::Entry;
use crate::emit::order::for_each_expr;
use crate::emit::project::{emitted, ext_class};
use crate::emit::{self, Analysis, Row, names};
use crate::ir::{ExprKind, Origin};
use crate::tools;
use compare::Class;
use input::{Dictionary, Gen};
pub(crate) use report::{FnResult, Report, Status};
use shape::{Plan, Shapes};

#[derive(Debug, Clone)]
pub(crate) struct Options {
    /// Root namespace of the emitted Lean.
    pub(crate) name: String,
    pub(crate) runtime: PathBuf,
    /// Directory for everything the check writes and builds.
    pub(crate) work: PathBuf,
    /// Only these functions, by C name; all when empty.
    pub(crate) functions: Vec<String>,
    pub(crate) count: usize,
    pub(crate) seed: u64,
    /// Most mutants tried per function; 0 skips the sensitivity check.
    pub(crate) mutants: usize,
    pub(crate) jobs: usize,
    /// Compiler arguments for the C harness, one per line, in place of the
    /// function's own compile command.
    pub(crate) cflags_file: Option<PathBuf>,
    /// Linker arguments, one per line: where the rest of the program is.
    pub(crate) link_file: Option<PathBuf>,
}

/// A function outside the selection that the check supplies a model for.
#[derive(Debug)]
struct ExtModel {
    name: &'static str,
    lean: &'static str,
    /// The Lean type the model has; a C declaration that maps to another
    /// type is not this function.
    sig: &'static str,
    what: &'static str,
}

const EXT_MODELS: &[ExtModel] = &[
    ExtModel {
        name: "strncasecmp",
        lean: "AchatesCheck.Models.strncasecmp",
        sig: "Ptr → Ptr → U64 → M I32",
        what: "POSIX strncasecmp in the C locale, returning the difference of the lower-cased bytes as glibc does",
    },
    ExtModel {
        name: "strcasecmp",
        lean: "AchatesCheck.Models.strcasecmp",
        sig: "Ptr → Ptr → M I32",
        what: "POSIX strcasecmp in the C locale, returning the difference of the lower-cased bytes as glibc does",
    },
    ExtModel {
        name: "memrchr",
        lean: "AchatesCheck.Models.memrchr",
        sig: "Ptr → I32 → U64 → M Ptr",
        what: "GNU memrchr",
    },
    ExtModel {
        name: "mp_log2",
        lean: "AchatesCheck.Models.mp_log2",
        sig: "U32 → M U32",
        what: "mpv's mp_log2 (common/common.c)",
    },
    ExtModel {
        name: "mp_round_next_power_of_2",
        lean: "AchatesCheck.Models.mp_round_next_power_of_2",
        sig: "U32 → M U32",
        what: "mpv's mp_round_next_power_of_2 (common/common.c)",
    },
    ExtModel {
        name: "ta_xstrndup",
        lean: "AchatesCheck.Models.ta_xstrndup",
        sig: "Ptr → Ptr → U64 → M Ptr",
        what: "talloc's ta_xstrndup (ta/ta_utils.c); allocation never fails",
    },
    ExtModel {
        name: "ta_xstrdup",
        lean: "AchatesCheck.Models.ta_xstrdup",
        sig: "Ptr → Ptr → M Ptr",
        what: "talloc's ta_xstrdup (ta/ta_utils.c); allocation never fails",
    },
    ExtModel {
        name: "strtoll",
        lean: "AchatesCheck.Models.strtoll",
        sig: "Ptr → Ptr → I32 → M I64",
        what: "glibc's __isoc23_strtoll, which the compiled C calls for strtoll: C23 strtoll with the 0b prefix; errno is not modelled",
    },
];

/// The lines of one function's definition.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Region {
    function: String,
    file: PathBuf,
    first_line: usize,
    lines: usize,
}

/// What is known about a function before anything runs.
struct Target<'a> {
    row: &'a Row,
    module: String,
    plan: Plan,
    models: Vec<&'static ExtModel>,
    /// The file the function's text is in and the unit's main file.
    def_file: PathBuf,
    main_file: PathBuf,
    /// The function's own text first, then that of the functions it calls
    /// that are defined in the same files: where bugs are planted.
    regions: Vec<Region>,
    dict: Dictionary,
    cflags: Vec<String>,
    cwd: PathBuf,
}

struct Ran {
    stdout: String,
    stderr: String,
    /// `None` when the process was killed for running too long.
    code: Option<i32>,
    signal: Option<i32>,
    timed_out: bool,
}

/// Sends SIGKILL to every process in the group `id` leads.
fn kill_group(id: u32) {
    let _ = Command::new("kill")
        .args(["-KILL", "--", &format!("-{id}")])
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status();
}

/// Runs a command with its output in files, so that a process that fills a
/// pipe cannot block. It is killed when it runs longer than `limit`, or
/// when its output does not grow for `idle`.
fn run_limited(
    cmd: &mut Command,
    scratch: &Path,
    limit: Duration,
    idle: Option<Duration>,
) -> Result<Ran> {
    use std::os::unix::process::{CommandExt as _, ExitStatusExt as _};
    let (out_path, err_path) = (
        scratch.with_extension("stdout"),
        scratch.with_extension("stderr"),
    );
    let out =
        File::create(&out_path).with_context(|| format!("creating {}", out_path.display()))?;
    let err =
        File::create(&err_path).with_context(|| format!("creating {}", err_path.display()))?;
    let mut child = cmd
        .stdin(Stdio::null())
        .stdout(Stdio::from(out))
        .stderr(Stdio::from(err))
        // Its own process group, so that a child it forked (the harness
        // runs a call expected to abort in one) dies with it.
        .process_group(0)
        .spawn()
        .with_context(|| format!("starting {}", cmd.get_program().display()))?;
    let start = Instant::now();
    let (mut grew, mut size) = (start, 0);
    let mut timed_out = false;
    let status = loop {
        if let Some(s) = child.try_wait()? {
            break s;
        }
        let now = std::fs::metadata(&out_path).map_or(0, |m| m.len());
        if now != size {
            (grew, size) = (Instant::now(), now);
        }
        if start.elapsed() > limit || idle.is_some_and(|d| grew.elapsed() > d) {
            timed_out = true;
            kill_group(child.id());
            break child.wait()?;
        }
        std::thread::sleep(Duration::from_millis(2));
    };
    // Whatever the leader left behind in its group goes too.
    kill_group(child.id());
    Ok(Ran {
        stdout: std::fs::read_to_string(&out_path).unwrap_or_default(),
        stderr: String::from_utf8_lossy(&std::fs::read(&err_path).unwrap_or_default()).into_owned(),
        code: status.code(),
        signal: status.signal(),
        timed_out,
    })
}

fn put(path: &Path, text: &str) -> Result<()> {
    if let Some(dir) = path.parent() {
        std::fs::create_dir_all(dir).with_context(|| format!("creating {}", dir.display()))?;
    }
    std::fs::write(path, text).with_context(|| format!("writing {}", path.display()))
}

fn rsp(path: &Path) -> Result<Vec<String>> {
    Ok(std::fs::read_to_string(path)
        .with_context(|| format!("reading {}", path.display()))?
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .map(str::to_owned)
        .collect())
}

/// The arguments the unit was compiled with, without the parts that name
/// its input and outputs.
fn own_cflags(e: &Entry) -> Vec<String> {
    let mut out = Vec::new();
    let mut skip = false;
    for a in e.argv.iter().skip(1) {
        if skip {
            skip = false;
        } else if matches!(a.as_str(), "-o" | "-MF" | "-MQ" | "-MT") {
            skip = true;
        } else if !(matches!(a.as_str(), "-c" | "-MD" | "-MMD" | "-MP") || *a == e.file) {
            out.push(a.clone());
        }
    }
    out
}

/// Constants in the function and in what it calls, for the generator.
fn dictionary(a: &Analysis, key: &str) -> Dictionary {
    let mut d = Dictionary::default();
    let mut todo = vec![key.to_owned()];
    let mut seen = BTreeSet::new();
    while let Some(k) = todo.pop() {
        if !seen.insert(k.clone()) || seen.len() > 40 {
            continue;
        }
        let Some((f, _, _)) = a.function(&k) else {
            continue;
        };
        for_each_expr(&f.body, &mut |e| match &e.kind {
            ExprKind::StringLit(b) if !b.is_empty() && b.len() <= 24 => d.strings.push(b.clone()),
            ExprKind::IntLit(v) => d.ints.push(i128::try_from(*v).unwrap_or(0)),
            ExprKind::CharLit(v) => {
                d.ints.push(i128::from(*v));
                if let Ok(b) = u8::try_from(*v & 0xff) {
                    d.strings.push(vec![b]);
                }
            }
            ExprKind::EnumConst { value, .. } => d.ints.push(*value),
            ExprKind::Call {
                direct: Some(name), ..
            } => {
                if let Some(c) = a.resolve(&k, name) {
                    todo.push(c);
                }
            }
            _ => {}
        });
    }
    d.strings.sort();
    d.strings.dedup();
    d.ints.sort_unstable();
    d.ints.dedup();
    d
}

/// Where to plant bugs for `row`: its own definition, then the
/// definitions of its direct callees in the files the harness compiles.
/// A callee elsewhere is linked from the library, and a changed copy of its
/// file would define its neighbours twice.
fn regions(a: &Analysis, row: &Row, def_file: &Path, main_file: &Path) -> Vec<Region> {
    let region = |key: &str| -> Option<Region> {
        let (f, _, _) = a.function(key)?;
        let r = a.rows.iter().find(|r| r.key == key)?;
        Some(Region {
            function: r.name.clone(),
            file: PathBuf::from(&f.def_file),
            first_line: usize::try_from(r.line).ok()?,
            lines: usize::try_from(f.lines).ok()?,
        })
    };
    let mut out: Vec<Region> = region(&row.key).into_iter().collect();
    let Some((f, _, _)) = a.function(&row.key) else {
        return out;
    };
    let mut callees = BTreeSet::new();
    for_each_expr(&f.body, &mut |e| {
        if let ExprKind::Call {
            direct: Some(name), ..
        } = &e.kind
            && let Some(k) = a.resolve(&row.key, name)
        {
            callees.insert(k);
        }
    });
    for k in callees {
        if let Some(r) = region(&k)
            && (r.file == def_file || r.file == main_file)
            && !out.contains(&r)
        {
            out.push(r);
        }
    }
    out
}

fn module_name(index: usize, name: &str) -> String {
    let safe: String = name
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    format!("F{index}_{safe}")
}

fn first_error(text: &str) -> String {
    text.lines()
        .find(|l| l.contains("error"))
        .or_else(|| text.lines().find(|l| !l.trim().is_empty()))
        .unwrap_or("no diagnostic")
        .trim()
        .chars()
        .take(300)
        .collect()
}

/// Most address space a Lean driver or a C harness may use, in KiB: an
/// input that makes either hold more is reported as a crash of that input
/// instead of taking the machine's memory from the other jobs.
const MEMORY_KIB: u64 = 4 << 20;

/// One of the two programs that run a function on input lines.
struct Runner<'a> {
    /// `c` or `lean`: names its files and its crashes.
    tag: &'static str,
    prog: &'a Path,
    /// Arguments before the input file.
    args: &'a [&'a str],
    /// The longest single call, in milliseconds, of the runs that reported
    /// it (the C harness does when it finishes).
    slowest: std::cell::Cell<u64>,
}

impl Runner<'_> {
    /// Runs the program over the lines of `input` and returns its line per
    /// index. An input on which it crashes, or prints nothing for `idle`,
    /// is recorded as a crash, and the run continues after it unless
    /// `stop_at_crash`.
    fn run(
        &self,
        dir: &Path,
        input: &[(usize, String)],
        limit: Duration,
        idle: Duration,
        stop_at_crash: bool,
    ) -> Result<BTreeMap<usize, String>> {
        let mut results = BTreeMap::new();
        let mut rest: &[(usize, String)] = input;
        while !rest.is_empty() {
            let path = dir.join(format!("{}.in", self.tag));
            let mut text = String::new();
            for (i, l) in rest {
                let _ = writeln!(text, "{i} {l}");
            }
            put(&path, &text)?;
            let mut cmd = Command::new("/bin/sh");
            cmd.arg("-c")
                // The CPU limit holds in every process the program forks,
                // whatever happens to this one.
                .arg(format!(
                    "ulimit -v {MEMORY_KIB} && ulimit -t {} && exec \"$0\" \"$@\"",
                    limit.as_secs() + 1
                ))
                .arg(self.prog)
                .args(self.args)
                .arg(&path);
            let ran = run_limited(&mut cmd, &dir.join(self.tag), limit, Some(idle))?;
            for l in ran.stderr.lines() {
                if let Some(ms) = l.strip_prefix("ck_max_ms=").and_then(|v| v.parse().ok()) {
                    self.slowest.set(self.slowest.get().max(ms));
                }
            }
            let mut done = 0;
            for l in ran.stdout.lines() {
                let Some((i, r)) = l.split_once(' ') else {
                    continue;
                };
                if let (Ok(i), Some((want, _))) = (i.parse::<usize>(), rest.get(done))
                    && i == *want
                {
                    results.insert(i, r.to_owned());
                    done += 1;
                }
            }
            if ran.code == Some(0) && !ran.timed_out {
                break;
            }
            // SIGALRM is the harness's own limit per call, SIGXCPU the CPU
            // limit set above.
            let timeout = ran.timed_out || matches!(ran.signal, Some(14 | 24));
            let how = if ran.timed_out {
                format!(
                    "printed nothing for {} s or ran past {} s",
                    idle.as_secs(),
                    limit.as_secs()
                )
            } else if let Some(s) = ran.signal {
                format!("was killed by signal {s}")
            } else {
                format!(
                    "exited with status {}: {}",
                    ran.code.unwrap_or(-1),
                    first_error(&ran.stderr)
                )
            };
            // The line of the input being run was cut off or never begun.
            if let Some((i, _)) = rest.get(done) {
                let kind = if timeout { "timeout" } else { "crash" };
                results.insert(*i, format!("{kind}: the {} program {how}", self.tag));
            }
            if stop_at_crash {
                break;
            }
            rest = rest.get(done + 1..).unwrap_or(&[]);
        }
        Ok(results)
    }
}

/// How long a program may print nothing before the input it is on counts
/// as a crash. The C harness ends a call itself after `CK_SECONDS`.
const IDLE: Duration = Duration::from_secs(30);

fn c_runner(bin: &Path) -> Runner<'_> {
    Runner {
        tag: "c",
        prog: bin,
        args: &[],
        slowest: std::cell::Cell::new(0),
    }
}

struct Ctx<'a> {
    opts: &'a Options,
    link: Vec<String>,
    driver: PathBuf,
    cc: &'static Path,
}

impl Ctx<'_> {
    fn run_dir(&self, t: &Target<'_>) -> PathBuf {
        self.opts.work.join("run").join(&t.module)
    }

    /// Compiles a harness that takes the function's text from `text_file`.
    /// Compiles a harness, with the file `replace.0` swapped for the copy
    /// `replace.1`; with `preprocess`, only runs the preprocessor and
    /// returns the path of its output.
    fn compile(
        &self,
        t: &Target<'_>,
        dir: &Path,
        replace: Option<(&Path, &Path)>,
        preprocess: bool,
    ) -> Result<Result<PathBuf, String>> {
        let mut includes = vec![t.def_file.as_path()];
        if t.def_file != t.main_file {
            includes.push(&t.main_file);
        }
        let includes: Vec<String> = includes
            .into_iter()
            .map(|f| match replace {
                Some((original, copy)) if original == f => copy.display().to_string(),
                _ => f.display().to_string(),
            })
            .collect();
        let src = dir.join("harness.c");
        put(&src, &harness::c_harness(&includes, &t.row.name, &t.plan))?;
        let bin = dir.join(if preprocess { "harness.i" } else { "harness" });
        let mut cmd = Command::new(self.cc);
        cmd.args(&t.cflags);
        // Debug information does not change the code and costs most of the
        // compile time; files next to the original are found by `-iquote`
        // when the text is a changed copy somewhere else.
        cmd.arg("-g0").arg("-w");
        for f in [&t.def_file, &t.main_file] {
            if let Some(d) = f.parent() {
                cmd.arg("-iquote").arg(d);
            }
        }
        cmd.arg(&src).arg("-o").arg(&bin);
        if preprocess {
            cmd.arg("-E").arg("-P");
        } else {
            cmd.args(&self.link);
        }
        cmd.current_dir(&t.cwd);
        let ran = run_limited(&mut cmd, &dir.join("cc"), Duration::from_mins(5), None)?;
        Ok(if ran.code == Some(0) {
            Ok(bin)
        } else {
            Err(first_error(&ran.stderr))
        })
    }

    /// Runs the Lean definition on every case and returns its line per
    /// case; a case the driver crashed or stalled on has a `crash:` line.
    fn run_lean(&self, t: &Target<'_>, dir: &Path, cases: &[String]) -> Result<Vec<String>> {
        let input: Vec<(usize, String)> = cases.iter().cloned().enumerate().collect();
        let lean = Runner {
            tag: "lean",
            prog: &self.driver,
            args: &[t.module.as_str()],
            slowest: std::cell::Cell::new(0),
        };
        let mut by_index = lean.run(dir, &input, Duration::from_hours(1), IDLE, false)?;
        Ok((0..cases.len())
            .map(|i| {
                by_index
                    .remove(&i)
                    .unwrap_or_else(|| "harness no result".to_owned())
            })
            .collect())
    }

    /// Checks the targets on `jobs` threads; the results in no fixed order.
    fn check_all(&self, targets: &[Target<'_>]) -> Vec<(String, Result<FnResult>)> {
        let next = AtomicUsize::new(0);
        let done: Mutex<Vec<(String, Result<FnResult>)>> = Mutex::new(Vec::new());
        std::thread::scope(|s| {
            for _ in 0..self.opts.jobs.max(1) {
                s.spawn(|| {
                    while let Some(t) = targets.get(next.fetch_add(1, Ordering::Relaxed)) {
                        let began = Instant::now();
                        let mut r = self.check_one(t);
                        if let Ok(r) = &mut r {
                            r.seconds = began.elapsed().as_secs_f64();
                        }
                        if let Ok(mut d) = done.lock() {
                            d.push((t.row.key.clone(), r));
                        }
                    }
                });
            }
        });
        // `scope` re-raises the panic of any thread, so a poisoned lock is
        // never seen here.
        done.into_inner()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    fn check_one(&self, t: &Target<'_>) -> Result<FnResult> {
        let mut res = FnResult::new(t.row, &self.opts.name);
        res.models = t.models.iter().map(|m| m.name.to_owned()).collect();
        let dir = self.run_dir(t);
        std::fs::create_dir_all(&dir).with_context(|| format!("creating {}", dir.display()))?;
        let mut generator = Gen::new(self.opts.seed, &t.row.key, &t.dict);
        let cases: Vec<String> = (0..self.opts.count)
            .map(|_| generator.case(&t.plan.params))
            .collect();
        let lean = self.run_lean(t, &dir, &cases)?;
        res.inputs = cases.len();
        let mut bad: BTreeMap<usize, String> = BTreeMap::new();
        let mut c_input = Vec::new();
        for (i, (case, l)) in cases.iter().zip(&lean).enumerate() {
            match compare::class(l) {
                Class::Ok => c_input.push((i, format!("R {case}"))),
                Class::Aborts => c_input.push((i, format!("A {case}"))),
                Class::Undefined => res.undefined += 1,
                Class::Unsupported => res.unsupported += 1,
                // Running out of fuel is a failure of the check, not an
                // input outside the contract: every case must finish.
                Class::OutOfFuel | Class::Broken => {
                    bad.insert(i, "not run".to_owned());
                }
            }
        }
        if !c_input.is_empty() {
            let bin = match self.compile(t, &dir, None, false)? {
                Ok(b) => b,
                Err(e) => {
                    res.status = Status::NotCheckable;
                    res.reasons = vec![format!("the generated C harness does not compile: {e}")];
                    return Ok(res);
                }
            };
            let started = Instant::now();
            let runner = c_runner(&bin);
            let c = runner.run(&dir, &c_input, Duration::from_hours(1), IDLE, false)?;
            let took = started.elapsed();
            let slowest = Duration::from_millis(runner.slowest.get());
            for (i, _) in &c_input {
                let l = lean.get(*i).map_or("", String::as_str);
                let r = c.get(i).map_or("no result", String::as_str);
                if !compare::agree(l, r) {
                    bad.insert(*i, r.to_owned());
                } else if compare::class(l) == Class::Ok {
                    res.compared += 1;
                } else {
                    res.aborts += 1;
                }
            }
            if bad.is_empty() && self.opts.mutants > 0 {
                // A planted bug may loop for ever; give each mutant a few
                // times what the original needed.
                let limit = took * 10 + Duration::from_secs(5);
                res.mutants = Some(self.mutants(t, &dir, &c_input, &lean, limit, slowest)?);
            }
        }
        res.disagreements = bad.len();
        res.first = bad
            .into_iter()
            .next()
            .map(|(index, c)| report::Disagreement {
                index,
                input: cases.get(index).cloned().unwrap_or_default(),
                lean: lean.get(index).cloned().unwrap_or_default(),
                c,
            });
        res.status = if res.disagreements > 0 {
            Status::Disagrees
        } else if res.compared + res.aborts == 0 {
            res.reasons = vec![format!(
                "no generated input has a defined result in the model ({} undefined, {} unsupported of {})",
                res.undefined, res.unsupported, res.inputs
            )];
            Status::NotCheckable
        } else if res.mutants.as_ref().is_some_and(|m| m.caught > 0) {
            Status::CheckedSensitive
        } else {
            Status::CheckedNotShownSensitive
        };
        Ok(res)
    }

    /// `Some(argument)` when the mutated copy preprocesses to the same text
    /// as the original, with the copy's path read as the original's.
    fn unchanged_after_preprocessing(
        &self,
        t: &Target<'_>,
        dir: &Path,
        mdir: &Path,
        original: &Path,
        copy: &Path,
    ) -> Result<Option<String>> {
        let base = dir.join("harness.i");
        if !base.exists() && self.compile(t, dir, None, true)?.is_err() {
            return Ok(None);
        }
        let Ok(mine) = self.compile(t, mdir, Some((original, copy)), true)? else {
            return Ok(None);
        };
        let a = std::fs::read_to_string(&base).unwrap_or_default();
        let b = std::fs::read_to_string(&mine)
            .unwrap_or_default()
            .replace(&copy.display().to_string(), &original.display().to_string());
        Ok((!a.is_empty() && a == b).then(|| {
            "the preprocessed text is unchanged: the change is in a branch of `#if` this build does not compile".to_owned()
        }))
    }

    fn mutants(
        &self,
        t: &Target<'_>,
        dir: &Path,
        c_input: &[(usize, String)],
        lean: &[String],
        limit: Duration,
        slowest: Duration,
    ) -> Result<report::Mutants> {
        // A mutant that only times out is caught when the original's
        // slowest call needed well under the limit per call.
        let timeouts_count = slowest * 4 < Duration::from_secs(harness::CK_SECONDS);
        let mut out = report::Mutants::default();
        let mut list = Vec::new();
        for r in &t.regions {
            // The callees only fill up what the function's own text leaves
            // of the cap.
            let room = self.opts.mutants.saturating_sub(list.len());
            if room == 0 {
                break;
            }
            let src = std::fs::read_to_string(&r.file)
                .with_context(|| format!("reading {}", r.file.display()))?;
            let (candidates, ms) =
                mutate::mutants(&src, r.first_line, r.lines, room, self.opts.seed);
            out.candidates += candidates;
            list.extend(ms.into_iter().map(|m| (r, m)));
        }
        out.generated = list.len();
        for (k, (r, m)) in list.iter().enumerate() {
            let mdir = dir.join(format!("m{k}"));
            let base = r
                .file
                .file_name()
                .map_or_else(|| "source.c".into(), |n| n.to_string_lossy().into_owned());
            let copy = mdir.join(&base);
            put(&copy, &m.source)?;
            // A change the preprocessor drops (in an `#if` branch this build
            // does not take) cannot change behaviour: set aside, with that
            // as the argument, instead of being run.
            if let Some(same) = self.unchanged_after_preprocessing(t, dir, &mdir, &r.file, &copy)? {
                out.equivalent.push(report::Survivor {
                    function: r.function.clone(),
                    file: r.file.display().to_string(),
                    line: m.line,
                    column: m.column,
                    operator: m.operator.to_owned(),
                    before: m.before.clone(),
                    after: m.after.clone(),
                    note: Some(same),
                });
                let _ = std::fs::remove_dir_all(&mdir);
                continue;
            }
            let Ok(bin) = self.compile(t, &mdir, Some((&r.file, &copy)), false)? else {
                let _ = std::fs::remove_dir_all(&mdir);
                continue;
            };
            out.compiled += 1;
            let c = c_runner(&bin).run(&mdir, c_input, limit, IDLE, true)?;
            let differ: Vec<&str> = c_input
                .iter()
                .map(|(i, _)| {
                    (
                        lean.get(*i).map_or("", String::as_str),
                        c.get(i).map_or("no result", String::as_str),
                    )
                })
                .filter(|(l, r)| !compare::agree(l, r))
                .map(|(_, r)| r)
                .collect();
            let by_value = differ.iter().any(|r| !compare::is_timeout(r));
            let note = if by_value || differ.is_empty() {
                None
            } else if timeouts_count {
                out.caught_by_timeout += 1;
                None
            } else {
                out.timeouts_not_counted += 1;
                Some(format!(
                    "timed out, but the original's slowest call took {} ms",
                    slowest.as_millis()
                ))
            };
            if by_value || (!differ.is_empty() && note.is_none()) {
                out.caught += 1;
            } else {
                out.survivors.push(report::Survivor {
                    function: r.function.clone(),
                    file: r.file.display().to_string(),
                    line: m.line,
                    column: m.column,
                    operator: m.operator.to_owned(),
                    before: m.before.clone(),
                    after: m.after.clone(),
                    note,
                });
            }
            let _ = std::fs::remove_dir_all(&mdir);
        }
        Ok(out)
    }
}

fn lake(dir: &Path, args: &[&str]) -> Result<Ran> {
    let mut cmd = Command::new("lake");
    cmd.args(args)
        .current_dir(dir)
        .env("PATH", tools::path_with_lean());
    run_limited(
        &mut cmd,
        &dir.join("lake-run"),
        Duration::from_hours(1),
        None,
    )
}

/// Writes the driver project for `targets` and builds it. A function whose
/// module does not compile is taken out and reported, and the rest is
/// built again.
fn build_driver(
    opts: &Options,
    targets: &mut Vec<Target<'_>>,
    failed: &mut Vec<(String, String)>,
) -> Result<PathBuf> {
    let dir = opts.work.join("driver");
    let root = &opts.name;
    let check = dir.join("Check");
    if check.exists() {
        std::fs::remove_dir_all(&check).with_context(|| format!("clearing {}", check.display()))?;
    }
    let rel = |to: &Path| -> Result<String> {
        Ok(std::fs::canonicalize(to)
            .with_context(|| format!("resolving {}", to.display()))?
            .display()
            .to_string())
    };
    put(
        &dir.join("lakefile.toml"),
        &format!(
            "name = \"check\"\ndefaultTargets = [\"check\"]\n\n[[require]]\nname = \"achates\"\npath = \"{}\"\n\n[[require]]\nname = \"{}\"\npath = \"{}\"\n\n[[lean_lib]]\nname = \"Check\"\nleanOptions = {{ autoImplicit = false, relaxedAutoImplicit = false }}\n\n[[lean_exe]]\nname = \"check\"\nroot = \"Main\"\n",
            rel(&opts.runtime)?,
            root.to_lowercase(),
            rel(&opts.work.join("emitted"))?,
        ),
    )?;
    put(&dir.join("lean-toolchain"), "leanprover/lean4:v4.36.0\n")?;
    let mut inst = format!(
        "import {root}\nimport AchatesCheck\n\n/-! The models `achates check` supplies for functions the emitted code\ntakes as parameters. Written by `achates check`; do not edit. -/\n\nopen Achates\n\n"
    );
    let used: BTreeSet<&str> = targets
        .iter()
        .flat_map(|t| t.models.iter().map(|m| m.name))
        .collect();
    for m in EXT_MODELS.iter().filter(|m| used.contains(m.name)) {
        let _ = writeln!(
            inst,
            "instance : {root}.{} := ⟨{}⟩",
            ext_class(m.name),
            m.lean
        );
    }
    put(&check.join("Instances.lean"), &inst)?;
    for t in targets.iter() {
        let lean_name = format!("{root}.{}.{}", t.row.module, names::ident(&t.row.name));
        put(
            &check.join(format!("{}.lean", t.module)),
            &harness::lean_module(root, &t.module, &lean_name, &t.plan, true),
        )?;
    }
    loop {
        let modules: Vec<String> = targets.iter().map(|t| t.module.clone()).collect();
        put(&dir.join("Main.lean"), &harness::lean_main(root, &modules))?;
        let ran = lake(&dir, &["build", "check"])?;
        if ran.code == Some(0) {
            return Ok(dir.join(".lake/build/bin/check"));
        }
        let log = format!("{}\n{}", ran.stdout, ran.stderr);
        let broken: Vec<usize> = targets
            .iter()
            .enumerate()
            .filter(|(_, t)| {
                log.contains(&format!("Check/{}.lean:", t.module))
                    || log.contains(&format!("Check.{} ", t.module))
                        && log.lines().any(|l| {
                            l.starts_with('✖') && l.contains(&format!("Check.{}", t.module))
                        })
            })
            .map(|(i, _)| i)
            .collect();
        if broken.is_empty() {
            bail!(
                "the check driver does not build, and no generated module is to blame:\n{}",
                log.lines()
                    .rev()
                    .take(40)
                    .collect::<Vec<_>>()
                    .into_iter()
                    .rev()
                    .collect::<Vec<_>>()
                    .join("\n")
            );
        }
        for i in broken.into_iter().rev() {
            let t = targets.remove(i);
            let marker = format!("Check/{}.lean:", t.module);
            let why = log
                .lines()
                .find(|l| l.contains(&marker) && l.contains("error"))
                .map_or_else(
                    || first_error(&log),
                    |l| l.trim().chars().take(300).collect(),
                );
            let _ = std::fs::remove_file(check.join(format!("{}.lean", t.module)));
            failed.push((t.row.key.clone(), why));
        }
    }
}

/// Decides for every wanted function whether it can be checked: a target
/// for each that can, and a result with the reason for each that cannot.
fn plan_all<'a>(
    entries: &[&Entry],
    opts: &Options,
    a: &'a Analysis,
    results: &mut BTreeMap<String, FnResult>,
) -> Result<Vec<Target<'a>>> {
    let shapes = Shapes::new(a);
    let wanted = |r: &Row| opts.functions.is_empty() || opts.functions.contains(&r.name);
    let override_flags = opts.cflags_file.as_deref().map(rsp).transpose()?;
    let mut targets = Vec::new();
    for (index, row) in a.rows.iter().enumerate().filter(|(_, r)| wanted(r)) {
        let mut res = FnResult::new(row, &opts.name);
        if !emitted(row) {
            res.status = Status::NotEmitted;
            res.reasons.clone_from(&row.res.reasons);
            results.insert(row.key.clone(), res);
            continue;
        }
        let mut reasons = Vec::new();
        let mut models = Vec::new();
        for e in &row.res.exts {
            let arrow = a.world.exts.get(e).and_then(|x| x.as_ref().ok());
            match EXT_MODELS
                .iter()
                .find(|m| m.name == e && Some(m.sig) == arrow.map(String::as_str))
            {
                Some(m) => models.push(m),
                None => reasons.push(format!("needs external {e}")),
            }
        }
        let plan = match shapes.plan(&row.key) {
            Ok(p) => Some(p),
            Err(e) => {
                reasons.extend(e);
                None
            }
        };
        let unit = a.unit_of(&row.key).and_then(|i| entries.get(i));
        let ir = a.function(&row.key);
        let (Some(plan), true, Some(unit), Some((f, _, _))) = (plan, reasons.is_empty(), unit, ir)
        else {
            res.status = Status::NotCheckable;
            res.reasons = reasons;
            results.insert(row.key.clone(), res);
            continue;
        };
        targets.push(Target {
            row,
            module: module_name(index, &row.name),
            plan,
            models,
            def_file: PathBuf::from(&f.def_file),
            main_file: unit.path.clone(),
            regions: regions(a, row, &PathBuf::from(&f.def_file), &unit.path),
            dict: dictionary(a, &row.key),
            cflags: override_flags.clone().unwrap_or_else(|| own_cflags(unit)),
            cwd: unit.directory.clone(),
        });
    }
    Ok(targets)
}

/// A change made to the emitted project before it is built.
pub(crate) type Tamper = dyn Fn(&Path) -> Result<()>;

/// Runs the check. `tamper` is called on the emitted project before it is
/// built; the tests use it to plant a wrong definition.
pub(crate) fn run(entries: &[&Entry], opts: &Options, tamper: Option<&Tamper>) -> Result<Report> {
    let started = Instant::now();
    // The harnesses are compiled in each unit's own directory, so every
    // path the check writes must not depend on the current one.
    let opts = &Options {
        work: std::path::absolute(&opts.work)
            .with_context(|| format!("resolving {}", opts.work.display()))?,
        runtime: std::path::absolute(&opts.runtime)
            .with_context(|| format!("resolving {}", opts.runtime.display()))?,
        ..opts.clone()
    };
    let a = emit::analyse(entries)?;
    let emitted_dir = opts.work.join("emitted");
    emit::project::write(
        &emit::Options {
            out: emitted_dir.clone(),
            name: opts.name.clone(),
            runtime: opts.runtime.clone(),
        },
        &a.world,
        &a.rows,
    )?;
    if let Some(f) = tamper {
        f(&emitted_dir)?;
    }
    let mut results: BTreeMap<String, FnResult> = BTreeMap::new();
    let mut targets = plan_all(entries, opts, &a, &mut results)?;
    let mut build_seconds = 0.0;
    if !targets.is_empty() {
        let mut failed = Vec::new();
        let build_started = Instant::now();
        let driver = build_driver(opts, &mut targets, &mut failed)?;
        build_seconds = build_started.elapsed().as_secs_f64();
        for (key, why) in failed {
            if let Some(row) = a.rows.iter().find(|r| r.key == key) {
                let mut res = FnResult::new(row, &opts.name);
                res.status = Status::NotCheckable;
                res.reasons = vec![format!("the generated Lean driver does not compile: {why}")];
                results.insert(key, res);
            }
        }
        let ctx = Ctx {
            opts,
            link: opts
                .link_file
                .as_deref()
                .map(rsp)
                .transpose()?
                .unwrap_or_default(),
            driver,
            cc: tools::cc()?,
        };
        for (key, r) in ctx.check_all(&targets) {
            results.insert(key, r?);
        }
    }
    let functions = a
        .rows
        .iter()
        .filter_map(|r| results.remove(&r.key))
        .collect();
    Ok(Report {
        seed: opts.seed,
        count: opts.count,
        mutant_cap: opts.mutants,
        models: EXT_MODELS
            .iter()
            .map(|m| (m.name.to_owned(), m.what.to_owned()))
            .collect(),
        functions,
        build_seconds,
        seconds: started.elapsed().as_secs_f64(),
    })
}

/// Whether a function is one the selection named, not a header function it reaches.
pub(crate) fn selected(origin: Origin) -> bool {
    origin == Origin::MainFile
}

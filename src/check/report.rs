//! The result of a check: one record per function, as JSON for programs
//! and as a summary for people.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::check::selected;
use crate::emit::project::emitted;
use crate::emit::{Row, names};
use crate::ir::Origin;

#[derive(serde::Serialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Status {
    /// The model and the compiled C agreed on every input compared, and
    /// the comparison caught at least one planted bug.
    #[serde(rename = "checked-and-sensitive")]
    CheckedSensitive,
    /// They agreed, but no planted bug was caught: the agreement is not
    /// shown to depend on what the function does.
    #[serde(rename = "checked-not-shown-sensitive")]
    CheckedNotShownSensitive,
    #[serde(rename = "disagrees")]
    Disagrees,
    #[serde(rename = "not-checkable")]
    NotCheckable,
    #[serde(rename = "not-emitted")]
    NotEmitted,
}

impl Status {
    pub(crate) const ALL: [Self; 5] = [
        Self::CheckedSensitive,
        Self::CheckedNotShownSensitive,
        Self::Disagrees,
        Self::NotCheckable,
        Self::NotEmitted,
    ];

    pub(crate) const fn label(self) -> &'static str {
        match self {
            Self::CheckedSensitive => "checked and sensitive",
            Self::CheckedNotShownSensitive => "checked, agreement not shown to be sensitive",
            Self::Disagrees => "disagrees",
            Self::NotCheckable => "not checkable",
            Self::NotEmitted => "not emitted",
        }
    }
}

#[derive(serde::Serialize, Debug, Clone)]
pub(crate) struct Disagreement {
    /// Position of the input in the generated sequence.
    pub(crate) index: usize,
    /// The input's tokens, as both programs read them.
    pub(crate) input: String,
    pub(crate) lean: String,
    pub(crate) c: String,
}

#[derive(serde::Serialize, Debug, Clone)]
pub(crate) struct Survivor {
    /// The function whose text was changed: the one checked or a callee.
    pub(crate) function: String,
    pub(crate) file: String,
    pub(crate) line: usize,
    pub(crate) column: usize,
    pub(crate) operator: String,
    pub(crate) before: String,
    pub(crate) after: String,
    /// Why a mutant that made the C differ is still listed here.
    pub(crate) note: Option<String>,
}

#[derive(serde::Serialize, Debug, Clone, Default)]
pub(crate) struct Mutants {
    /// Every change the operators could make to the function.
    pub(crate) candidates: usize,
    /// How many of them were tried.
    pub(crate) generated: usize,
    pub(crate) compiled: usize,
    pub(crate) caught: usize,
    /// Of `caught`, those whose only difference was running past the time
    /// limit of a call.
    pub(crate) caught_by_timeout: usize,
    /// Mutants that only timed out where the original's slowest call was
    /// too close to the limit for that to count; they are survivors.
    pub(crate) timeouts_not_counted: usize,
    pub(crate) survivors: Vec<Survivor>,
    /// Mutants set aside as equivalent, each with the argument; neither
    /// run nor counted as compiled, caught or surviving.
    pub(crate) equivalent: Vec<Survivor>,
}

#[derive(serde::Serialize, Debug, Clone)]
pub(crate) struct FnResult {
    pub(crate) function: String,
    pub(crate) file: String,
    pub(crate) line: u64,
    pub(crate) origin: Origin,
    pub(crate) lean: Option<String>,
    pub(crate) status: Status,
    pub(crate) reasons: Vec<String>,
    /// Inputs generated and run through the Lean definition.
    pub(crate) inputs: usize,
    /// Inputs with a result in the model that the compiled C agreed with.
    pub(crate) compared: usize,
    /// Inputs on which the model stops at a failed assertion or an abort
    /// and the compiled C died from `abort` as well.
    pub(crate) aborts: usize,
    /// Inputs the model gives no meaning (undefined behaviour); not run in C.
    pub(crate) undefined: usize,
    /// Inputs that reach something the model does not cover; not run in C.
    pub(crate) unsupported: usize,
    pub(crate) disagreements: usize,
    /// The first disagreement, in input order.
    pub(crate) first: Option<Disagreement>,
    /// External functions the check supplied a model for.
    pub(crate) models: Vec<String>,
    pub(crate) mutants: Option<Mutants>,
    /// Wall time; not written to the JSON, which stays the same from run to run.
    #[serde(skip)]
    pub(crate) seconds: f64,
}

impl FnResult {
    pub(crate) fn new(row: &Row, root: &str) -> Self {
        Self {
            function: row.name.clone(),
            file: row.file.clone(),
            line: row.line,
            origin: row.origin,
            lean: emitted(row)
                .then(|| format!("{root}.{}.{}", row.module, names::ident(&row.name))),
            status: Status::NotCheckable,
            reasons: Vec::new(),
            inputs: 0,
            compared: 0,
            aborts: 0,
            undefined: 0,
            unsupported: 0,
            disagreements: 0,
            first: None,
            models: Vec::new(),
            mutants: None,
            seconds: 0.0,
        }
    }

    /// Inputs the model puts outside the function's contract: undefined
    /// behaviour, a failed assertion, or an abort.
    pub(crate) const fn out_of_contract(&self) -> usize {
        self.undefined + self.aborts
    }
}

#[derive(serde::Serialize, Debug)]
pub(crate) struct Report {
    pub(crate) seed: u64,
    /// Inputs generated per function.
    pub(crate) count: usize,
    /// Most mutants tried per function.
    pub(crate) mutant_cap: usize,
    /// External functions the check has a model for, and what each models.
    pub(crate) models: BTreeMap<String, String>,
    pub(crate) functions: Vec<FnResult>,
    #[serde(skip)]
    pub(crate) build_seconds: f64,
    #[serde(skip)]
    pub(crate) seconds: f64,
}

fn percent(part: usize, whole: usize) -> String {
    (part * 1000)
        .checked_div(whole)
        .map_or_else(|| "-".to_owned(), |p| format!("{}%", p.div_ceil(10)))
}

/// The lines of the summary about one function.
fn line(o: &mut String, f: &FnResult) {
    let _ = write!(
        o,
        "{}:{} {}: {}",
        f.file,
        f.line,
        f.function,
        f.status.label()
    );
    match f.status {
        Status::NotCheckable | Status::NotEmitted => {
            let _ = write!(o, ": {}", f.reasons.join("; "));
        }
        _ => {
            let _ = write!(
                o,
                "; {} inputs, {} compared, {} aborts confirmed, {} undefined, {} unsupported, out of contract {}",
                f.inputs,
                f.compared,
                f.aborts,
                f.undefined,
                f.unsupported,
                percent(f.out_of_contract(), f.inputs)
            );
            if let Some(m) = &f.mutants {
                let _ = write!(
                    o,
                    "; mutants caught {} of {} generated ({} by timeout; {} equivalent; {} compiled, {} candidates)",
                    m.caught,
                    m.generated,
                    m.caught_by_timeout,
                    m.equivalent.len(),
                    m.compiled,
                    m.candidates
                );
            }
        }
    }
    o.push('\n');
    if let Some(d) = &f.first {
        let _ = writeln!(
            o,
            "  {} disagreement(s); first at input {}:\n    input: {}\n    lean:  {}\n    c:     {}",
            f.disagreements, d.index, d.input, d.lean, d.c
        );
    }
    for s in f.mutants.iter().flat_map(|m| &m.survivors) {
        let _ = writeln!(
            o,
            "  survivor {}:{}:{} (in {}) {}: `{}` -> `{}`{}",
            s.file,
            s.line,
            s.column,
            s.function,
            s.operator,
            s.before,
            s.after,
            s.note
                .as_ref()
                .map(|n| format!(" ({n})"))
                .unwrap_or_default()
        );
    }
}

impl Report {
    pub(crate) fn json(&self) -> anyhow::Result<String> {
        Ok(serde_json::to_string_pretty(self)? + "\n")
    }

    pub(crate) fn any_disagreement(&self) -> bool {
        self.functions.iter().any(|f| f.status == Status::Disagrees)
    }

    pub(crate) fn summary(&self) -> String {
        let mut o = String::new();
        for f in &self.functions {
            line(&mut o, f);
        }
        for (title, pick) in [("Selected", true), ("Header", false)] {
            let fs: Vec<&FnResult> = self
                .functions
                .iter()
                .filter(|f| selected(f.origin) == pick)
                .collect();
            if fs.is_empty() {
                continue;
            }
            let _ = writeln!(o, "\n{title} functions by status ({} in all):", fs.len());
            for s in Status::ALL {
                let n = fs.iter().filter(|f| f.status == s).count();
                let _ = writeln!(o, "  {n:>4}  {}", s.label());
            }
        }
        let mut reasons: BTreeMap<&str, usize> = BTreeMap::new();
        for f in self
            .functions
            .iter()
            .filter(|f| f.status == Status::NotCheckable)
        {
            for r in &f.reasons {
                *reasons.entry(r.as_str()).or_default() += 1;
            }
        }
        let mut by_count: Vec<(usize, &str)> = reasons.into_iter().map(|(r, n)| (n, r)).collect();
        by_count.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(b.1)));
        if !by_count.is_empty() {
            let _ = writeln!(
                o,
                "\nReasons a function is not checkable, by number of functions:"
            );
            for (n, r) in by_count {
                let _ = writeln!(o, "  {n:>4}  {r}");
            }
        }
        let checked: Vec<&FnResult> = self.functions.iter().filter(|f| f.inputs > 0).collect();
        let sum = |g: &dyn Fn(&FnResult) -> usize| checked.iter().map(|f| g(f)).sum::<usize>();
        let _ = writeln!(
            o,
            "\nInputs: {} run through the model for {} functions; {} compared with compiled C, {} aborts confirmed, {} undefined, {} unsupported, {} disagreements.",
            sum(&|f| f.inputs),
            checked.len(),
            sum(&|f| f.compared),
            sum(&|f| f.aborts),
            sum(&|f| f.undefined),
            sum(&|f| f.unsupported),
            sum(&|f| f.disagreements),
        );
        let ms: Vec<&Mutants> = self
            .functions
            .iter()
            .filter_map(|f| f.mutants.as_ref())
            .collect();
        if !ms.is_empty() {
            let _ = writeln!(
                o,
                "Mutants: {} generated of {} candidates, {} set aside as equivalent, {} compiled, {} caught ({} of them by timeout only), {} survived ({} timed out where that does not count).",
                ms.iter().map(|m| m.generated).sum::<usize>(),
                ms.iter().map(|m| m.candidates).sum::<usize>(),
                ms.iter().map(|m| m.equivalent.len()).sum::<usize>(),
                ms.iter().map(|m| m.compiled).sum::<usize>(),
                ms.iter().map(|m| m.caught).sum::<usize>(),
                ms.iter().map(|m| m.caught_by_timeout).sum::<usize>(),
                ms.iter().map(|m| m.survivors.len()).sum::<usize>(),
                ms.iter().map(|m| m.timeouts_not_counted).sum::<usize>(),
            );
        }
        let _ = writeln!(
            o,
            "Seed {}, {} inputs per function, at most {} mutants per function. Time: {:.0} s, of which {:.0} s building the Lean driver.",
            self.seed, self.count, self.mutant_cap, self.seconds, self.build_seconds
        );
        o
    }
}

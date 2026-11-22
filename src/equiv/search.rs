//! How a theorem is searched for: the tier it starts at, chosen from what
//! the generator knows of both sides before any Lean runs, and what a
//! failed try says about the tier to try next. A theorem gets at most
//! [`TRIES`] tries.

use crate::equiv::prove::Tier;

/// The most tries any theorem gets.
pub(crate) const TRIES: usize = 2;

/// The tiers, by index: 0, 1 and 2.
///
/// Each has its own heartbeat budget, the most a try at that tier is
/// allowed, set from measurement (`docs/equiv-report.md`, "Budgets"), in
/// the units of `maxHeartbeats` (about 12,000 to the second per Lean
/// process on the machine measured, four at a time):
///
/// * tier 0, 400 thousand (about 30 s): its one proof needs 316, and a
///   theorem it runs out on goes to tier 1, which splits;
/// * tier 1, 8 million (about 11 min): the largest proof measured,
///   `h_to_i`, needs 4.2 million;
/// * tier 2, 4 million (about 5 min): its proofs need at most 262
///   thousand, no theorem that ran out closed with several times more, and
///   three of them grew past 5 GB before twice this, too much for four
///   tries at once on 16 GB.
pub(crate) fn tiers() -> Vec<Tier> {
    let t = |label: &str, tactic: &str, budget: u64| Tier {
        label: label.to_owned(),
        tactic: tactic.to_owned(),
        budget,
    };
    vec![
        t("tier 0", "equiv_tier0 [UNFOLD]", 400_000),
        t("tier 1", "equiv_tier1 [UNFOLD]", 8_000_000),
        t("tier 2", "equiv_tier2 [UNFOLD]", 4_000_000),
    ]
}

/// How a statement passes memory.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) enum Args {
    /// Scalars only, in and out.
    #[default]
    Scalars,
    /// C strings, no `bstr` argument; no script takes `IsCStr` apart.
    CStrings,
    /// A `bstr` argument, which tier 2's script takes apart.
    Bstrs,
}

/// What both sides reach, and how the statement passes memory: what the
/// tier is predicted from.
#[derive(Debug, Clone, Default)]
pub(crate) struct Reach {
    /// The C side reaches a loop (a recursive or fuelled definition).
    pub(crate) c_loops: bool,
    /// The C side reads objects with static storage.
    pub(crate) reads_statics: bool,
    /// Aeneas declarations without a body the Rust side reaches.
    pub(crate) axioms: Vec<String>,
    /// A body either side reaches has an `if`, a `match` or a bind (`←`,
    /// a step that can fail, which the rewriting turns into an `if`).
    pub(crate) branches: bool,
    pub(crate) args: Args,
}

/// The tier a theorem's first try runs at.
///
/// * A `bstr` argument: tier 2, the only script that takes `IsBstr` apart
///   and executes the C side's memory.
/// * Only scalars, and no `if`, `match` or bind on either side: tier 0,
///   since there is nothing to split.
/// * Otherwise tier 1: scalars with branches, and the C-string-only
///   shapes, where tier 2's script cannot start (it needs a `bstr`
///   hypothesis) and tier 1 gets furthest.
pub(crate) fn predict(r: &Reach) -> usize {
    match r.args {
        Args::Bstrs => 2,
        Args::Scalars if !r.branches => 0,
        Args::Scalars | Args::CStrings => 1,
    }
}

/// How a try failed, read from Lean's messages for the theorem.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Failure {
    /// Out of heartbeats, at the named step (`whnf`, `isDefEq`, ...).
    Budget { at: String },
    /// A step of the script failed before its end, with the first line.
    Script(String),
    /// The script ran to its end and left goals; what they mention.
    Unsolved(Residual),
    /// No error, but the axioms are not Lean's own, or never came.
    Axioms(String),
    /// Lean stopped without a word on the theorem (killed, out of
    /// memory). Not a property of the theorem: never cached.
    Stopped(String),
}

/// The memory the goals a script left mention.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) enum Left {
    #[default]
    Nothing,
    /// The C side's memory (`StateT.run`, `Mem.`, `Region`, `IsBstr`) or
    /// a library call over it (`memcmp`).
    Memory,
    /// A C string: `IsCStr`, or `strlen` on either side.
    CString,
}

/// What the goals a script left mention.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Residual {
    /// An `if` or `match` is left on either side.
    pub(crate) branch: bool,
    pub(crate) memory: Left,
    /// A static object.
    pub(crate) statics: bool,
    /// The Rust recursions named, other than those a tier has a lemma or
    /// a reason for (`clib.memcmp_loop`, `clib.strlen_loop`).
    pub(crate) loops: Vec<String>,
}

/// The Rust recursions tier 2 has a lemma for, or that `Residual::cstr`
/// accounts for.
const KNOWN_LOOPS: [&str; 2] = ["clib.memcmp_loop", "clib.strlen_loop"];

impl Failure {
    /// The failure the errors of one try describe, first error first.
    pub(crate) fn read(errors: &[String]) -> Self {
        if let Some(e) = errors
            .iter()
            .find(|e| e.contains("maximum number of heartbeats"))
        {
            let at = e
                .split_once("timeout at `")
                .and_then(|(_, r)| r.split_once('`'))
                .map_or("", |(a, _)| a);
            return Self::Budget { at: at.to_owned() };
        }
        let Some(first) = errors.first() else {
            return Self::Axioms(String::new());
        };
        if !first.starts_with("unsolved goals") {
            let line = first.lines().next().unwrap_or("");
            return Self::Script(line.to_owned());
        }
        let has = |k: &[&str]| k.iter().any(|k| first.contains(k));
        let mut loops: Vec<String> = first
            .split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '.'))
            .filter(|t| t.ends_with("_loop") && !KNOWN_LOOPS.iter().any(|k| t.ends_with(k)))
            .map(str::to_owned)
            .collect();
        loops.sort();
        loops.dedup();
        let memory = if has(&["IsCStr", "strlen"]) {
            Left::CString
        } else if has(&["StateT.run", "Mem.", "Region", "IsBstr", "memcmp"]) {
            Left::Memory
        } else {
            Left::Nothing
        };
        Self::Unsolved(Residual {
            branch: has(&["if ", "match "]),
            memory,
            statics: has(&["Statics."]),
            loops,
        })
    }
}

/// What to do after a failed try.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Next {
    /// Try again at this tier.
    Tier(usize),
    /// No tier would help; the reason, as the report gives it.
    Stop(String),
}

pub(crate) const AXIOM: &str = "Aeneas axiom reached";
pub(crate) const C_LOOP: &str = "loop: a C loop needs a fuel bound and an invariant";
pub(crate) const RUST_LOOP: &str = "loop: a Rust recursion needs an induction";
pub(crate) const STATICS: &str = "memory: static tables against Aeneas constants";
pub(crate) const CSTR: &str =
    "memory: a C string argument (no script takes `IsCStr` apart; `strlen` has no lemma)";
pub(crate) const MEMORY: &str = "memory correspondence";
pub(crate) const BUDGET: &str = "budget: out of heartbeats at the top tier for its shape";
pub(crate) const ARITH: &str = "arithmetic or unfolding";

/// The tier a failure at `tier` points to, or why none would help.
///
/// What no tier has comes first, whatever the failure: an Aeneas axiom, a
/// C loop (no script has a loop rule), a Rust recursion without a lemma,
/// a static table. Then the failure itself:
///
/// * out of heartbeats at tier 0, which does not split: tier 1, whose
///   leaves are smaller (tier 2 with a `bstr` argument); at tier 1 with a
///   `bstr` argument: tier 2; otherwise this was the top tier for the
///   theorem's shape;
/// * goals left that mention memory: tier 2 if there is a `bstr`
///   argument and it was not tried; else a C string, or a memory form
///   tier 2 does not cover;
/// * goals left with an `if` or `match` after tier 0: tier 1;
/// * anything else: arithmetic tier 1's closer does not finish, or a
///   script step that does not apply.
pub(crate) fn decide(tier: usize, failure: &Failure, r: &Reach) -> Next {
    let stop = |s: &str| Next::Stop(s.to_owned());
    let bstr = r.args == Args::Bstrs;
    let up = |t: usize| {
        if t > tier {
            Next::Tier(t)
        } else {
            stop(BUDGET)
        }
    };
    if !r.axioms.is_empty() {
        return stop(AXIOM);
    }
    if let Failure::Axioms(a) = failure {
        return Next::Stop(format!(
            "no error, but the theorem's axioms are not Lean's own (or were never reported){}",
            if a.is_empty() {
                String::new()
            } else {
                format!(": {a}")
            }
        ));
    }
    if let Failure::Stopped(why) = failure {
        return Next::Stop(why.clone());
    }
    if r.c_loops {
        return stop(C_LOOP);
    }
    let residual = match failure {
        Failure::Unsolved(res) => Some(res),
        _ => None,
    };
    if residual.is_some_and(|res| !res.loops.is_empty()) {
        return stop(RUST_LOOP);
    }
    if r.reads_statics || residual.is_some_and(|res| res.statics) {
        return stop(STATICS);
    }
    match failure {
        Failure::Budget { .. } => match (tier, bstr) {
            (0, true) => up(2),
            (0, false) | (1, true) => up(tier + 1),
            _ => stop(BUDGET),
        },
        Failure::Unsolved(res) if res.memory != Left::Nothing => {
            if bstr && tier < 2 {
                up(2)
            } else if res.memory == Left::CString || r.args == Args::CStrings {
                stop(CSTR)
            } else {
                stop(MEMORY)
            }
        }
        Failure::Unsolved(res) if res.branch && tier == 0 => up(1),
        Failure::Script(_) if bstr && tier < 2 => up(2),
        Failure::Script(line) => Next::Stop(format!("tier {tier}'s script does not apply: {line}")),
        _ => stop(ARITH),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scalar(branches: bool) -> Reach {
        Reach {
            branches,
            ..Reach::default()
        }
    }

    fn bstr() -> Reach {
        Reach {
            args: Args::Bstrs,
            branches: true,
            ..Reach::default()
        }
    }

    fn cstr_only() -> Reach {
        Reach {
            args: Args::CStrings,
            branches: true,
            ..Reach::default()
        }
    }

    #[test]
    fn the_prediction_on_the_shapes_of_misc() {
        // `ucdGraphemeDone`: one comparison, nothing to split.
        assert_eq!(predict(&scalar(false)), 0);
        // The `ctype.h` tests and `ucdToCharacterWidth` (a shift, which
        // can fail).
        assert_eq!(predict(&scalar(true)), 1);
        // `bstrcmp`, `bstr_startswith`.
        assert_eq!(predict(&bstr()), 2);
        // C strings only (`bstr0`, `mp_natural_sort_cmp`).
        assert_eq!(predict(&cstr_only()), 1);
        // A loop does not change the start: the first try is what tells.
        let looping = Reach {
            c_loops: true,
            ..bstr()
        };
        assert_eq!(predict(&looping), 2);
    }

    #[test]
    fn a_tier_never_repeats_or_goes_down() {
        let budget = Failure::Budget { at: "whnf".into() };
        for tier in 0..3 {
            for r in [scalar(false), scalar(true), bstr()] {
                if let Next::Tier(t) = decide(tier, &budget, &r) {
                    assert!(t > tier);
                }
            }
        }
        assert_eq!(decide(2, &budget, &bstr()), Next::Stop(BUDGET.into()));
    }

    /// First errors of the measured run (`lean --json`, the theorem's
    /// first error message), with the tier of the try.
    const FAILURES: &str = include_str!("testdata/failures.json");

    fn failure(theorem: &str, tier: usize) -> Failure {
        let all: serde_json::Value = serde_json::from_str(FAILURES).unwrap_or_default();
        let error = all
            .as_array()
            .into_iter()
            .flatten()
            .find(|f| {
                f.get("theorem").and_then(serde_json::Value::as_str) == Some(theorem)
                    && f.get("tier").and_then(serde_json::Value::as_u64) == Some(tier as u64)
            })
            .and_then(|f| f.get("error")?.as_str())
            .unwrap_or_default()
            .to_owned();
        assert!(!error.is_empty(), "no error for {theorem} at tier {tier}");
        Failure::read(&[error])
    }

    #[test]
    fn real_failures_map_to_the_tier_that_addresses_them() {
        let scalar_statics = Reach {
            reads_statics: true,
            ..scalar(true)
        };
        let bstr_loop = Reach {
            c_loops: true,
            ..bstr()
        };
        let cases: [(&str, usize, Reach, Next); 12] = [
            // Out of heartbeats at tier 0, which does not split: tier 1
            // (measured: proved there in 245 s).
            ("mp_isalnum", 0, scalar(true), Next::Tier(1)),
            // An `if` left by tier 0: tier 1 splits it.
            ("mp_isupper", 0, scalar(true), Next::Tier(1)),
            // Memory left by tier 1, a `bstr` argument: tier 2.
            ("bstrcmp", 1, bstr(), Next::Tier(2)),
            // Out of heartbeats at tier 1 with scalars only: the top tier
            // for the shape.
            ("h_to_i", 1, scalar(true), Next::Stop(BUDGET.into())),
            ("bstr_splice", 2, bstr(), Next::Stop(BUDGET.into())),
            // An arithmetic goal tier 1's closer leaves.
            ("rotl_u64", 1, scalar(true), Next::Stop(ARITH.into())),
            (
                "ucdGraphemeJoins",
                1,
                scalar_statics.clone(),
                Next::Stop(STATICS.into()),
            ),
            ("ucdLookup", 2, scalar_statics, Next::Stop(STATICS.into())),
            // `memchr_loop`, a recursion with no lemma.
            ("bstrchr", 2, bstr(), Next::Stop(RUST_LOOP.into())),
            ("bstrcspn", 2, bstr_loop, Next::Stop(C_LOOP.into())),
            // Only `memcmp_loop`, which tier 2 has: another memory form.
            ("bstr_endswith", 2, bstr(), Next::Stop(MEMORY.into())),
            // A C string and no `bstr`: tier 2 cannot start.
            ("bstr0", 1, cstr_only(), Next::Stop(CSTR.into())),
        ];
        for (thm, tier, r, want) in cases {
            assert_eq!(decide(tier, &failure(thm, tier), &r), want, "{thm}");
        }
    }

    #[test]
    fn reading_a_failure() {
        assert_eq!(failure("h_to_i", 1), Failure::Budget { at: "whnf".into() });
        let residual = |f: Failure| match f {
            Failure::Unsolved(r) => Some(r),
            _ => None,
        };
        let r = residual(failure("bstrchr", 2)).unwrap_or_default();
        assert_eq!(r.loops, vec!["rmpv_misc.clib.memchr_loop".to_owned()]);
        assert!(r.memory == Left::Memory && r.branch);
        let r = residual(failure("rotl_u64", 1));
        assert!(r.is_some_and(|r| r.branch && r.memory == Left::Nothing && r.loops.is_empty()));
        assert!(
            matches!(failure("ucdLookup", 2), Failure::Script(l) if l.contains("did not unfold"))
        );
    }
}

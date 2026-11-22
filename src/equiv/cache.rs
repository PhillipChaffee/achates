//! The tier cache (`equiv/tiers.json`): for each theorem, what the last
//! search found, under a key that hashes everything the result depends
//! on. An entry whose key differs from the theorem's key now is stale and
//! the theorem is searched again; its time still serves as the cost
//! estimate that orders the queue.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use anyhow::{Context as _, Result};
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::equiv::lean::Def;
use crate::equiv::prove::{Goal, HEADER, Tier};
use crate::equiv::sha256::Sha256;

/// Bumped when the search itself (the prediction, the failure mapping,
/// the try limit) changes, which the hashed files do not show.
const SEARCH_VERSION: &str = "equiv-search 1";

/// One try, as recorded.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub(crate) struct TryRecord {
    pub(crate) tier: usize,
    /// The `maxHeartbeats` it ran with.
    pub(crate) budget: u64,
    /// What it used, when Lean reported it.
    pub(crate) heartbeats: Option<u64>,
    pub(crate) seconds: f64,
    /// `proved`, or what the failure was.
    pub(crate) result: String,
    /// The first error's first lines, when it failed.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) first_error: Option<String>,
}

/// What became of one theorem.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub(crate) struct Entry {
    pub(crate) key: String,
    /// The tier that proved it, if one did.
    pub(crate) proved: Option<usize>,
    /// Why it is open, when it is.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) reason: Option<String>,
    pub(crate) tries: Vec<TryRecord>,
    /// The `#print axioms` message of the proof.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) axioms: Option<String>,
}

impl Entry {
    /// Wall time of its tries, the cost estimate for the next search.
    pub(crate) fn seconds(&self) -> f64 {
        self.tries.iter().map(|t| t.seconds).sum()
    }
}

#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
pub(crate) struct Cache {
    #[serde(default)]
    pub(crate) about: String,
    pub(crate) theorems: BTreeMap<String, Entry>,
}

const ABOUT: &str = "Written by `achates equiv --prove`: per theorem, the outcome of its \
    last search and the key it holds for. See docs/equiv-report.md, \"The cache\".";

/// The cache at `path`; empty if there is none, or if it cannot be read
/// (with a warning: the search then starts over).
pub(crate) fn load(path: &Path) -> Cache {
    let Ok(text) = std::fs::read_to_string(path) else {
        return Cache::default();
    };
    serde_json::from_str(&text).unwrap_or_else(|e| {
        eprintln!(
            "achates equiv: ignoring {}: {e}; every theorem is searched",
            path.display()
        );
        Cache::default()
    })
}

pub(crate) fn save(path: &Path, cache: &Cache) -> Result<()> {
    let mut c = cache.clone();
    ABOUT.clone_into(&mut c.about);
    std::fs::write(path, serde_json::to_string_pretty(&c)? + "\n")
        .with_context(|| format!("writing {}", path.display()))
}

/// Feeds `part` with its length first, so that no two lists of parts
/// hash the same.
fn feed(h: &mut Sha256, part: &[u8]) {
    h.update(&(part.len() as u64).to_le_bytes());
    h.update(part);
}

/// The digest of the definitions `names` of `defs`, each with its name
/// and text, in name order; a name with no definition is skipped.
pub(crate) fn defs_digest<'a>(
    defs: &BTreeMap<String, Def>,
    names: impl IntoIterator<Item = &'a String>,
) -> String {
    let mut names: Vec<&String> = names.into_iter().collect();
    names.sort();
    names.dedup();
    let mut h = Sha256::default();
    for n in names {
        if let Some(d) = defs.get(n) {
            feed(&mut h, n.as_bytes());
            feed(&mut h, d.text.as_bytes());
        }
    }
    h.hex()
}

/// Every file under `dir` whose name satisfies `keep`, skipping `.lake`,
/// sorted.
fn files(dir: &Path, keep: &dyn Fn(&Path) -> bool, out: &mut Vec<PathBuf>) -> Result<()> {
    for e in std::fs::read_dir(dir).with_context(|| format!("reading {}", dir.display()))? {
        let p = e?.path();
        if p.file_name().is_some_and(|n| n == ".lake" || n == ".git") {
            continue;
        }
        if p.is_dir() {
            files(&p, keep, out)?;
        } else if keep(&p) {
            out.push(p);
        }
    }
    out.sort();
    Ok(())
}

/// The part of every key that does not depend on the theorem: the
/// search's version, the attempt header, every tier's script and budget,
/// the toolchain (`lean --version` and `lean-toolchain`), the Lake
/// configuration and manifest (which pins Mathlib), every Lean file of
/// the path packages the manifest names (the Achates runtime, the Aeneas
/// library) and of the Equiv library, except the generated
/// `Proved.lean`. The two generated sides enter per theorem, by the
/// definitions it reaches.
pub(crate) fn global_key(lake_dir: &Path, tiers: &[Tier], toolchain: &str) -> Result<String> {
    let mut h = Sha256::default();
    feed(&mut h, SEARCH_VERSION.as_bytes());
    feed(&mut h, HEADER.as_bytes());
    for t in tiers {
        feed(&mut h, t.label.as_bytes());
        feed(&mut h, t.tactic.as_bytes());
        feed(&mut h, &t.budget.to_le_bytes());
    }
    feed(&mut h, toolchain.as_bytes());
    let mut paths = Vec::new();
    for f in ["lean-toolchain", "lakefile.toml", "lake-manifest.json"] {
        let p = lake_dir.join(f);
        if p.exists() {
            paths.push(p);
        }
    }
    let lean = |p: &Path| p.extension().is_some_and(|x| x == "lean");
    let mut lib = Vec::new();
    files(
        &lake_dir.join("Equiv"),
        &|p| lean(p) && p.file_name().is_none_or(|n| n != "Proved.lean"),
        &mut lib,
    )?;
    paths.extend(lib);
    let manifest: Value = std::fs::read_to_string(lake_dir.join("lake-manifest.json"))
        .ok()
        .and_then(|t| serde_json::from_str(&t).ok())
        .unwrap_or(Value::Null);
    let packages = manifest
        .get("packages")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default();
    for p in packages {
        if p.get("type").and_then(Value::as_str) != Some("path") {
            continue;
        }
        let Some(dir) = p.get("dir").and_then(Value::as_str) else {
            continue;
        };
        let mut pkg = Vec::new();
        files(
            &lake_dir.join(dir),
            &|p| {
                lean(p)
                    || p.file_name()
                        .is_some_and(|n| n.to_string_lossy().starts_with("lakefile"))
            },
            &mut pkg,
        )?;
        paths.extend(pkg);
    }
    for p in paths {
        let text = std::fs::read(&p).with_context(|| format!("reading {}", p.display()))?;
        // The path relative to the Lake project, so the key does not
        // depend on where the checkout is.
        let rel = p.strip_prefix(lake_dir).unwrap_or(&p);
        feed(&mut h, rel.to_string_lossy().as_bytes());
        feed(&mut h, &text);
    }
    Ok(h.hex())
}

/// The key of one theorem: the global part, the statement, the unfold
/// list its scripts get, and the digest of the definitions it reaches.
pub(crate) fn key(global: &str, goal: &Goal) -> String {
    let mut h = Sha256::default();
    feed(&mut h, global.as_bytes());
    feed(&mut h, goal.name.as_bytes());
    feed(&mut h, goal.text.as_bytes());
    for u in &goal.unfold {
        feed(&mut h, u.as_bytes());
    }
    feed(&mut h, goal.sources.as_bytes());
    h.hex()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::equiv::lean;

    const SIDE: &str = "namespace A\n\n\
        def f (fuel : Nat) (c : I8) : M I32 := do\n  let x ← A.g fuel c\n  return x\n\n\
        def g (fuel : Nat) (c : I8) : M I32 := do\n  A.h fuel c\n\n\
        def h (fuel : Nat) (c : I8) : M I32 := do\n  return 0\n\n\
        def k (fuel : Nat) (c : I8) : M I32 := do\n  return 1\n\nend A\n";

    /// The digest `achates equiv` keys `A.f` by: every definition it
    /// reaches.
    fn digest_of_f(text: &str) -> String {
        let defs: BTreeMap<String, Def> = lean::parse(text)
            .into_iter()
            .map(|d| (d.name.clone(), d))
            .collect();
        defs_digest(&defs, &lean::reach(&defs, "A.f", &[]))
    }

    #[test]
    fn the_key_follows_the_definitions_reached_and_only_those() {
        let base = digest_of_f(SIDE);
        assert_eq!(base, digest_of_f(SIDE));
        // `h` is reached through `g`: a comment in it changes the key.
        let callee = SIDE.replace("  return 0", "  -- a comment\n  return 0");
        assert_ne!(base, digest_of_f(&callee));
        let own = SIDE.replace("  return x", "  return x -- here");
        assert_ne!(base, digest_of_f(&own));
        // `k` is not reached.
        let unrelated = SIDE.replace("  return 1", "  return 2");
        assert_eq!(base, digest_of_f(&unrelated));
    }

    fn scratch(name: &str) -> PathBuf {
        let d = std::env::temp_dir().join(format!("achates-cache-{}-{name}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        d
    }

    #[test]
    fn the_key_follows_the_library_the_tiers_and_the_toolchain() -> Result<()> {
        let dir = scratch("lib");
        std::fs::create_dir_all(dir.join("Equiv"))?;
        std::fs::create_dir_all(dir.join("runtime/.lake"))?;
        std::fs::write(
            dir.join("lake-manifest.json"),
            r#"{"packages":[{"type":"path","name":"achates","dir":"runtime"}]}"#,
        )?;
        std::fs::write(dir.join("runtime/R.lean"), "def r := 1\n")?;
        std::fs::write(dir.join("runtime/.lake/Built.lean"), "x")?;
        std::fs::write(
            dir.join("Equiv/Tactic.lean"),
            "macro \"t\" : tactic => `(tactic| rfl)\n",
        )?;
        std::fs::write(dir.join("Equiv/Proved.lean"), "-- generated\n")?;
        let tiers = crate::equiv::search::tiers();
        let k = |tiers: &[Tier], tc: &str| global_key(&dir, tiers, tc);
        let base = k(&tiers, "Lean 4.36.0")?;
        assert_eq!(base, k(&tiers, "Lean 4.36.0")?);
        assert_ne!(base, k(&tiers, "Lean 4.37.0")?);
        let mut more = tiers.clone();
        if let Some(t) = more.first_mut() {
            t.budget += 1;
        }
        assert_ne!(base, k(&more, "Lean 4.36.0")?);
        // The generated proofs and the build directory do not count.
        std::fs::write(dir.join("Equiv/Proved.lean"), "-- generated again\n")?;
        std::fs::write(dir.join("runtime/.lake/Built.lean"), "y")?;
        assert_eq!(base, k(&tiers, "Lean 4.36.0")?);
        std::fs::write(dir.join("Equiv/Tactic.lean"), "-- changed\n")?;
        let lib = k(&tiers, "Lean 4.36.0")?;
        assert_ne!(base, lib);
        std::fs::write(dir.join("runtime/R.lean"), "def r := 2\n")?;
        assert_ne!(lib, k(&tiers, "Lean 4.36.0")?);
        std::fs::remove_dir_all(&dir)?;
        Ok(())
    }

    #[test]
    fn a_cache_reads_back_as_written() -> Result<()> {
        let dir = scratch("rt");
        std::fs::create_dir_all(&dir)?;
        let path = dir.join("tiers.json");
        assert_eq!(load(&path), Cache::default());
        let mut c = Cache::default();
        c.theorems.insert(
            "bstrcmp".into(),
            Entry {
                key: "ab".into(),
                proved: Some(2),
                reason: None,
                tries: vec![TryRecord {
                    tier: 2,
                    budget: 4_000_000,
                    heartbeats: Some(812_000),
                    seconds: 42.5,
                    result: "proved".into(),
                    first_error: None,
                }],
                axioms: Some("'Equiv.Gen.bstrcmp' depends on axioms: [propext]".into()),
            },
        );
        c.theorems.insert(
            "bstrchr".into(),
            Entry {
                key: "cd".into(),
                proved: None,
                reason: Some("loop: a Rust recursion needs an induction".into()),
                tries: vec![TryRecord {
                    tier: 2,
                    budget: 4_000_000,
                    heartbeats: None,
                    seconds: 1.0,
                    result: "unsolved goals".into(),
                    first_error: Some("unsolved goals\n".into()),
                }],
                axioms: None,
            },
        );
        save(&path, &c)?;
        let back = load(&path);
        assert_eq!(back.theorems, c.theorems);
        std::fs::write(&path, "not json")?;
        assert_eq!(load(&path), Cache::default());
        std::fs::remove_dir_all(&dir)?;
        Ok(())
    }
}

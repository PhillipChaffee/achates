//! Running clang and reading its JSON syntax tree.
//!
//! clang omits `file` and `line` from a location when they equal those of the
//! location it printed just before, in document order, across the whole
//! dump. [`LocState`] replays that rule so that every location object comes
//! out self-contained, whatever node it sits in.

use std::collections::HashMap;
use std::fmt;
use std::path::PathBuf;
use std::process::Command;

use anyhow::{Context as _, Result, bail};
use serde::de::{DeserializeSeed, IgnoredAny, MapAccess, SeqAccess, Visitor};
use serde_json::{Map, Value};

use crate::compdb::{ClangArgs, Entry, normalize};

pub(crate) const CLANG: &str = "clang";

/// Runs clang in the entry's directory and returns its stdout, or an error
/// naming the file with the tail of clang's diagnostics.
pub(crate) fn run(entry: &Entry, args: &[String], what: &str) -> Result<Vec<u8>> {
    let out = Command::new(CLANG)
        .args(args)
        .current_dir(&entry.directory)
        .output()
        .with_context(|| format!("starting {CLANG} for {}", entry.file))?;
    if !out.status.success() {
        let err = String::from_utf8_lossy(&out.stderr);
        let lines: Vec<&str> = err.lines().collect();
        let tail = lines
            .get(lines.len().saturating_sub(20)..)
            .unwrap_or_default();
        bail!(
            "{CLANG} failed ({what}) on {}: {}\n{}",
            entry.file,
            out.status,
            tail.join("\n")
        );
    }
    Ok(out.stdout)
}

/// Tracks the location de-duplication state of clang's JSON dumper.
#[derive(Debug, Default)]
pub(crate) struct LocState {
    file: Option<String>,
    line: Option<u64>,
}

impl LocState {
    /// Walks `v` in document order and fills in every omitted `file` and
    /// `line`. Requires `serde_json`'s `preserve_order`, since the order of
    /// keys is the order clang printed them.
    pub(crate) fn normalize(&mut self, v: &mut Value) {
        match v {
            Value::Object(m) => {
                if m.contains_key("offset") {
                    self.bare(m);
                    return;
                }
                for (k, child) in m.iter_mut() {
                    // `includedFrom` names a file without being a location.
                    if k != "includedFrom" {
                        self.normalize(child);
                    }
                }
            }
            Value::Array(a) => {
                for child in a {
                    self.normalize(child);
                }
            }
            _ => {}
        }
    }

    fn bare(&mut self, m: &mut Map<String, Value>) {
        match m.get("file").and_then(Value::as_str) {
            Some(f) => self.file = Some(f.to_owned()),
            None => {
                if let Some(f) = &self.file {
                    m.insert("file".into(), Value::String(f.clone()));
                }
            }
        }
        match m.get("line").and_then(Value::as_u64) {
            Some(l) => self.line = Some(l),
            None => {
                if let Some(l) = self.line {
                    m.insert("line".into(), Value::from(l));
                }
            }
        }
    }
}

/// The top-level declarations Achates keeps from one translation unit.
#[derive(Debug, Default)]
pub(crate) struct RawTu {
    /// Function definitions whose name is in the main file.
    pub(crate) functions: Vec<Value>,
    /// Records, enums, typedefs and file-scope variables from every file.
    pub(crate) decls: Vec<Value>,
    /// Every function declaration by id, for resolving linkage across redeclarations.
    pub(crate) fn_decls: HashMap<String, FnDeclInfo>,
}

#[derive(Debug, Clone)]
pub(crate) struct FnDeclInfo {
    pub(crate) is_static: bool,
    pub(crate) previous: Option<String>,
}

/// Where a node is: the expansion location, so code produced by a macro is
/// placed where the macro was used.
#[derive(serde::Serialize, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Loc {
    pub(crate) file: String,
    pub(crate) line: u64,
    pub(crate) col: u64,
}

impl fmt::Display for Loc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}:{}", self.file, self.line, self.col)
    }
}

/// Reads a location object after [`LocState::normalize`].
pub(crate) fn read_loc(v: &Value) -> Option<Loc> {
    let bare = v.get("expansionLoc").unwrap_or(v);
    Some(Loc {
        file: bare.get("file")?.as_str()?.to_owned(),
        line: bare.get("line")?.as_u64()?,
        col: bare.get("col")?.as_u64()?,
    })
}

/// The best location of a node: its `loc`, else the start of its range.
pub(crate) fn node_loc(v: &Value) -> Option<Loc> {
    v.get("loc").and_then(read_loc).or_else(|| {
        v.get("range")
            .and_then(|r| r.get("begin"))
            .and_then(read_loc)
    })
}

pub(crate) fn range_lines(v: &Value) -> Option<(u64, u64)> {
    let r = v.get("range")?;
    Some((
        read_loc(r.get("begin")?)?.line,
        read_loc(r.get("end")?)?.line,
    ))
}

/// Runs clang's JSON dump on the entry and keeps what the IR needs.
pub(crate) fn load_ast(entry: &Entry, args: &ClangArgs) -> Result<RawTu> {
    let mut cmd = args.flags.clone();
    cmd.extend(["-fsyntax-only", "-Xclang", "-ast-dump=json"].map(String::from));
    cmd.push(entry.file.clone());
    let out = run(entry, &cmd, "syntax tree")?;
    parse_ast(entry, &out)
}

pub(crate) fn parse_ast(entry: &Entry, json: &[u8]) -> Result<RawTu> {
    let mut sink = Sink {
        entry,
        main: entry.path.clone(),
        tu: RawTu::default(),
        cache: HashMap::new(),
    };
    let mut de = serde_json::Deserializer::from_slice(json);
    TuSeed { sink: &mut sink }
        .deserialize(&mut de)
        .with_context(|| format!("reading clang's syntax tree for {}", entry.file))?;
    de.end()
        .with_context(|| format!("trailing data in clang's output for {}", entry.file))?;
    Ok(sink.tu)
}

struct Sink<'a> {
    entry: &'a Entry,
    main: PathBuf,
    tu: RawTu,
    cache: HashMap<String, bool>,
}

impl Sink<'_> {
    fn is_main(&mut self, file: &str) -> bool {
        if let Some(b) = self.cache.get(file) {
            return *b;
        }
        let b = normalize(&self.entry.directory.join(file)) == self.main;
        self.cache.insert(file.to_owned(), b);
        b
    }

    fn take(&mut self, v: Value) {
        let kind = v.get("kind").and_then(Value::as_str).unwrap_or("");
        match kind {
            "FunctionDecl" => {
                if let Some(id) = v.get("id").and_then(Value::as_str) {
                    let info = FnDeclInfo {
                        is_static: v.get("storageClass").and_then(Value::as_str) == Some("static"),
                        previous: v
                            .get("previousDecl")
                            .and_then(Value::as_str)
                            .map(String::from),
                    };
                    self.tu.fn_decls.insert(id.to_owned(), info);
                }
                let has_body = v.get("inner").and_then(Value::as_array).is_some_and(|a| {
                    a.iter()
                        .any(|c| c.get("kind") == Some(&"CompoundStmt".into()))
                });
                let in_main = node_loc(&v).is_some_and(|l| self.is_main(&l.file));
                if has_body && in_main {
                    self.tu.functions.push(v);
                }
            }
            "RecordDecl" | "EnumDecl" | "TypedefDecl" | "VarDecl" => self.tu.decls.push(v),
            _ => {}
        }
    }
}

struct TuSeed<'s, 'a> {
    sink: &'s mut Sink<'a>,
}

impl<'de> DeserializeSeed<'de> for TuSeed<'_, '_> {
    type Value = ();
    fn deserialize<D: serde::Deserializer<'de>>(self, d: D) -> Result<(), D::Error> {
        d.deserialize_map(self)
    }
}

impl<'de> Visitor<'de> for TuSeed<'_, '_> {
    type Value = ();
    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a TranslationUnitDecl object")
    }
    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<(), A::Error> {
        let mut state = LocState::default();
        while let Some(key) = map.next_key::<String>()? {
            if key == "inner" {
                map.next_value_seed(InnerSeed {
                    sink: self.sink,
                    state: &mut state,
                })?;
            } else {
                map.next_value::<IgnoredAny>()?;
            }
        }
        Ok(())
    }
}

struct InnerSeed<'s, 'a> {
    sink: &'s mut Sink<'a>,
    state: &'s mut LocState,
}

impl<'de> DeserializeSeed<'de> for InnerSeed<'_, '_> {
    type Value = ();
    fn deserialize<D: serde::Deserializer<'de>>(self, d: D) -> Result<(), D::Error> {
        d.deserialize_seq(self)
    }
}

impl<'de> Visitor<'de> for InnerSeed<'_, '_> {
    type Value = ();
    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("the top-level declarations")
    }
    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<(), A::Error> {
        // One top-level declaration at a time: the dump of a file is tens of
        // MB, mostly header declarations that are dropped here.
        while let Some(mut v) = seq.next_element::<Value>()? {
            self.state.normalize(&mut v);
            self.sink.take(v);
        }
        Ok(())
    }
}

/// Reads several JSON values printed one after another, as clang does with
/// `-ast-dump-filter`.
pub(crate) fn parse_many(json: &[u8]) -> Result<Vec<Value>> {
    let mut out = Vec::new();
    for v in serde_json::Deserializer::from_slice(json).into_iter::<Value>() {
        let mut v = v.context("reading clang's filtered dump")?;
        LocState::default().normalize(&mut v);
        out.push(v);
    }
    Ok(out)
}

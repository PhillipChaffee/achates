//! Reads the headers and bodies of the Lean definitions on both sides: the
//! project Achates emitted for the C, and the file Aeneas wrote for the
//! Rust. Only the shapes those two generators write are recognised; this
//! is not a Lean parser.

use std::collections::{BTreeMap, BTreeSet};

/// One `def` or `axiom`.
#[derive(Debug, Clone)]
pub(crate) struct Def {
    /// Fully qualified name.
    pub(crate) name: String,
    /// Explicit parameters as (name, type).
    pub(crate) params: Vec<(String, String)>,
    /// The type after the last top-level colon, such as `M I32` or
    /// `Result Std.I32`.
    pub(crate) ret: String,
    pub(crate) body: String,
    pub(crate) axiom: bool,
}

impl Def {
    /// Calls itself, so unfolding it does not terminate: a loop that
    /// Aeneas turned into recursion, or a C function recursive in its fuel.
    pub(crate) fn recursive(&self) -> bool {
        self.body.contains("partial_fixpoint")
            || self.body.contains("termination_by")
            || tokens(&self.body).any(|t| t == self.name || self.name.ends_with(&format!(".{t}")))
    }
}

/// The identifiers of `text`, with their dots.
fn tokens(text: &str) -> impl Iterator<Item = &str> {
    text.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '.' || c == '\''))
        .filter(|t| !t.is_empty())
}

/// Splits a header's parameter part into its bracketed groups.
fn groups(s: &str) -> (Vec<String>, String) {
    let mut out = Vec::new();
    let mut depth = 0usize;
    let mut cur = String::new();
    let mut rest = String::new();
    let mut chars = s.char_indices().peekable();
    while let Some((i, c)) = chars.next() {
        if depth == 0 {
            if c == '(' || c == '[' || c == '{' {
                depth = 1;
                cur.clear();
                cur.push(c);
                continue;
            }
            if c == ':' {
                s.get(i + 1..).unwrap_or("").trim().clone_into(&mut rest);
                break;
            }
            continue;
        }
        cur.push(c);
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => {
                depth -= 1;
                if depth == 0 {
                    out.push(std::mem::take(&mut cur));
                }
            }
            _ => {}
        }
        let _ = chars.peek();
    }
    (out, rest)
}

fn header_end(line: &str) -> bool {
    line.trim_end().ends_with(":= do") || line.trim_end().ends_with(":=") || line.contains(" := ")
}

/// Every `def` and `axiom` of one file, under the namespaces it opens.
pub(crate) fn parse(text: &str) -> Vec<Def> {
    let lines: Vec<&str> = text.lines().collect();
    let mut ns: Vec<String> = Vec::new();
    let mut defs = Vec::new();
    let mut i = 0;
    while let Some(line) = lines.get(i) {
        if let Some(n) = line.strip_prefix("namespace ") {
            ns.push(n.trim().to_owned());
            i += 1;
            continue;
        }
        if line.starts_with("end ") && !ns.is_empty() {
            ns.pop();
            i += 1;
            continue;
        }
        let kw = if line.starts_with("def ") {
            Some(false)
        } else if line.starts_with("axiom ") {
            Some(true)
        } else {
            None
        };
        let Some(axiom) = kw else {
            i += 1;
            continue;
        };
        let mut header = String::new();
        let mut j = i;
        while let Some(l) = lines.get(j) {
            header.push(' ');
            header.push_str(l.trim());
            j += 1;
            let next_starts = lines
                .get(j)
                .is_none_or(|n| !n.starts_with(' ') || n.trim_start().starts_with("--"));
            if (!axiom && header_end(l)) || (axiom && next_starts) {
                break;
            }
        }
        let mut body = String::new();
        while let Some(l) = lines.get(j) {
            if l.starts_with("/--")
                || l.starts_with("def ")
                || l.starts_with("axiom ")
                || l.starts_with("@[")
                || l.starts_with("end ")
                || l.starts_with("structure ")
                || l.starts_with("inductive ")
                || l.starts_with("theorem ")
            {
                break;
            }
            body.push_str(l);
            body.push('\n');
            j += 1;
        }
        let head = header.trim();
        let head = head
            .strip_prefix(if axiom { "axiom " } else { "def " })
            .unwrap_or(head);
        let head = head.split(" := ").next().unwrap_or(head);
        let head = head.strip_suffix(":= do").unwrap_or(head);
        let head = head.strip_suffix(":=").unwrap_or(head).trim();
        let (short, sig) = head.split_once(' ').unwrap_or((head, ""));
        let (gs, ret) = groups(sig);
        let mut params = Vec::new();
        for g in gs {
            // Instance arguments (`[Ext.x]`) are skipped: `status.json` lists
            // the externals.
            if let Some(inner) = g.strip_prefix('(').and_then(|g| g.strip_suffix(')'))
                && let Some((n, t)) = inner.split_once(" : ")
            {
                for n in n.split_whitespace() {
                    params.push((n.to_owned(), t.trim().to_owned()));
                }
            }
        }
        let mut full = ns.join(".");
        if !full.is_empty() {
            full.push('.');
        }
        full.push_str(short);
        defs.push(Def {
            name: full,
            params,
            ret,
            body,
            axiom,
        });
        i = j;
    }
    defs
}

/// The definitions of `defs` that `name` reaches through its body,
/// transitively, `name` included. A body names a definition either fully
/// or relative to one of the namespaces `prefixes` lists.
pub(crate) fn reach(
    defs: &BTreeMap<String, Def>,
    name: &str,
    prefixes: &[&str],
) -> BTreeSet<String> {
    let mut seen = BTreeSet::new();
    let mut todo = vec![name.to_owned()];
    while let Some(n) = todo.pop() {
        if !seen.insert(n.clone()) {
            continue;
        }
        let Some(d) = defs.get(&n) else { continue };
        // A body may also name a definition relative to any namespace that
        // encloses its own, as Lean resolves names.
        let mut scopes: Vec<String> = prefixes.iter().map(|p| (*p).to_owned()).collect();
        let mut ns = n.as_str();
        while let Some((outer, _)) = ns.rsplit_once('.') {
            scopes.push(outer.to_owned());
            ns = outer;
        }
        for t in tokens(&d.body) {
            let candidates =
                std::iter::once(t.to_owned()).chain(scopes.iter().map(|p| format!("{p}.{t}")));
            for c in candidates {
                if defs.contains_key(&c) && !seen.contains(&c) {
                    todo.push(c);
                }
            }
        }
    }
    seen
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_an_emitted_c_definition() {
        let text = "namespace Misc.Misc.Bstr_c\n\n/-- C function. -/\n\
            def bstrcasecmp [Ext.strncasecmp] (fuel : Nat) (str1 : Agg) (str2 : Agg) : M I32 := do\n  \
            let x ← f\n  return x\n\nend Misc.Misc.Bstr_c\n";
        let defs = parse(text);
        let d = defs.first().unwrap();
        assert_eq!(d.name, "Misc.Misc.Bstr_c.bstrcasecmp");
        assert_eq!(d.params.len(), 3);
        assert_eq!(d.ret, "M I32");
        assert!(!d.recursive());
    }

    #[test]
    fn reads_an_aeneas_definition_over_several_lines() {
        let text = "namespace rmpv_misc\n\n@[rust_loop]\ndef clib.memcmp_loop\n  \
            (a : Slice Std.U8) (b : Slice Std.U8) (n : Std.Usize) (i : Std.Usize) :\n  \
            Result Std.I32\n  := do\n  if i < n\n  then clib.memcmp_loop a b n i\n  \
            else ok 0#i32\npartial_fixpoint\n\n/-- doc -/\ndef clib.memcmp\n  \
            (a : Slice Std.U8) : Result (Std.I32 × (Slice Std.U8)) := do\n  \
            clib.memcmp_loop a a 0#usize 0#usize\n";
        let defs = parse(text);
        let l = defs.first().unwrap();
        assert_eq!(l.name, "rmpv_misc.clib.memcmp_loop");
        assert_eq!(l.params.len(), 4);
        assert_eq!(l.ret, "Result Std.I32");
        assert!(l.recursive());
        let m = defs.get(1).unwrap();
        assert_eq!(m.ret, "Result (Std.I32 × (Slice Std.U8))");
        let map: BTreeMap<String, Def> = defs.into_iter().map(|d| (d.name.clone(), d)).collect();
        let r = reach(&map, "rmpv_misc.clib.memcmp", &[]);
        assert!(r.contains("rmpv_misc.clib.memcmp_loop"));
    }

    #[test]
    fn a_call_relative_to_an_enclosing_namespace_is_found() {
        let text = "namespace Misc.Misc.Ctype_h\n\ndef mp_isupper (fuel : Nat) (c : I8) : M I32 := do\n  \
            return 0\n\ndef mp_tolower (fuel : Nat) (c : I8) : M I8 := do\n  \
            let t1 : I32 ← Misc.Ctype_h.mp_isupper fuel c\n  return c\n\nend Misc.Misc.Ctype_h\n";
        let map: BTreeMap<String, Def> = parse(text)
            .into_iter()
            .map(|d| (d.name.clone(), d))
            .collect();
        let r = reach(&map, "Misc.Misc.Ctype_h.mp_tolower", &[]);
        assert!(r.contains("Misc.Misc.Ctype_h.mp_isupper"));
    }
}

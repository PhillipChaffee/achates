//! Planted bugs: small changes to the text of one C function. A check that
//! reports agreement on the original must report a difference on these, or
//! its agreement shows little.

use crate::check::input::Rng;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Mutant {
    pub(crate) line: usize,
    pub(crate) column: usize,
    /// The kind of change: `comparison`, `arithmetic`, `constant`,
    /// `logical`, `statement`.
    pub(crate) operator: &'static str,
    pub(crate) before: String,
    pub(crate) after: String,
    /// The whole file with the change applied.
    pub(crate) source: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Ident,
    Number,
    Punct,
    /// A string or character literal: never changed, but it ends an operand.
    Literal,
}

#[derive(Debug, Clone, Copy)]
struct Token<'a> {
    kind: Kind,
    text: &'a str,
    start: usize,
    line: usize,
    column: usize,
}

const PUNCT3: &[&str] = &["<<=", ">>=", "..."];
const PUNCT2: &[&str] = &[
    "->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||", "+=", "-=", "*=", "/=", "%=",
    "&=", "|=", "^=", "##",
];

/// The tokens of a C file. Comments, preprocessor lines and the insides of
/// literals yield no tokens, so no change is made there.
fn tokens(src: &str) -> Vec<Token<'_>> {
    let b = src.as_bytes();
    let mut out = Vec::new();
    let (mut i, mut line, mut line_start) = (0usize, 1usize, 0usize);
    let mut at_line_start = true;
    while let Some(&c) = b.get(i) {
        let next = b.get(i + 1).copied();
        if c == b'\n' {
            line += 1;
            line_start = i + 1;
            at_line_start = true;
            i += 1;
        } else if c.is_ascii_whitespace() {
            i += 1;
        } else if c == b'/' && next == Some(b'/') {
            while b.get(i).is_some_and(|x| *x != b'\n') {
                i += 1;
            }
        } else if c == b'/' && next == Some(b'*') {
            i += 2;
            while i < b.len() && !(b.get(i) == Some(&b'*') && b.get(i + 1) == Some(&b'/')) {
                if b.get(i) == Some(&b'\n') {
                    line += 1;
                    line_start = i + 1;
                }
                i += 1;
            }
            i += 2;
        } else if c == b'#' && at_line_start {
            // A directive runs to the end of the line, or further when the
            // line ends in a backslash.
            while let Some(&x) = b.get(i) {
                if x == b'\n' {
                    if i > 0 && b.get(i - 1) == Some(&b'\\') {
                        line += 1;
                        line_start = i + 1;
                    } else {
                        break;
                    }
                }
                i += 1;
            }
        } else {
            at_line_start = false;
            let start = i;
            let kind = if c == b'"' || c == b'\'' {
                i += 1;
                while let Some(&x) = b.get(i) {
                    if x == b'\\' {
                        i += 1;
                    } else if x == c || x == b'\n' {
                        break;
                    }
                    i += 1;
                }
                i += 1;
                Kind::Literal
            } else if c.is_ascii_alphabetic() || c == b'_' {
                while b
                    .get(i)
                    .is_some_and(|x| x.is_ascii_alphanumeric() || *x == b'_')
                {
                    i += 1;
                }
                Kind::Ident
            } else if c.is_ascii_digit() {
                while b
                    .get(i)
                    .is_some_and(|x| x.is_ascii_alphanumeric() || *x == b'.' || *x == b'_')
                {
                    i += 1;
                }
                Kind::Number
            } else {
                let rest = src.get(i..).unwrap_or("");
                let len = PUNCT3
                    .iter()
                    .chain(PUNCT2)
                    .find(|p| rest.starts_with(**p))
                    .map_or(1, |p| p.len());
                i += len;
                Kind::Punct
            };
            let end = i.min(b.len());
            if let Some(text) = src.get(start..end) {
                out.push(Token {
                    kind,
                    text,
                    start,
                    line,
                    column: start - line_start + 1,
                });
            }
        }
    }
    out
}

fn swap(text: &str) -> Option<(&'static str, &'static str)> {
    Some(match text {
        "<" => ("comparison", "<="),
        "<=" => ("comparison", "<"),
        ">" => ("comparison", ">="),
        ">=" => ("comparison", ">"),
        "==" => ("comparison", "!="),
        "!=" => ("comparison", "=="),
        "&&" => ("logical", "||"),
        "||" => ("logical", "&&"),
        "+=" => ("arithmetic", "-="),
        "-=" => ("arithmetic", "+="),
        "++" => ("arithmetic", "--"),
        "--" => ("arithmetic", "++"),
        "<<" => ("arithmetic", ">>"),
        ">>" => ("arithmetic", "<<"),
        "/" => ("arithmetic", "*"),
        "%" => ("arithmetic", "/"),
        _ => return None,
    })
}

/// `+` and `-` are changed only where they are binary: after an operand.
fn binary_swap(text: &str, prev: Option<&Token<'_>>) -> Option<(&'static str, &'static str)> {
    let after_operand = prev.is_some_and(|p| {
        matches!(p.kind, Kind::Ident | Kind::Number | Kind::Literal)
            && !matches!(p.text, "return" | "case" | "sizeof")
            || matches!(p.text, ")" | "]")
    });
    match text {
        "+" if after_operand => Some(("arithmetic", "-")),
        "-" if after_operand => Some(("arithmetic", "+")),
        _ => None,
    }
}

/// An integer constant one larger, in the notation it was written in.
fn bump(text: &str) -> Option<String> {
    if let Some(h) = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
        let v = u64::from_str_radix(h, 16).ok()?;
        return Some(format!("0x{:x}", v.checked_add(1)?));
    }
    if text.len() > 1 && text.starts_with('0') {
        let v = u64::from_str_radix(text, 8).ok()?;
        return Some(format!("0{:o}", v.checked_add(1)?));
    }
    let v: u64 = text.parse().ok()?;
    Some(v.checked_add(1)?.to_string())
}

const NOT_DROPPED: &[&str] = &[
    "return", "goto", "case", "default", "else", "for", "if", "while", "do", "switch", "struct",
    "union", "enum", "static", "const", "typedef", "extern", "register", "volatile", "unsigned",
    "signed", "int", "char", "long", "short", "float", "double", "void", "bool", "_Bool",
];

/// A statement on one line of its own that is not a declaration: its first
/// and last token index, when `first` starts one.
fn droppable(toks: &[Token<'_>], first: usize) -> Option<usize> {
    let t = toks.get(first)?;
    let prev = first.checked_sub(1).and_then(|i| toks.get(i));
    // After `)` or `else` on an earlier line, the statement is the body of
    // an `if`, a loop or an `else`, and `;` in its place is still one.
    if prev.is_some_and(|p| {
        p.line == t.line || !matches!(p.text, ";" | "{" | "}" | ":" | ")" | "else")
    }) {
        return None;
    }
    if t.kind != Kind::Ident && !matches!(t.text, "*" | "++" | "--" | "(") {
        return None;
    }
    if NOT_DROPPED.contains(&t.text) {
        return None;
    }
    let last = (first..toks.len()).find(|i| toks.get(*i).is_some_and(|x| x.text == ";"))?;
    let end = toks.get(last)?;
    if end.line != t.line || toks.get(last + 1).is_some_and(|n| n.line == t.line) {
        return None;
    }
    let body = toks.get(first..last)?;
    // `type name ...` and `type *name ...` declare; an expression statement
    // never starts with two names.
    let declares = matches!(body, [a, b, ..] if a.kind == Kind::Ident
        && (b.kind == Kind::Ident
            || (b.text == "*" && matches!(body.get(2), Some(c) if c.kind == Kind::Ident)
                && !body.iter().any(|x| x.text == "=" ) )));
    let effect = body.len() == 1
        || body.iter().any(|x| {
            matches!(
                x.text,
                "=" | "("
                    | "++"
                    | "--"
                    | "+="
                    | "-="
                    | "*="
                    | "/="
                    | "%="
                    | "&="
                    | "|="
                    | "^="
                    | "<<="
                    | ">>="
            )
        });
    (!declares && effect && !body.iter().any(|x| matches!(x.text, "{" | "}"))).then_some(last)
}

/// Every single change the operators make to the function that occupies
/// `lines` lines from `first_line`; at most `cap` of them, chosen by a
/// generator seeded with `seed` and the function's position.
pub(crate) fn mutants(
    src: &str,
    first_line: usize,
    lines: usize,
    cap: usize,
    seed: u64,
) -> (usize, Vec<Mutant>) {
    let toks = tokens(src);
    let in_fn = |t: &Token<'_>| t.line >= first_line && t.line < first_line + lines;
    let Some(body_start) = toks.iter().position(|t| in_fn(t) && t.text == "{") else {
        return (0, Vec::new());
    };
    // (operator, start, end, replacement, line, column)
    let mut edits: Vec<(&'static str, usize, usize, String, usize, usize)> = Vec::new();
    for (i, t) in toks.iter().enumerate().skip(body_start + 1) {
        if !in_fn(t) {
            break;
        }
        let end = t.start + t.text.len();
        let prev = i.checked_sub(1).and_then(|p| toks.get(p));
        match t.kind {
            Kind::Punct => {
                if let Some((op, to)) = swap(t.text).or_else(|| binary_swap(t.text, prev)) {
                    edits.push((op, t.start, end, to.to_owned(), t.line, t.column));
                }
            }
            Kind::Number => {
                if let Some(to) = bump(t.text) {
                    edits.push(("constant", t.start, end, to, t.line, t.column));
                }
            }
            Kind::Ident | Kind::Literal => {}
        }
        if let Some(last) = droppable(&toks, i)
            && let Some(l) = toks.get(last)
        {
            edits.push((
                "statement",
                t.start,
                l.start + 1,
                ";".to_owned(),
                t.line,
                t.column,
            ));
        }
    }
    let candidates = edits.len();
    if cap > 0 && edits.len() > cap {
        // A partial Fisher-Yates shuffle picks `cap` without favouring the
        // start of the function; the order of the text is restored after.
        let mut rng = Rng::new(seed, &format!("mutants@{first_line}"));
        for i in 0..cap {
            let j = i + usize::try_from(rng.below((edits.len() - i) as u64)).unwrap_or(0);
            edits.swap(i, j);
        }
        edits.truncate(cap);
        edits.sort_by_key(|e| e.1);
    }
    let out = edits
        .into_iter()
        .filter_map(|(operator, start, end, to, line, column)| {
            let before = src.get(start..end)?.to_owned();
            let source = format!("{}{to}{}", src.get(..start)?, src.get(end..)?);
            Some(Mutant {
                line,
                column,
                operator,
                before,
                after: to,
                source,
            })
        })
        .collect();
    (candidates, out)
}

#[cfg(test)]
mod tests {
    use super::*;

    const SRC: &str = "#include <a.h>\n#define N 10 < 3\nint g(int a) { return a < 1; }\n/* x < y */\nint f(int a, int b)\n{\n    // a > b\n    int n = 0;\n    char *s = \"a < b\";\n    if (a <= b && a != -3)\n        n += a + b;\n    n++;\n    g(n);\n    for (int i = 0; i < 0x10; i++)\n        n = n * 2;\n    return n;\n}\nint h(int a) { return a > 2; }\n";

    fn all() -> Vec<Mutant> {
        mutants(SRC, 5, 13, 0, 1).1
    }

    #[test]
    fn changes_stay_inside_the_function_and_outside_comments_and_strings() {
        let ms = all();
        assert!(!ms.is_empty());
        for m in &ms {
            assert!((6..=17).contains(&m.line), "{m:?}");
            assert!(m.line != 7 && m.line != 9, "{m:?}");
            // Exactly one place differs, and the other functions are intact.
            assert!(m.source.contains("int g(int a) { return a < 1; }"));
            assert!(m.source.contains("int h(int a) { return a > 2; }"));
            assert!(m.source.contains("\"a < b\""));
            assert_ne!(m.source, SRC);
        }
    }

    #[test]
    fn each_operator_produces_its_changes() {
        let ms = all();
        let has = |op: &str, before: &str, after: &str, line: usize| {
            ms.iter().any(|m| {
                m.operator == op && m.before == before && m.after == after && m.line == line
            })
        };
        assert!(has("comparison", "<=", "<", 10));
        assert!(has("comparison", "!=", "==", 10));
        assert!(has("logical", "&&", "||", 10));
        assert!(has("arithmetic", "+=", "-=", 11));
        assert!(has("arithmetic", "+", "-", 11));
        assert!(has("arithmetic", "++", "--", 12));
        assert!(has("constant", "0", "1", 8));
        assert!(has("constant", "0x10", "0x11", 14));
        assert!(has("statement", "n++;", ";", 12));
        assert!(has("statement", "g(n);", ";", 13));
        assert!(has("statement", "n += a + b;", ";", 11));
        // A unary minus is not a subtraction, and a declaration is not dropped.
        assert!(!ms.iter().any(|m| m.before == "-" && m.line == 10));
        assert!(!ms.iter().any(|m| m.operator == "statement" && m.line == 8));
        assert!(!ms.iter().any(|m| m.operator == "statement" && m.line == 16));
    }

    #[test]
    fn the_cap_limits_the_number_and_is_repeatable() {
        let (candidates, a) = mutants(SRC, 5, 13, 5, 1);
        let (_, b) = mutants(SRC, 5, 13, 5, 1);
        assert!(candidates > 5);
        assert_eq!(a.len(), 5);
        assert_eq!(a, b);
    }
}

//! C types in the IR, and the parser that reads them from clang's printed
//! type spellings.
//!
//! clang's JSON gives an expression's type only as text (`qualType`), so the
//! text is parsed here, with typedef names resolved through the typedef
//! declarations of the same translation unit.

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::target::Target;

#[derive(serde::Serialize, Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub(crate) struct Quals {
    pub(crate) is_const: bool,
    pub(crate) is_volatile: bool,
    pub(crate) is_restrict: bool,
}

impl Quals {
    fn union(self, o: Self) -> Self {
        Self {
            is_const: self.is_const || o.is_const,
            is_volatile: self.is_volatile || o.is_volatile,
            is_restrict: self.is_restrict || o.is_restrict,
        }
    }
}

#[derive(serde::Serialize, Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct QualType {
    pub(crate) ty: Type,
    pub(crate) quals: Quals,
}

impl QualType {
    pub(crate) const fn plain(ty: Type) -> Self {
        Self {
            ty,
            quals: Quals {
                is_const: false,
                is_volatile: false,
                is_restrict: false,
            },
        }
    }

    pub(crate) fn unsupported(spelling: &str, reason: impl Into<String>) -> Self {
        Self::plain(Type::Unsupported {
            spelling: spelling.to_owned(),
            reason: reason.into(),
        })
    }
}

#[derive(serde::Serialize, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum IntKind {
    Char,
    SChar,
    UChar,
    Short,
    UShort,
    Int,
    UInt,
    Long,
    ULong,
    LongLong,
    ULongLong,
    Int128,
    UInt128,
}

impl IntKind {
    pub(crate) const fn c_name(self) -> &'static str {
        match self {
            Self::Char => "char",
            Self::SChar => "signed char",
            Self::UChar => "unsigned char",
            Self::Short => "short",
            Self::UShort => "unsigned short",
            Self::Int => "int",
            Self::UInt => "unsigned int",
            Self::Long => "long",
            Self::ULong => "unsigned long",
            Self::LongLong => "long long",
            Self::ULongLong => "unsigned long long",
            Self::Int128 => "__int128",
            Self::UInt128 => "unsigned __int128",
        }
    }
}

/// An integer type with its width and signedness on the entry's target.
#[derive(serde::Serialize, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct IntType {
    pub(crate) kind: IntKind,
    pub(crate) bits: u32,
    pub(crate) signed: bool,
}

#[derive(serde::Serialize, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum FloatKind {
    Float,
    Double,
}

#[derive(serde::Serialize, Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum RecordKind {
    Struct,
    Union,
}

impl RecordKind {
    pub(crate) const fn keyword(self) -> &'static str {
        match self {
            Self::Struct => "struct",
            Self::Union => "union",
        }
    }
}

/// How a struct, union or enum is named.
#[derive(serde::Serialize, Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum TagName {
    /// `struct foo`.
    Tag(String),
    /// An anonymous tag given a name by a typedef, which clang then prints
    /// as `struct foo` although no tag `foo` exists.
    Typedef(String),
    /// An anonymous tag without a typedef, known by where it is declared.
    Anon(String),
}

impl fmt::Display for TagName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Tag(n) => f.write_str(n),
            Self::Typedef(n) => write!(f, "(typedef {n})"),
            Self::Anon(l) => write!(f, "(anonymous at {l})"),
        }
    }
}

#[derive(serde::Serialize, Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct FnType {
    pub(crate) ret: QualType,
    pub(crate) params: Vec<QualType>,
    pub(crate) variadic: bool,
    /// False for a K&R `()` declaration, which says nothing about parameters.
    pub(crate) prototyped: bool,
    pub(crate) noreturn: bool,
}

#[derive(serde::Serialize, Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Type {
    Void,
    Bool {
        bits: u32,
    },
    Int(IntType),
    Float {
        kind: FloatKind,
        bits: u32,
    },
    Pointer(Box<QualType>),
    Array {
        elem: Box<QualType>,
        len: Option<u64>,
    },
    Record {
        kind: RecordKind,
        name: TagName,
    },
    Enum(TagName),
    Function(Box<FnType>),
    Atomic(Box<QualType>),
    Unsupported {
        spelling: String,
        reason: String,
    },
}

impl fmt::Display for QualType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.quals.is_const {
            f.write_str("const ")?;
        }
        if self.quals.is_volatile {
            f.write_str("volatile ")?;
        }
        if self.quals.is_restrict {
            f.write_str("restrict ")?;
        }
        write!(f, "{}", self.ty)
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Void => f.write_str("void"),
            Self::Bool { bits } => write!(f, "_Bool:u{bits}"),
            Self::Int(i) => {
                write!(
                    f,
                    "{}:{}{}",
                    i.kind.c_name(),
                    if i.signed { 'i' } else { 'u' },
                    i.bits
                )
            }
            Self::Float {
                kind: FloatKind::Float,
                bits,
            } => write!(f, "float:f{bits}"),
            Self::Float {
                kind: FloatKind::Double,
                bits,
            } => write!(f, "double:f{bits}"),
            Self::Pointer(p) => write!(f, "ptr<{p}>"),
            Self::Array { elem, len: Some(n) } => write!(f, "array<{elem}; {n}>"),
            Self::Array { elem, len: None } => write!(f, "array<{elem}; ?>"),
            Self::Record { kind, name } => write!(f, "{} {name}", kind.keyword()),
            Self::Enum(name) => write!(f, "enum {name}"),
            Self::Function(ft) => {
                f.write_str("fn(")?;
                if ft.prototyped {
                    let mut first = true;
                    for p in &ft.params {
                        if !first {
                            f.write_str(", ")?;
                        }
                        first = false;
                        write!(f, "{p}")?;
                    }
                    if ft.variadic {
                        f.write_str(if first { "..." } else { ", ..." })?;
                    }
                } else {
                    f.write_str("?")?;
                }
                write!(f, ") -> {}", ft.ret)?;
                if ft.noreturn {
                    f.write_str(" noreturn")?;
                }
                Ok(())
            }
            Self::Atomic(t) => write!(f, "_Atomic<{t}>"),
            Self::Unsupported { spelling, reason } => {
                write!(f, "unsupported-type(`{spelling}`: {reason})")
            }
        }
    }
}

/// Prints a type as a C type name, for the probes clang evaluates. `None`
/// when the type cannot be named at file scope.
pub(crate) fn to_c(t: &QualType) -> Option<String> {
    to_c_decl(t, "")
}

fn quals_c(q: Quals) -> String {
    let mut s = String::new();
    if q.is_const {
        s.push_str("const ");
    }
    if q.is_volatile {
        s.push_str("volatile ");
    }
    if q.is_restrict {
        s.push_str("restrict ");
    }
    s
}

fn to_c_decl(t: &QualType, inner: &str) -> Option<String> {
    let q = quals_c(t.quals);
    let base = |name: &str| {
        Some(format!(
            "{q}{name}{}{inner}",
            if inner.is_empty() { "" } else { " " }
        ))
    };
    match &t.ty {
        Type::Void => base("void"),
        Type::Bool { .. } => base("_Bool"),
        Type::Int(i) => base(i.kind.c_name()),
        Type::Float {
            kind: FloatKind::Float,
            ..
        } => base("float"),
        Type::Float {
            kind: FloatKind::Double,
            ..
        } => base("double"),
        Type::Record {
            kind,
            name: TagName::Tag(n),
        } => base(&format!("{} {n}", kind.keyword())),
        Type::Record {
            name: TagName::Typedef(n),
            ..
        }
        | Type::Enum(TagName::Typedef(n)) => base(n),
        Type::Enum(TagName::Tag(n)) => base(&format!("enum {n}")),
        Type::Record {
            name: TagName::Anon(_),
            ..
        }
        | Type::Enum(TagName::Anon(_))
        | Type::Unsupported { .. } => None,
        Type::Atomic(a) => base(&format!("_Atomic({})", to_c(a)?)),
        Type::Pointer(p) => {
            let me = format!("*{}{inner}", quals_c(t.quals));
            let me = if matches!(p.ty, Type::Array { .. } | Type::Function(_)) {
                format!("({me})")
            } else {
                me
            };
            to_c_decl(p, &me)
        }
        Type::Array { elem, len } => {
            let n = len.map(|n| n.to_string()).unwrap_or_default();
            to_c_decl(elem, &format!("{inner}[{n}]"))
        }
        Type::Function(ft) => {
            let mut ps = Vec::new();
            for p in &ft.params {
                ps.push(to_c(p)?);
            }
            if ft.variadic {
                ps.push("...".into());
            }
            if ft.prototyped && ps.is_empty() {
                ps.push("void".into());
            }
            to_c_decl(&ft.ret, &format!("{inner}({})", ps.join(", ")))
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum TagKind {
    Struct,
    Union,
    Enum,
}

impl TagKind {
    pub(crate) fn from_keyword(k: &str) -> Option<Self> {
        match k {
            "struct" => Some(Self::Struct),
            "union" => Some(Self::Union),
            "enum" => Some(Self::Enum),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
enum TypedefEntry {
    One(String),
    Conflict(Vec<String>),
}

/// Resolves type spellings for one translation unit.
#[derive(Debug)]
pub(crate) struct TypeCtx {
    pub(crate) target: Target,
    typedefs: HashMap<String, TypedefEntry>,
    tags: HashSet<(TagKind, String)>,
    typedef_tags: HashSet<(TagKind, String)>,
    cache: HashMap<String, QualType>,
    resolving: HashSet<String>,
}

impl TypeCtx {
    pub(crate) fn new(target: Target) -> Self {
        Self {
            target,
            typedefs: HashMap::new(),
            tags: HashSet::new(),
            typedef_tags: HashSet::new(),
            cache: HashMap::new(),
            resolving: HashSet::new(),
        }
    }

    pub(crate) fn add_typedef(&mut self, name: &str, spelling: &str) {
        let entry = match self.typedefs.remove(name) {
            None => TypedefEntry::One(spelling.to_owned()),
            Some(TypedefEntry::One(s)) if s == spelling => TypedefEntry::One(s),
            Some(TypedefEntry::One(s)) => TypedefEntry::Conflict(vec![s, spelling.to_owned()]),
            Some(TypedefEntry::Conflict(mut v)) => {
                v.push(spelling.to_owned());
                TypedefEntry::Conflict(v)
            }
        };
        self.typedefs.insert(name.to_owned(), entry);
    }

    pub(crate) fn add_tag(&mut self, kind: TagKind, name: &str) {
        self.tags.insert((kind, name.to_owned()));
    }

    pub(crate) fn add_typedef_tag(&mut self, kind: TagKind, name: &str) {
        self.typedef_tags.insert((kind, name.to_owned()));
    }

    pub(crate) fn tag_name(&self, kind: TagKind, name: &str) -> Result<TagName, String> {
        let key = (kind, name.to_owned());
        match (self.tags.contains(&key), self.typedef_tags.contains(&key)) {
            (true, true) => Err(format!(
                "`{name}` names both a tag and a typedef'd anonymous tag"
            )),
            (false, true) => Ok(TagName::Typedef(name.to_owned())),
            _ => Ok(TagName::Tag(name.to_owned())),
        }
    }

    /// Parses a clang type spelling. Never fails: what cannot be read
    /// becomes [`Type::Unsupported`].
    pub(crate) fn parse(&mut self, spelling: &str) -> QualType {
        if let Some(t) = self.cache.get(spelling) {
            return t.clone();
        }
        let t = match tokenize(spelling) {
            Ok(toks) => {
                let mut p = Parser {
                    toks,
                    pos: 0,
                    ctx: self,
                };
                match p.full() {
                    Ok(t) => t,
                    Err(reason) => QualType::unsupported(spelling, reason),
                }
            }
            Err(reason) => QualType::unsupported(spelling, reason),
        };
        self.cache.insert(spelling.to_owned(), t.clone());
        t
    }

    fn typedef(&mut self, name: &str) -> Result<QualType, String> {
        let spelling = match self.typedefs.get(name) {
            None => return Err(format!("unknown type name `{name}`")),
            Some(TypedefEntry::Conflict(v)) => {
                return Err(format!(
                    "typedef `{name}` has conflicting definitions: {}",
                    v.join(" / ")
                ));
            }
            Some(TypedefEntry::One(s)) => s.clone(),
        };
        if !self.resolving.insert(name.to_owned()) {
            return Err(format!("typedef `{name}` refers to itself"));
        }
        let t = self.parse(&spelling);
        self.resolving.remove(name);
        Ok(t)
    }

    fn int(&self, kind: IntKind) -> Result<Type, String> {
        let t = &self.target;
        let (bits, signed) = match kind {
            IntKind::Char => (t.char_bits, t.char_signed),
            IntKind::SChar => (t.char_bits, true),
            IntKind::UChar => (t.char_bits, false),
            IntKind::Short => (t.short_bits, true),
            IntKind::UShort => (t.short_bits, false),
            IntKind::Int => (t.int_bits, true),
            IntKind::UInt => (t.int_bits, false),
            IntKind::Long => (t.long_bits, true),
            IntKind::ULong => (t.long_bits, false),
            IntKind::LongLong => (t.long_long_bits, true),
            IntKind::ULongLong => (t.long_long_bits, false),
            IntKind::Int128 | IntKind::UInt128 => (
                t.int128_bits.ok_or("__int128 on a target without it")?,
                kind == IntKind::Int128,
            ),
        };
        Ok(Type::Int(IntType { kind, bits, signed }))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Num(u64),
    Star,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Comma,
    Ellipsis,
    /// `(unnamed struct at FILE:LINE:COL)` and its variants, holding the location.
    Anon(String),
    /// The inside of `__attribute__((...))`.
    Attr(String),
}

/// Finds the `)` matching the `(` at byte `open`.
fn matching_paren(s: &str, open: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (i, c) in s.char_indices().skip_while(|(i, _)| *i < open) {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

fn tokenize(s: &str) -> Result<Vec<Tok>, String> {
    let mut toks = Vec::new();
    let mut i = 0;
    while let Some(c) = s.get(i..).and_then(|r| r.chars().next()) {
        let rest = s.get(i..).unwrap_or("");
        if c.is_whitespace() {
            i += c.len_utf8();
        } else if c.is_ascii_alphabetic() || c == '_' {
            let len = rest
                .find(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_'))
                .unwrap_or(rest.len());
            let word = rest.get(..len).unwrap_or("");
            i += len;
            if s.get(i..).is_some_and(|r| r.starts_with("::")) {
                // `struct outer::(anonymous at ...)`: the qualifier adds nothing
                // beyond the location that follows.
                i += 2;
            } else if word == "__attribute__" {
                let open = s
                    .get(i..)
                    .and_then(|r| r.find('('))
                    .map(|o| o + i)
                    .ok_or("bad attribute")?;
                let close = matching_paren(s, open).ok_or("unbalanced attribute")?;
                let body = s.get(open + 1..close).unwrap_or("");
                let body = body
                    .trim()
                    .trim_start_matches('(')
                    .trim_end_matches(')')
                    .trim();
                toks.push(Tok::Attr(body.to_owned()));
                i = close + 1;
            } else {
                toks.push(Tok::Ident(word.to_owned()));
            }
        } else if c.is_ascii_digit() {
            let len = rest
                .find(|ch: char| !ch.is_ascii_digit())
                .unwrap_or(rest.len());
            let n = rest
                .get(..len)
                .unwrap_or("")
                .parse::<u64>()
                .map_err(|e| e.to_string())?;
            toks.push(Tok::Num(n));
            i += len;
        } else if c == '(' && (rest.starts_with("(unnamed") || rest.starts_with("(anonymous")) {
            let close = matching_paren(s, i).ok_or("unbalanced anonymous tag")?;
            let body = s.get(i + 1..close).unwrap_or("");
            let loc = body
                .split_once(" at ")
                .map(|(_, l)| l)
                .ok_or("anonymous tag without location")?;
            toks.push(Tok::Anon(loc.to_owned()));
            i = close + 1;
        } else if rest.starts_with("...") {
            toks.push(Tok::Ellipsis);
            i += 3;
        } else {
            toks.push(match c {
                '*' => Tok::Star,
                '(' => Tok::LParen,
                ')' => Tok::RParen,
                '[' => Tok::LBracket,
                ']' => Tok::RBracket,
                ',' => Tok::Comma,
                other => return Err(format!("unexpected `{other}` in type")),
            });
            i += 1;
        }
    }
    Ok(toks)
}

#[derive(Debug)]
enum Suffix {
    Array(Option<u64>),
    Func {
        params: Vec<QualType>,
        variadic: bool,
        prototyped: bool,
        noreturn: bool,
    },
}

#[derive(Debug, Default)]
struct Declarator {
    ptrs: Vec<Quals>,
    inner: Option<Box<Self>>,
    suffixes: Vec<Suffix>,
}

struct Parser<'c> {
    toks: Vec<Tok>,
    pos: usize,
    ctx: &'c mut TypeCtx,
}

impl Parser<'_> {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }

    fn peek_at(&self, n: usize) -> Option<&Tok> {
        self.toks.get(self.pos + n)
    }

    fn bump(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.pos).cloned();
        self.pos += 1;
        t
    }

    fn expect(&mut self, t: &Tok) -> Result<(), String> {
        match self.bump() {
            Some(got) if got == *t => Ok(()),
            got => Err(format!("expected {t:?}, found {got:?}")),
        }
    }

    fn full(&mut self) -> Result<QualType, String> {
        let t = self.type_name()?;
        self.peek().map_or(Ok(t), |extra| {
            Err(format!("unexpected {extra:?} after type"))
        })
    }

    fn type_name(&mut self) -> Result<QualType, String> {
        let base = self.specifiers()?;
        let d = self.declarator()?;
        Ok(apply(base, d))
    }

    fn qualifier(word: &str, q: &mut Quals) -> bool {
        match word {
            "const" => q.is_const = true,
            "volatile" => q.is_volatile = true,
            "restrict" | "__restrict" | "__restrict__" => q.is_restrict = true,
            _ => return false,
        }
        true
    }

    fn specifiers(&mut self) -> Result<QualType, String> {
        let mut quals = Quals::default();
        let mut words: Vec<String> = Vec::new();
        let mut base: Option<QualType> = None;
        while let Some(Tok::Ident(w)) = self.peek().cloned() {
            if Self::qualifier(&w, &mut quals) {
                self.bump();
                continue;
            }
            match w.as_str() {
                "void" | "char" | "short" | "int" | "long" | "signed" | "unsigned" | "float"
                | "double" | "_Bool" | "__int128" => words.push(w.clone()),
                "bool" if !self.ctx.typedefs.contains_key("bool") => words.push("_Bool".into()),
                "_Complex" | "_Imaginary" | "_Float16" | "__fp16" | "__bf16" | "_Float128"
                | "__float128" | "_BitInt" | "typeof" | "__typeof__" | "__typeof"
                | "typeof_unqual" => {
                    return Err(format!("`{w}` types are not represented"));
                }
                "struct" | "union" | "enum" => {
                    self.bump();
                    base = Some(self.tag(&w)?);
                    continue;
                }
                "_Atomic" => {
                    self.bump();
                    self.expect(&Tok::LParen)?;
                    let inner = self.type_name()?;
                    self.expect(&Tok::RParen)?;
                    base = Some(QualType::plain(Type::Atomic(Box::new(inner))));
                    continue;
                }
                _ if base.is_none() && words.is_empty() => {
                    let mut t = self.ctx.typedef(&w)?;
                    if let Type::Unsupported { reason, .. } = &t.ty {
                        return Err(format!("typedef `{w}`: {reason}"));
                    }
                    if let Type::Array { elem, .. } = &mut t.ty {
                        // Qualifiers on an array typedef qualify its elements.
                        elem.quals = elem.quals.union(quals);
                        quals = Quals::default();
                    }
                    base = Some(t);
                }
                _ => break,
            }
            self.bump();
        }
        let mut t = match (base, words.is_empty()) {
            (Some(t), true) => t,
            (None, false) => QualType::plain(self.builtin(&words)?),
            (Some(_), false) => return Err("type specifiers mixed with a named type".into()),
            (None, true) => return Err("no type specifier".into()),
        };
        t.quals = t.quals.union(quals);
        Ok(t)
    }

    fn tag(&mut self, keyword: &str) -> Result<QualType, String> {
        let kind = TagKind::from_keyword(keyword).ok_or("not a tag keyword")?;
        let name = match self.bump() {
            Some(Tok::Ident(n)) => self.ctx.tag_name(kind, &n)?,
            Some(Tok::Anon(loc)) => TagName::Anon(loc),
            other => {
                return Err(format!(
                    "expected a tag name after `{keyword}`, found {other:?}"
                ));
            }
        };
        Ok(QualType::plain(match kind {
            TagKind::Struct => Type::Record {
                kind: RecordKind::Struct,
                name,
            },
            TagKind::Union => Type::Record {
                kind: RecordKind::Union,
                name,
            },
            TagKind::Enum => Type::Enum(name),
        }))
    }

    fn builtin(&self, words: &[String]) -> Result<Type, String> {
        let count = |w: &str| words.iter().filter(|x| *x == w).count();
        let (signed, unsigned, longs) = (count("signed"), count("unsigned"), count("long"));
        let has = |w: &str| count(w) > 0;
        let others = words.len() - signed - unsigned - longs - count("int");
        let spelled = words.join(" ");
        let err = || format!("unrecognised builtin type `{spelled}`");
        if signed + unsigned > 1 {
            return Err(err());
        }
        let u = unsigned == 1;
        let pick = |s: IntKind, uk: IntKind| if u { uk } else { s };
        let kind = match (others, longs) {
            (0, 0) => pick(IntKind::Int, IntKind::UInt),
            (0, 1) => pick(IntKind::Long, IntKind::ULong),
            (0, 2) => pick(IntKind::LongLong, IntKind::ULongLong),
            (1, 0) if has("short") => pick(IntKind::Short, IntKind::UShort),
            (1, 0) if has("__int128") => pick(IntKind::Int128, IntKind::UInt128),
            (1, 0) if has("char") && !has("int") => match (signed, unsigned) {
                (1, _) => IntKind::SChar,
                (_, 1) => IntKind::UChar,
                _ => IntKind::Char,
            },
            (1, _) if words.len() == 1 => {
                return match words.first().map(String::as_str) {
                    Some("void") => Ok(Type::Void),
                    Some("_Bool") => Ok(Type::Bool {
                        bits: self.ctx.target.bool_bits,
                    }),
                    Some("float") => Ok(Type::Float {
                        kind: FloatKind::Float,
                        bits: self.ctx.target.float_bits,
                    }),
                    Some("double") => Ok(Type::Float {
                        kind: FloatKind::Double,
                        bits: self.ctx.target.double_bits,
                    }),
                    _ => Err(err()),
                };
            }
            (1, 1) if has("double") && words.len() == 2 => {
                return Err("`long double` (x87 80-bit extended format) is not represented".into());
            }
            _ => return Err(err()),
        };
        self.ctx.int(kind)
    }

    fn declarator(&mut self) -> Result<Declarator, String> {
        let mut d = Declarator::default();
        while self.peek() == Some(&Tok::Star) {
            self.bump();
            let mut q = Quals::default();
            while let Some(Tok::Ident(w)) = self.peek().cloned() {
                if !Self::qualifier(&w, &mut q) {
                    break;
                }
                self.bump();
            }
            d.ptrs.push(q);
        }
        if self.peek() == Some(&Tok::LParen) && self.peek_at(1) == Some(&Tok::Star) {
            self.bump();
            d.inner = Some(Box::new(self.declarator()?));
            self.expect(&Tok::RParen)?;
        }
        loop {
            match self.peek().cloned() {
                Some(Tok::LBracket) => {
                    self.bump();
                    match self.bump() {
                        Some(Tok::RBracket) => d.suffixes.push(Suffix::Array(None)),
                        Some(Tok::Num(n)) => {
                            self.expect(&Tok::RBracket)?;
                            d.suffixes.push(Suffix::Array(Some(n)));
                        }
                        _ => return Err("variable length array type".into()),
                    }
                }
                Some(Tok::LParen) => {
                    let s = self.params()?;
                    d.suffixes.push(s);
                }
                Some(Tok::Attr(a)) => {
                    self.bump();
                    let is_noreturn = matches!(a.as_str(), "noreturn" | "__noreturn__");
                    match d.suffixes.last_mut() {
                        Some(Suffix::Func { noreturn, .. }) if is_noreturn => *noreturn = true,
                        _ => return Err(format!("type attribute `{a}`")),
                    }
                }
                _ => break,
            }
        }
        Ok(d)
    }

    fn params(&mut self) -> Result<Suffix, String> {
        self.expect(&Tok::LParen)?;
        if self.peek() == Some(&Tok::RParen) {
            self.bump();
            return Ok(Suffix::Func {
                params: vec![],
                variadic: false,
                prototyped: false,
                noreturn: false,
            });
        }
        let mut params = Vec::new();
        let mut variadic = false;
        loop {
            if self.peek() == Some(&Tok::Ellipsis) {
                self.bump();
                variadic = true;
            } else {
                params.push(self.type_name()?);
            }
            match self.bump() {
                Some(Tok::Comma) => {}
                Some(Tok::RParen) => break,
                other => {
                    return Err(format!(
                        "expected `,` or `)` in parameters, found {other:?}"
                    ));
                }
            }
        }
        if !variadic && params.len() == 1 && params.first() == Some(&QualType::plain(Type::Void)) {
            params.clear();
        }
        Ok(Suffix::Func {
            params,
            variadic,
            prototyped: true,
            noreturn: false,
        })
    }
}

fn apply(base: QualType, d: Declarator) -> QualType {
    let mut t = base;
    for q in d.ptrs {
        t = QualType {
            ty: Type::Pointer(Box::new(t)),
            quals: q,
        };
    }
    for s in d.suffixes.into_iter().rev() {
        t = QualType::plain(match s {
            Suffix::Array(len) => Type::Array {
                elem: Box::new(t),
                len,
            },
            Suffix::Func {
                params,
                variadic,
                prototyped,
                noreturn,
            } => Type::Function(Box::new(FnType {
                ret: t,
                params,
                variadic,
                prototyped,
                noreturn,
            })),
        });
    }
    match d.inner {
        Some(inner) => apply(t, *inner),
        None => t,
    }
}

/// Calls `f` on every type nested in `t`, `t` included.
pub(crate) fn walk(t: &QualType, f: &mut impl FnMut(&QualType)) {
    f(t);
    match &t.ty {
        Type::Pointer(p) | Type::Atomic(p) | Type::Array { elem: p, .. } => walk(p, f),
        Type::Function(ft) => {
            walk(&ft.ret, f);
            for p in &ft.params {
                walk(p, f);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    pub(crate) fn x86_64() -> Target {
        Target {
            char_bits: 8,
            char_signed: true,
            short_bits: 16,
            int_bits: 32,
            long_bits: 64,
            long_long_bits: 64,
            int128_bits: Some(128),
            bool_bits: 8,
            pointer_bits: 64,
            float_bits: 32,
            double_bits: 64,
        }
    }

    fn show(ctx: &mut TypeCtx, s: &str) -> String {
        ctx.parse(s).to_string()
    }

    #[test]
    fn parses_declarators() {
        let mut c = TypeCtx::new(x86_64());
        c.add_typedef("size_t", "unsigned long");
        c.add_typedef("va_list", "struct __va_list_tag[1]");
        c.add_tag(TagKind::Struct, "bstr");
        assert_eq!(show(&mut c, "unsigned char"), "unsigned char:u8");
        assert_eq!(show(&mut c, "char"), "char:i8");
        assert_eq!(show(&mut c, "long long"), "long long:i64");
        assert_eq!(
            show(&mut c, "const size_t *"),
            "ptr<const unsigned long:u64>"
        );
        assert_eq!(
            show(&mut c, "char *const[3]"),
            "array<const ptr<char:i8>; 3>"
        );
        assert_eq!(show(&mut c, "int (*)[4]"), "ptr<array<int:i32; 4>>");
        assert_eq!(
            show(&mut c, "struct bstr (*)(struct bstr, int, ...)"),
            "ptr<fn(struct bstr, int:i32, ...) -> struct bstr>"
        );
        assert_eq!(
            show(&mut c, "void (*(*)(int))(void)"),
            "ptr<fn(int:i32) -> ptr<fn() -> void>>"
        );
        assert_eq!(show(&mut c, "int ()"), "fn(?) -> int:i32");
        assert_eq!(
            show(&mut c, "void (*)(void) __attribute__((noreturn))"),
            "ptr<fn() -> void noreturn>"
        );
        assert_eq!(
            show(
                &mut c,
                "const union mpv_node::(unnamed at ../x/client.h:765:5) *"
            ),
            "ptr<const union (anonymous at ../x/client.h:765:5)>"
        );
        assert_eq!(show(&mut c, "va_list"), "array<struct __va_list_tag; 1>");
        assert_eq!(show(&mut c, "_Atomic(bool)"), "_Atomic<_Bool:u8>");
        assert!(matches!(c.parse("int[n]").ty, Type::Unsupported { .. }));
        assert!(matches!(
            c.parse("long double").ty,
            Type::Unsupported { .. }
        ));
        assert!(matches!(c.parse("mystery_t").ty, Type::Unsupported { .. }));
    }

    #[test]
    fn prints_c_type_names() {
        let mut c = TypeCtx::new(x86_64());
        for s in [
            "int (*)[4]",
            "char *const[3]",
            "void (*(*)(int))(void)",
            "const char *",
            "int",
        ] {
            let t = c.parse(s);
            let back = to_c(&t).unwrap();
            assert_eq!(c.parse(&back), t, "{s} -> {back}");
        }
    }
}

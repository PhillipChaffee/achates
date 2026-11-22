//! A readable, stable text form of the IR: one node per line, children
//! indented, every expression followed by its type.

use std::fmt::Write as _;

use crate::ir::{
    BinOp, Decl, Expr, ExprKind, Function, Linkage, LocalVar, LogicalOp, Origin, Stmt, Storage,
    TraitArg, TranslationUnit, TypeTrait, UnaryOp, Unsupported, VarRef,
};
use crate::scan;

#[derive(Debug, Default)]
struct Out {
    s: String,
}

impl Out {
    fn line(&mut self, depth: usize, text: &str) {
        for _ in 0..depth {
            self.s.push_str("  ");
        }
        self.s.push_str(text);
        self.s.push('\n');
    }

    fn labelled_stmt(&mut self, depth: usize, label: &str, s: &Stmt) {
        self.line(depth, &format!("{label}:"));
        self.stmt(depth + 1, s);
    }

    fn labelled_expr(&mut self, depth: usize, label: &str, e: &Expr) {
        self.line(depth, &format!("{label}:"));
        self.expr(depth + 1, e);
    }

    fn stmt(&mut self, d: usize, s: &Stmt) {
        match s {
            Stmt::Compound(v) => {
                self.line(d, "compound");
                for s in v {
                    self.stmt(d + 1, s);
                }
            }
            Stmt::Decl(ds) => {
                self.line(d, "decl");
                for x in ds {
                    match x {
                        Decl::Var(v) => self.local(d + 1, v),
                        Decl::Unsupported(u) => self.line(d + 1, &unsupported(u)),
                    }
                }
            }
            Stmt::Expr(e) => self.expr(d, e),
            Stmt::If { cond, then, els } => {
                self.line(d, "if");
                self.labelled_expr(d + 1, "cond", cond);
                self.labelled_stmt(d + 1, "then", then);
                if let Some(e) = els {
                    self.labelled_stmt(d + 1, "else", e);
                }
            }
            Stmt::While { cond, body } => {
                self.line(d, "while");
                self.labelled_expr(d + 1, "cond", cond);
                self.labelled_stmt(d + 1, "body", body);
            }
            Stmt::DoWhile { body, cond } => {
                self.line(d, "do-while");
                self.labelled_stmt(d + 1, "body", body);
                self.labelled_expr(d + 1, "cond", cond);
            }
            Stmt::For {
                init,
                cond,
                inc,
                body,
            } => {
                self.line(d, "for");
                match init {
                    Some(i) => self.labelled_stmt(d + 1, "init", i),
                    None => self.line(d + 1, "init: none"),
                }
                match cond {
                    Some(c) => self.labelled_expr(d + 1, "cond", c),
                    None => self.line(d + 1, "cond: none"),
                }
                match inc {
                    Some(i) => self.labelled_expr(d + 1, "inc", i),
                    None => self.line(d + 1, "inc: none"),
                }
                self.labelled_stmt(d + 1, "body", body);
            }
            Stmt::Switch { cond, body } => {
                self.line(d, "switch");
                self.labelled_expr(d + 1, "cond", cond);
                self.labelled_stmt(d + 1, "body", body);
            }
            Stmt::Case { expr, value, body } => {
                match value {
                    Some(v) => self.line(d, &format!("case value {v}")),
                    None => self.line(d, "case"),
                }
                self.labelled_expr(d + 1, "label", expr);
                self.labelled_stmt(d + 1, "then", body);
            }
            Stmt::Default { body } => {
                self.line(d, "default");
                self.labelled_stmt(d + 1, "then", body);
            }
            Stmt::Break => self.line(d, "break"),
            Stmt::Continue => self.line(d, "continue"),
            Stmt::Return(None) => self.line(d, "return"),
            Stmt::Return(Some(e)) => {
                self.line(d, "return");
                self.expr(d + 1, e);
            }
            Stmt::Goto(l) => self.line(d, &format!("goto {l}")),
            Stmt::Label { name, body } => {
                self.line(d, &format!("label {name}"));
                self.stmt(d + 1, body);
            }
            Stmt::Null => self.line(d, "null"),
            Stmt::Unsupported(u) => self.line(d, &unsupported(u)),
        }
    }

    fn local(&mut self, d: usize, v: &LocalVar) {
        let mut head = format!("local {}#{} : {}", v.name, v.id, v.ty);
        match v.storage {
            Storage::None => {}
            Storage::Static => head.push_str(" static"),
            Storage::Register => head.push_str(" register"),
            Storage::Extern => head.push_str(" extern"),
        }
        if !v.attrs.is_empty() {
            let _ = write!(head, " attrs({})", v.attrs.join(", "));
        }
        self.line(d, &head);
        if let Some(e) = &v.init {
            self.labelled_expr(d + 1, "init", e);
        }
    }

    fn expr(&mut self, d: usize, e: &Expr) {
        let cat = if e.lvalue { " lvalue" } else { "" };
        self.line(d, &format!("{} : {}{cat}", label(&e.kind), e.ty));
        match &e.kind {
            ExprKind::InitList { elems, filler, .. } => {
                if let Some(f) = filler {
                    self.labelled_expr(d + 1, "filler", f);
                }
                for x in elems {
                    self.expr(d + 1, x);
                }
            }
            ExprKind::TypeTrait {
                arg: TraitArg::Type(t),
                ..
            } => {
                self.line(d + 1, &format!("type {t}"));
            }
            ExprKind::CompoundAssign {
                compute_lhs,
                compute_result,
                lhs,
                rhs,
                ..
            } => {
                self.line(
                    d + 1,
                    &format!("computed-as {compute_lhs} -> {compute_result}"),
                );
                self.expr(d + 1, lhs);
                self.expr(d + 1, rhs);
            }
            _ => scan::children(e)
                .into_iter()
                .for_each(|c| self.expr(d + 1, c)),
        }
    }
}

fn unsupported(u: &Unsupported) -> String {
    let at = u
        .loc
        .as_ref()
        .map(|l| format!(" at {l}"))
        .unwrap_or_default();
    format!("UNSUPPORTED {}: {}{at}", u.clang_kind, u.reason)
}

const fn unary(op: UnaryOp) -> &'static str {
    match op {
        UnaryOp::Plus => "+",
        UnaryOp::Minus => "-",
        UnaryOp::BitNot => "~",
        UnaryOp::Not => "!",
        UnaryOp::Deref => "deref *",
        UnaryOp::AddrOf => "address-of &",
        UnaryOp::PreInc => "pre++",
        UnaryOp::PreDec => "pre--",
        UnaryOp::PostInc => "post++",
        UnaryOp::PostDec => "post--",
        UnaryOp::Extension => "__extension__",
    }
}

pub(crate) const fn binary(op: BinOp) -> &'static str {
    match op {
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
        BinOp::Lt => "<",
        BinOp::Gt => ">",
        BinOp::Le => "<=",
        BinOp::Ge => ">=",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::BitAnd => "&",
        BinOp::BitXor => "^",
        BinOp::BitOr => "|",
    }
}

fn escape(bytes: &[u8]) -> String {
    let mut s = String::from("\"");
    for b in bytes {
        match b {
            b'"' => s.push_str("\\\""),
            b'\\' => s.push_str("\\\\"),
            b'\n' => s.push_str("\\n"),
            b'\t' => s.push_str("\\t"),
            0x20..=0x7e => s.push(char::from(*b)),
            _ => {
                let _ = write!(s, "\\x{b:02x}");
            }
        }
    }
    s.push('"');
    s
}

fn var(v: &VarRef) -> String {
    match v {
        VarRef::Param { name, index } => format!("var param {name} (#{index})"),
        VarRef::Local { id, name } => format!("var local {name}#{id}"),
        VarRef::Global { name } => format!("var global {name}"),
    }
}

fn label(k: &ExprKind) -> String {
    match k {
        ExprKind::IntLit(n) => format!("int {n}"),
        ExprKind::FloatLit { text, bits } => format!("float {text} (bits {bits:#x})"),
        ExprKind::CharLit(c) => format!("char {c}"),
        ExprKind::StringLit(b) => format!("string {}", escape(b)),
        ExprKind::Var(v) => var(v),
        ExprKind::Func {
            name,
            builtin: false,
        } => format!("function {name}"),
        ExprKind::Func {
            name,
            builtin: true,
        } => format!("builtin-function {name}"),
        ExprKind::EnumConst { name, value } => format!("enum-constant {name} = {value}"),
        ExprKind::Unary { op, .. } => format!("unary {}", unary(*op)),
        ExprKind::Binary { op, .. } => format!("binary {}", binary(*op)),
        ExprKind::Logical {
            op: LogicalOp::And, ..
        } => "logical && (rhs only if lhs nonzero)".into(),
        ExprKind::Logical {
            op: LogicalOp::Or, ..
        } => "logical || (rhs only if lhs zero)".into(),
        ExprKind::Comma { .. } => "comma (lhs then rhs)".into(),
        ExprKind::Assign { .. } => "assign =".into(),
        ExprKind::CompoundAssign { op, .. } => format!("compound-assign {}=", binary(*op)),
        ExprKind::Cond { .. } => "conditional ?:".into(),
        ExprKind::Call {
            direct: Some(n), ..
        } => format!("call direct {n}"),
        ExprKind::Call { direct: None, .. } => "call indirect".into(),
        ExprKind::Member { field, arrow, .. } => {
            let f = if field.is_empty() {
                "<anonymous>"
            } else {
                field
            };
            format!("member {}{f}", if *arrow { "->" } else { "." })
        }
        ExprKind::Index { .. } => "index".into(),
        ExprKind::Cast {
            kind,
            explicit: false,
            ..
        } => format!("implicit-cast {kind:?}"),
        ExprKind::Cast {
            kind,
            explicit: true,
            ..
        } => format!("cast {kind:?}"),
        ExprKind::TypeTrait { trait_, value, .. } => {
            let t = match trait_ {
                TypeTrait::Size => "sizeof",
                TypeTrait::Align => "_Alignof",
                TypeTrait::PreferredAlign => "__alignof__",
            };
            format!("{t} = {value} (operand not evaluated)")
        }
        ExprKind::InitList {
            union_field: Some(f),
            ..
        } => format!("init-list union-member {f}"),
        ExprKind::InitList {
            union_field: None, ..
        } => "init-list".into(),
        ExprKind::CompoundLiteral(_) => "compound-literal".into(),
        ExprKind::ImplicitValueInit => "zero-init".into(),
        ExprKind::Predefined { name, .. } => format!("predefined {name}"),
        ExprKind::Atomic { op, .. } => format!("atomic {op}"),
        ExprKind::VaArg(_) => "va-arg".into(),
        ExprKind::Unsupported(u) => unsupported(u),
    }
}

/// The function's signature and body, without the function's own location,
/// to compare one header function across translation units.
pub(crate) fn fingerprint(f: &Function) -> String {
    let mut o = Out::default();
    let params: Vec<String> = f
        .params
        .iter()
        .map(|p| format!("{}: {}", p.name, p.ty))
        .collect();
    o.line(
        0,
        &format!(
            "{}({}) -> {} variadic {}",
            f.name,
            params.join(", "),
            f.ret,
            f.variadic
        ),
    );
    o.stmt(0, &f.body);
    o.s
}

pub(crate) fn function(f: &Function, tu: &TranslationUnit) -> String {
    let mut o = Out::default();
    let params: Vec<String> = f
        .params
        .iter()
        .map(|p| format!("{}: {}", p.name, p.ty))
        .collect();
    let mut params = params.join(", ");
    if f.variadic {
        params.push_str(if params.is_empty() { "..." } else { ", ..." });
    }
    let linkage = match f.linkage {
        Linkage::External => "external",
        Linkage::Internal => "internal",
    };
    o.line(0, &format!("function {}({params}) -> {}", f.name, f.ret));
    let origin = match f.origin {
        Origin::MainFile => "main file",
        Origin::ProjectHeader => "project header",
        Origin::SystemHeader => "system header",
    };
    let mut facts = vec![format!("linkage {linkage}"), format!("defined in {origin}")];
    if f.inline {
        facts.push("inline".into());
    }
    if f.noreturn {
        facts.push("noreturn".into());
    }
    if let Some(l) = &f.loc {
        facts.push(format!("at {l}"));
    }
    facts.push(format!("{} lines", f.lines));
    o.line(1, &facts.join(", "));
    if !f.attrs.is_empty() {
        o.line(1, &format!("attrs {}", f.attrs.join(", ")));
    }
    o.stmt(0, &f.body);
    used(&mut o, f, tu);
    let reached: Vec<&str> = scan::reaches(f, tu)
        .iter()
        .map(|h| h.name.as_str())
        .collect();
    if !reached.is_empty() {
        o.line(
            0,
            &format!("reaches header functions: {}", reached.join(", ")),
        );
    }
    o.s
}

fn used(o: &mut Out, f: &Function, tu: &TranslationUnit) {
    let mut records = std::collections::BTreeSet::new();
    let mut enums = std::collections::BTreeSet::new();
    for t in scan::types_of(f) {
        crate::convert::tags_in(t, &mut records, &mut enums);
    }
    for k in &records {
        let Some(r) = tu.records.get(k) else { continue };
        match &r.fields {
            None => o.line(
                0,
                &format!(
                    "{} {} (no definition in this unit)",
                    r.kind.keyword(),
                    r.name
                ),
            ),
            Some(fields) => {
                let attrs = if r.attrs.is_empty() {
                    String::new()
                } else {
                    format!(" attrs({})", r.attrs.join(", "))
                };
                o.line(0, &format!("{} {}{attrs}", r.kind.keyword(), r.name));
                for fl in fields {
                    let n = if fl.name.is_empty() {
                        "<anonymous>"
                    } else {
                        &fl.name
                    };
                    let bits = fl
                        .bit_width
                        .map(|b| format!(" : {b} bits"))
                        .unwrap_or_default();
                    o.line(1, &format!("field {n} : {}{bits}", fl.ty));
                }
            }
        }
    }
    for n in &enums {
        let Some(e) = tu.enums.get(n) else { continue };
        let u = match &e.underlying {
            Ok(t) => crate::types::Type::Int(*t).to_string(),
            Err(why) => format!("unknown ({why})"),
        };
        o.line(0, &format!("enum {n} : {u}"));
        for (c, v) in &e.constants {
            o.line(1, &format!("{c} = {v}"));
        }
    }
    for g in &f.globals {
        let Some(g) = tu.globals.get(g) else { continue };
        let storage = match g.storage {
            Storage::None => "",
            Storage::Static => " static",
            Storage::Extern => " extern",
            Storage::Register => " register",
        };
        let place = if g.in_main_file {
            ""
        } else {
            " (declared in a header)"
        };
        o.line(0, &format!("global {} : {}{storage}{place}", g.name, g.ty));
        if let Some(i) = &g.init {
            o.labelled_expr(1, "init", i);
        }
    }
}

#[derive(serde::Serialize)]
struct JsonDoc<'a> {
    file: &'a str,
    target: &'a crate::target::Target,
    function: &'a Function,
    records: Vec<&'a crate::ir::RecordDef>,
    enums: Vec<&'a crate::ir::EnumDef>,
    globals: Vec<&'a crate::ir::Global>,
    unsupported: Vec<Unsupported>,
}

/// The function's IR as JSON, with every record, enum and global it
/// reaches, for tools that consume the IR.
pub(crate) fn json(f: &Function, tu: &TranslationUnit) -> anyhow::Result<String> {
    let (records, enums) = scan::reachable(f, tu);
    let doc = JsonDoc {
        file: &tu.file,
        target: &tu.target,
        function: f,
        records,
        enums,
        globals: f.globals.iter().filter_map(|g| tu.globals.get(g)).collect(),
        unsupported: scan::unsupported_of(f, tu),
    };
    Ok(serde_json::to_string_pretty(&doc)? + "\n")
}

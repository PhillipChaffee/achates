//! Walks over a function's IR: the types it mentions and the constructs it
//! does not represent.

use std::collections::BTreeSet;

use crate::ir::{
    Decl, EnumDef, Expr, ExprKind, Function, RecordDef, Stmt, TraitArg, TranslationUnit,
    Unsupported,
};
use crate::types::{QualType, Type, walk};

#[derive(Debug, Default)]
struct Found<'a> {
    unsupported: Vec<&'a Unsupported>,
    types: Vec<&'a QualType>,
    builtins: BTreeSet<String>,
}

impl<'a> Found<'a> {
    fn stmt(&mut self, s: &'a Stmt) {
        match s {
            Stmt::Compound(v) => v.iter().for_each(|s| self.stmt(s)),
            Stmt::Decl(ds) => {
                for d in ds {
                    match d {
                        Decl::Var(v) => {
                            self.types.push(&v.ty);
                            if let Some(e) = &v.init {
                                self.expr(e);
                            }
                        }
                        Decl::Unsupported(u) => self.unsupported.push(u),
                    }
                }
            }
            Stmt::Expr(e) | Stmt::Return(Some(e)) => self.expr(e),
            Stmt::If { cond, then, els } => {
                self.expr(cond);
                self.stmt(then);
                if let Some(e) = els {
                    self.stmt(e);
                }
            }
            Stmt::While { cond, body }
            | Stmt::DoWhile { body, cond }
            | Stmt::Switch { cond, body } => {
                self.expr(cond);
                self.stmt(body);
            }
            Stmt::For {
                init,
                cond,
                inc,
                body,
            } => {
                if let Some(i) = init {
                    self.stmt(i);
                }
                for e in [cond, inc].into_iter().flatten() {
                    self.expr(e);
                }
                self.stmt(body);
            }
            Stmt::Case { expr, body, .. } => {
                self.expr(expr);
                self.stmt(body);
            }
            Stmt::Default { body } | Stmt::Label { body, .. } => self.stmt(body),
            Stmt::Unsupported(u) => self.unsupported.push(u),
            Stmt::Break | Stmt::Continue | Stmt::Return(None) | Stmt::Goto(_) | Stmt::Null => {}
        }
    }

    fn expr(&mut self, e: &'a Expr) {
        self.types.push(&e.ty);
        for c in children(e) {
            self.expr(c);
        }
        match &e.kind {
            ExprKind::CompoundAssign {
                compute_lhs,
                compute_result,
                ..
            } => {
                self.types.push(compute_lhs);
                self.types.push(compute_result);
            }
            ExprKind::TypeTrait {
                arg: TraitArg::Type(t),
                ..
            } => self.types.push(t),
            ExprKind::Unsupported(u) => self.unsupported.push(u),
            ExprKind::Func {
                name,
                builtin: true,
            } => {
                self.builtins.insert(name.clone());
            }
            ExprKind::Atomic { op, .. } => {
                self.builtins.insert(op.clone());
            }
            _ => {}
        }
    }
}

/// The sub-expressions of `e`, in evaluation-neutral source order.
pub(crate) fn children(e: &Expr) -> Vec<&Expr> {
    match &e.kind {
        ExprKind::Unary { operand: a, .. }
        | ExprKind::Cast { operand: a, .. }
        | ExprKind::CompoundLiteral(a)
        | ExprKind::Member { base: a, .. }
        | ExprKind::Predefined { value: a, .. }
        | ExprKind::TypeTrait {
            arg: TraitArg::Expr(a),
            ..
        } => vec![a],
        ExprKind::Binary { lhs, rhs, .. }
        | ExprKind::Logical { lhs, rhs, .. }
        | ExprKind::Comma { lhs, rhs }
        | ExprKind::Assign { lhs, rhs }
        | ExprKind::CompoundAssign { lhs, rhs, .. }
        | ExprKind::Index { lhs, rhs } => vec![lhs, rhs],
        ExprKind::Cond { cond, then, els } => vec![cond, then, els],
        ExprKind::Call { callee, args, .. } => std::iter::once(&**callee).chain(args).collect(),
        ExprKind::InitList { elems, filler, .. } => {
            filler.iter().map(|b| &**b).chain(elems).collect()
        }
        ExprKind::Atomic { operands, .. } => operands.iter().collect(),
        ExprKind::IntLit(_)
        | ExprKind::FloatLit { .. }
        | ExprKind::CharLit(_)
        | ExprKind::StringLit(_)
        | ExprKind::Var(_)
        | ExprKind::Func { .. }
        | ExprKind::EnumConst { .. }
        | ExprKind::TypeTrait {
            arg: TraitArg::Type(_),
            ..
        }
        | ExprKind::ImplicitValueInit
        | ExprKind::Unsupported(_) => vec![],
    }
}

fn found(f: &Function) -> Found<'_> {
    let mut x = Found::default();
    x.types.push(&f.ret);
    for p in &f.params {
        x.types.push(&p.ty);
    }
    x.stmt(&f.body);
    x
}

/// Every type written or computed in the function.
pub(crate) fn types_of(f: &Function) -> Vec<&QualType> {
    found(f).types
}

fn type_unsupported(t: &QualType, out: &mut Vec<Unsupported>) {
    walk(t, &mut |q| {
        if let Type::Unsupported { spelling, reason } = &q.ty {
            out.push(Unsupported {
                clang_kind: "type".into(),
                reason: format!("{reason} (`{spelling}`)"),
                loc: None,
            });
        }
    });
}

/// The records and enums `f` reaches, through the fields of records too.
pub(crate) fn reachable<'t>(
    f: &Function,
    tu: &'t TranslationUnit,
) -> (Vec<&'t RecordDef>, Vec<&'t EnumDef>) {
    let mut records = BTreeSet::new();
    let mut enums = BTreeSet::new();
    for t in types_of(f) {
        crate::convert::tags_in(t, &mut records, &mut enums);
    }
    for g in f.globals.iter().filter_map(|g| tu.globals.get(g)) {
        crate::convert::tags_in(&g.ty, &mut records, &mut enums);
    }
    let mut todo: Vec<_> = records.into_iter().collect();
    let mut done = BTreeSet::new();
    let mut out = Vec::new();
    while let Some(k) = todo.pop() {
        if !done.insert(k.clone()) {
            continue;
        }
        if let Some(r) = tu.records.get(&k) {
            for fld in r.fields.iter().flatten() {
                let mut more = BTreeSet::new();
                crate::convert::tags_in(&fld.ty, &mut more, &mut enums);
                todo.extend(more);
            }
            out.push(r);
        }
    }
    out.sort_by(|a, b| (a.kind, &a.name).cmp(&(b.kind, &b.name)));
    (out, enums.iter().filter_map(|e| tu.enums.get(e)).collect())
}

/// Everything in `f` that is not represented, including unrepresented
/// types of the fields of records it reaches. Empty means the function is
/// fully represented.
pub(crate) fn unsupported_of(f: &Function, tu: &TranslationUnit) -> Vec<Unsupported> {
    let x = found(f);
    let mut out: Vec<Unsupported> = x.unsupported.into_iter().cloned().collect();
    let mut seen = BTreeSet::new();
    for t in x.types {
        if seen.insert(t.to_string()) {
            type_unsupported(t, &mut out);
        }
    }
    let (records, enums) = reachable(f, tu);
    for fld in records.iter().filter_map(|r| r.fields.as_ref()).flatten() {
        type_unsupported(&fld.ty, &mut out);
    }
    for e in enums {
        if let Err(reason) = &e.underlying {
            out.push(Unsupported {
                clang_kind: "type".into(),
                reason: format!("integer type of `enum {}` unknown: {reason}", e.name),
                loc: None,
            });
        }
    }
    out
}

/// Compiler builtins and atomic operations `f` uses. They are represented,
/// but a back end needs a model of each.
pub(crate) fn builtins_of(f: &Function) -> BTreeSet<String> {
    found(f).builtins
}

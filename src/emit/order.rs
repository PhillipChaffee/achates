//! Two analyses of a function's IR that decide what the emitter may do:
//! which variables can be Lean values instead of memory, and whether an
//! expression's value depends on the order C leaves unspecified.

use std::collections::BTreeSet;

use crate::ir::{CastKind, Decl, Expr, ExprKind, Function, Stmt, Storage, UnaryOp, VarRef};
use crate::types::{QualType, Type};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum VarKey {
    Param(usize),
    Local(u32),
}

pub(crate) fn var_key(v: &VarRef) -> Option<VarKey> {
    match v {
        VarRef::Param { index, .. } => Some(VarKey::Param(*index)),
        VarRef::Local { id, .. } => Some(VarKey::Local(*id)),
        VarRef::Global { .. } => None,
    }
}

/// The variable an lvalue expression is a part of, when it names one
/// without going through a pointer.
pub(crate) fn root(e: &Expr) -> Option<VarKey> {
    match &e.kind {
        ExprKind::Var(v) => var_key(v),
        ExprKind::Member {
            base, arrow: false, ..
        } => root(base),
        ExprKind::Index { lhs, rhs } => decayed_root(lhs).or_else(|| decayed_root(rhs)),
        ExprKind::Unary {
            op: UnaryOp::Extension,
            operand,
        }
        | ExprKind::Cast {
            kind: CastKind::NoOp,
            operand,
            ..
        } => root(operand),
        _ => None,
    }
}

fn decayed_root(e: &Expr) -> Option<VarKey> {
    match &e.kind {
        ExprKind::Cast {
            kind: CastKind::ArrayToPointerDecay,
            operand,
            ..
        } => root(operand),
        _ => None,
    }
}

fn scalar_value(t: &QualType) -> bool {
    !t.quals.is_volatile
        && matches!(
            t.ty,
            Type::Bool { .. }
                | Type::Int(_)
                | Type::Float { .. }
                | Type::Pointer(_)
                | Type::Enum(_)
        )
}

#[derive(Debug, Default)]
pub(crate) struct Classes {
    /// Variables held as Lean values: scalars whose address is never taken
    /// and that are initialised where they are declared.
    pub(crate) temps: BTreeSet<VarKey>,
    /// Locals with static storage, by number.
    pub(crate) statics: BTreeSet<u32>,
    /// Every other local, with its type, in declaration order.
    pub(crate) memory: Vec<(u32, String, QualType)>,
}

#[derive(Default)]
struct Scan {
    addressed: BTreeSet<VarKey>,
    /// Local, type, initialised, static, declared in a block that has labels.
    locals: Vec<(u32, String, QualType, bool, bool, bool)>,
}

impl Scan {
    fn stmt(&mut self, s: &Stmt, labelled: bool) {
        match s {
            Stmt::Compound(v) => {
                let has = v.iter().any(|s| {
                    matches!(
                        s,
                        Stmt::Label { .. } | Stmt::Case { .. } | Stmt::Default { .. }
                    )
                });
                for s in v {
                    self.stmt(s, has);
                }
            }
            Stmt::Decl(ds) => {
                for d in ds {
                    if let Decl::Var(v) = d {
                        self.locals.push((
                            v.id,
                            v.name.clone(),
                            v.ty.clone(),
                            v.init.is_some(),
                            v.storage == Storage::Static,
                            labelled,
                        ));
                        if let Some(e) = &v.init {
                            self.expr(e);
                        }
                    }
                }
            }
            Stmt::Expr(e) | Stmt::Return(Some(e)) => self.expr(e),
            Stmt::If { cond, then, els } => {
                self.expr(cond);
                self.stmt(then, false);
                if let Some(e) = els {
                    self.stmt(e, false);
                }
            }
            Stmt::While { cond, body }
            | Stmt::DoWhile { body, cond }
            | Stmt::Switch { cond, body } => {
                self.expr(cond);
                self.stmt(body, false);
            }
            Stmt::For {
                init,
                cond,
                inc,
                body,
            } => {
                if let Some(i) = init {
                    self.stmt(i, false);
                }
                for e in [cond, inc].into_iter().flatten() {
                    self.expr(e);
                }
                self.stmt(body, false);
            }
            Stmt::Case { body, .. } | Stmt::Default { body } | Stmt::Label { body, .. } => {
                self.stmt(body, true);
            }
            _ => {}
        }
    }

    fn expr(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Unary {
                op: UnaryOp::AddrOf,
                operand,
            }
            | ExprKind::Cast {
                kind: CastKind::ArrayToPointerDecay,
                operand,
                ..
            } => self.addressed.extend(root(operand)),
            _ => {}
        }
        for c in crate::scan::children(e) {
            self.expr(c);
        }
    }
}

pub(crate) fn classify(f: &Function) -> Classes {
    let mut s = Scan::default();
    s.stmt(&f.body, false);
    let mut c = Classes::default();
    for (i, p) in f.params.iter().enumerate() {
        let k = VarKey::Param(i);
        if scalar_value(&p.ty) && !s.addressed.contains(&k) {
            c.temps.insert(k);
        }
    }
    for (id, name, ty, init, is_static, labelled) in s.locals {
        let k = VarKey::Local(id);
        if is_static {
            c.statics.insert(id);
        } else if scalar_value(&ty) && init && !labelled && !s.addressed.contains(&k) {
            c.temps.insert(k);
        } else {
            c.memory.push((id, name, ty));
        }
    }
    c
}

/// What evaluating an expression reads and writes.
#[derive(Debug, Default, Clone)]
pub(crate) struct Effects {
    temps_read: BTreeSet<VarKey>,
    temps_written: BTreeSet<VarKey>,
    mem_read: bool,
    mem_written: bool,
    /// Calls a function the selection takes as a parameter.
    calls_external: bool,
}

/// What a call may do to memory the caller can see.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CallEffect {
    ReadsOnly,
    Writes,
    /// A function taken as a parameter: nothing is known about it.
    External,
}

/// The outcome of checking one full expression.
#[derive(Debug, Default)]
pub(crate) struct Verdict {
    /// Two operands C does not sequence may interfere.
    pub(crate) refused: bool,
    /// The only possible interference is an external function writing
    /// memory that another operand reads.
    pub(crate) assumes_external_order: bool,
}

impl Effects {
    fn join(&mut self, o: &Self) {
        self.temps_read.extend(&o.temps_read);
        self.temps_written.extend(&o.temps_written);
        self.mem_read |= o.mem_read;
        self.mem_written |= o.mem_written;
        self.calls_external |= o.calls_external;
    }

    fn interferes(&self, o: &Self) -> bool {
        let one_way = |a: &Self, b: &Self| {
            a.temps_written
                .iter()
                .any(|v| b.temps_read.contains(v) || b.temps_written.contains(v))
                || (a.mem_written && (b.mem_read || b.mem_written || b.calls_external))
                || (a.calls_external && b.calls_external)
        };
        one_way(self, o) || one_way(o, self)
    }

    /// An external call beside an operand that only reads memory.
    fn external_beside_read(&self, o: &Self) -> bool {
        (self.calls_external && o.mem_read) || (o.calls_external && self.mem_read)
    }
}

/// What the analysis needs to know about the world outside the expression.
pub(crate) struct OrderCx<'a> {
    pub(crate) temps: &'a BTreeSet<VarKey>,
    /// Whether a call to the named function may write memory the caller can see.
    pub(crate) call_effect: &'a dyn Fn(Option<&str>) -> CallEffect,
}

impl OrderCx<'_> {
    fn temp_of(&self, lv: &Expr) -> Option<VarKey> {
        match &lv.kind {
            ExprKind::Var(v) => var_key(v).filter(|k| self.temps.contains(k)),
            ExprKind::Unary {
                op: UnaryOp::Extension,
                operand,
            } => self.temp_of(operand),
            _ => None,
        }
    }

    /// Effects of computing the address an lvalue designates.
    fn place(&self, lv: &Expr, bad: &mut Verdict) -> Effects {
        if self.temp_of(lv).is_some() || matches!(lv.kind, ExprKind::Var(_)) {
            return Effects::default();
        }
        self.eval(lv, bad)
    }

    fn write(&self, lv: &Expr, bad: &mut Verdict, read: bool) -> Effects {
        let mut e = self.place(lv, bad);
        if let Some(k) = self.temp_of(lv) {
            e.temps_written.insert(k);
            if read {
                e.temps_read.insert(k);
            }
        } else {
            e.mem_written = true;
            e.mem_read |= read;
        }
        e
    }

    fn unsequenced(parts: &[Effects], bad: &mut Verdict) -> Effects {
        let mut all = Effects::default();
        for (i, a) in parts.iter().enumerate() {
            for b in parts.iter().skip(i + 1) {
                bad.refused |= a.interferes(b);
                bad.assumes_external_order |= a.external_beside_read(b);
            }
            all.join(a);
        }
        all
    }

    fn assignment(&self, lhs: &Expr, rhs: &Expr, compound: bool, bad: &mut Verdict) -> Effects {
        let r = self.eval(rhs, bad);
        let target = self.temp_of(lhs);
        // `x = x++`: the assignment's own store is unsequenced with the
        // side effect in its operand.
        if target.is_some_and(|k| r.temps_written.contains(&k)) {
            bad.refused = true;
        }
        let mut all = Self::unsequenced(&[self.place(lhs, bad), r], bad);
        all.join(&self.write(lhs, &mut Verdict::default(), compound));
        all
    }

    /// Effects of evaluating `e`; records in `bad` when two operands that C
    /// does not sequence could interfere, so that the result may depend on
    /// the order the compiler chose (or the behaviour is undefined).
    pub(crate) fn eval(&self, e: &Expr, bad: &mut Verdict) -> Effects {
        match &e.kind {
            ExprKind::Cast {
                kind: CastKind::LValueToRValue,
                operand,
                ..
            } => {
                let mut x = self.place(operand, bad);
                match self.temp_of(operand) {
                    Some(k) => {
                        x.temps_read.insert(k);
                    }
                    None => x.mem_read = true,
                }
                x
            }
            ExprKind::Unary {
                op: UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec,
                operand,
            } => self.write(operand, bad, true),
            ExprKind::Unary {
                op: UnaryOp::AddrOf,
                operand,
            } => self.place(operand, bad),
            ExprKind::Assign { lhs, rhs } => self.assignment(lhs, rhs, false, bad),
            ExprKind::CompoundAssign { lhs, rhs, .. } => self.assignment(lhs, rhs, true, bad),
            ExprKind::Binary { lhs, rhs, .. } | ExprKind::Index { lhs, rhs } => {
                Self::unsequenced(&[self.eval(lhs, bad), self.eval(rhs, bad)], bad)
            }
            ExprKind::Call {
                callee,
                args,
                direct,
            } => {
                let mut parts: Vec<Effects> = args.iter().map(|a| self.eval(a, bad)).collect();
                if direct.is_none() {
                    parts.push(self.eval(callee, bad));
                }
                let mut all = Self::unsequenced(&parts, bad);
                all.mem_read = true;
                match (self.call_effect)(direct.as_deref()) {
                    CallEffect::ReadsOnly => {}
                    CallEffect::Writes => all.mem_written = true,
                    CallEffect::External => all.calls_external = true,
                }
                all
            }
            ExprKind::InitList { elems, .. } => {
                let parts: Vec<Effects> = elems.iter().map(|a| self.eval(a, bad)).collect();
                Self::unsequenced(&parts, bad)
            }
            ExprKind::Atomic { operands, .. } => {
                let mut all = Effects::default();
                for o in operands {
                    all.join(&self.eval(o, bad));
                }
                all.mem_read = true;
                all.mem_written = true;
                all
            }
            ExprKind::TypeTrait { .. } => Effects::default(),
            _ => {
                // Sequenced operands (`&&`, `||`, `?:`, comma) and
                // single-operand nodes: effects accumulate in order.
                let mut all = Effects::default();
                for c in crate::scan::children(e) {
                    all.join(&self.eval(c, bad));
                }
                all
            }
        }
    }
}

/// Whether `f` may write memory its caller can observe: a store through a
/// pointer or to a global, an atomic store, or a call that may.
pub(crate) fn writes_memory(f: &Function, call_writes: &dyn Fn(Option<&str>) -> bool) -> bool {
    fn expr(e: &Expr, cw: &dyn Fn(Option<&str>) -> bool) -> bool {
        let here = match &e.kind {
            ExprKind::Assign { lhs, .. } | ExprKind::CompoundAssign { lhs, .. } => {
                root(lhs).is_none()
            }
            ExprKind::Unary {
                op: UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec,
                operand,
            } => root(operand).is_none(),
            ExprKind::Call { direct, .. } => cw(direct.as_deref()),
            ExprKind::Atomic { .. } => true,
            _ => false,
        };
        here || crate::scan::children(e).into_iter().any(|c| expr(c, cw))
    }
    fn stmt(s: &Stmt, cw: &dyn Fn(Option<&str>) -> bool) -> bool {
        match s {
            Stmt::Compound(v) => v.iter().any(|s| stmt(s, cw)),
            Stmt::Decl(ds) => ds.iter().any(|d| match d {
                Decl::Var(v) => {
                    v.storage == Storage::Static || v.init.as_ref().is_some_and(|e| expr(e, cw))
                }
                Decl::Unsupported(_) => true,
            }),
            Stmt::Expr(e) | Stmt::Return(Some(e)) => expr(e, cw),
            Stmt::If { cond, then, els } => {
                expr(cond, cw) || stmt(then, cw) || els.as_ref().is_some_and(|e| stmt(e, cw))
            }
            Stmt::While { cond, body }
            | Stmt::DoWhile { body, cond }
            | Stmt::Switch { cond, body } => expr(cond, cw) || stmt(body, cw),
            Stmt::For {
                init,
                cond,
                inc,
                body,
            } => {
                init.as_ref().is_some_and(|s| stmt(s, cw))
                    || [cond, inc].into_iter().flatten().any(|e| expr(e, cw))
                    || stmt(body, cw)
            }
            Stmt::Case { body, .. } | Stmt::Default { body } | Stmt::Label { body, .. } => {
                stmt(body, cw)
            }
            Stmt::Unsupported(_) => true,
            _ => false,
        }
    }
    stmt(&f.body, call_writes)
}

/// Calls `f` on every expression of the statement, at every depth.
pub(crate) fn for_each_expr(s: &Stmt, f: &mut dyn FnMut(&Expr)) {
    fn deep(e: &Expr, f: &mut dyn FnMut(&Expr)) {
        f(e);
        for c in crate::scan::children(e) {
            deep(c, f);
        }
    }
    match s {
        Stmt::Compound(v) => v.iter().for_each(|s| for_each_expr(s, f)),
        Stmt::Decl(ds) => {
            for d in ds {
                if let Decl::Var(v) = d
                    && let Some(e) = &v.init
                {
                    deep(e, f);
                }
            }
        }
        Stmt::Expr(e) | Stmt::Return(Some(e)) => deep(e, f),
        Stmt::If { cond, then, els } => {
            deep(cond, f);
            for_each_expr(then, f);
            if let Some(e) = els {
                for_each_expr(e, f);
            }
        }
        Stmt::While { cond, body } | Stmt::DoWhile { body, cond } | Stmt::Switch { cond, body } => {
            deep(cond, f);
            for_each_expr(body, f);
        }
        Stmt::For {
            init,
            cond,
            inc,
            body,
        } => {
            if let Some(i) = init {
                for_each_expr(i, f);
            }
            for e in [cond, inc].into_iter().flatten() {
                deep(e, f);
            }
            for_each_expr(body, f);
        }
        Stmt::Case { expr, body, .. } => {
            deep(expr, f);
            for_each_expr(body, f);
        }
        Stmt::Default { body } | Stmt::Label { body, .. } => for_each_expr(body, f),
        _ => {}
    }
}

/// The functions `f` calls by name.
pub(crate) fn direct_calls(f: &Function) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for_each_expr(&f.body, &mut |e| {
        if let ExprKind::Call {
            direct: Some(name), ..
        } = &e.kind
        {
            out.insert(name.clone());
        }
    });
    out
}

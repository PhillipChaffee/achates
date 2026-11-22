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

/// Bytes `start..end` of the object a pointer held in a Lean value points
/// to. Two such locations with the same pointer and disjoint ranges are
/// different memory, whatever the pointer points to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Field {
    base: VarKey,
    start: u64,
    end: u64,
}

/// A set of memory locations: everything, or some fields.
#[derive(Debug, Default, Clone)]
pub(crate) struct Locs {
    any: bool,
    fields: Vec<Field>,
}

impl Locs {
    fn is_empty(&self) -> bool {
        !self.any && self.fields.is_empty()
    }

    fn add(&mut self, f: Option<Field>) {
        match f {
            Some(f) => self.fields.push(f),
            None => self.any = true,
        }
    }

    fn join(&mut self, o: &Self) {
        self.any |= o.any;
        self.fields.extend(&o.fields);
    }

    fn overlaps(&self, o: &Self) -> bool {
        if self.is_empty() || o.is_empty() {
            return false;
        }
        self.any
            || o.any
            || self.fields.iter().any(|a| {
                // Through two different pointers, any two locations may be
                // the same memory.
                o.fields
                    .iter()
                    .any(|b| a.base != b.base || (a.start < b.end && b.start < a.end))
            })
    }
}

/// What evaluating an expression reads and writes.
#[derive(Debug, Default, Clone)]
pub(crate) struct Effects {
    temps_read: BTreeSet<VarKey>,
    temps_written: BTreeSet<VarKey>,
    reads: Locs,
    /// Memory that existed before the expression and may be written.
    writes: Locs,
    /// Creates objects that outlive the expression (heap allocations).
    allocates: bool,
    /// Calls a function the selection takes as a parameter.
    calls_external: bool,
    /// Relies on an external function writing no memory (`EXT_READS`).
    relies: bool,
}

/// What a call may do to memory that existed before it: the summary of a
/// function's body, of a model, or of every function a pointer may call.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct Summary {
    /// May write memory that existed before the call. Its own local
    /// variables do not count: they are created by the call and gone when
    /// it returns.
    pub(crate) writes: bool,
    /// May create objects that outlive the call.
    pub(crate) allocates: bool,
    /// Writes no memory only because an external function's specification
    /// says it writes none (`EXT_READS`).
    pub(crate) relies: bool,
}

impl Summary {
    pub(crate) const WRITES: Self = Self {
        writes: true,
        allocates: true,
        relies: false,
    };

    #[must_use]
    pub(crate) const fn join(self, o: Self) -> Self {
        Self {
            writes: self.writes || o.writes,
            allocates: self.allocates || o.allocates,
            relies: self.relies || o.relies,
        }
    }
}

/// What a call may do to memory the caller can see.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CallEffect {
    Known(Summary),
    /// A function taken as a parameter: nothing is known about it.
    External,
}

/// What accepting an order of two operands rests on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Assume {
    /// The only possible interference is an external function writing
    /// memory that another operand reads.
    ExternalOrder,
    /// Two operands both create objects, so the two orders number the new
    /// blocks differently.
    BlockNumbering,
    /// An operand writes no memory only by an external's specification.
    ExternalReads,
}

/// The outcome of checking one full expression.
#[derive(Debug, Default)]
pub(crate) struct Verdict {
    /// Two operands C does not sequence may interfere.
    pub(crate) refused: bool,
    pub(crate) assumes: BTreeSet<Assume>,
}

/// Offset and size of a member of a record type, when known.
pub(crate) type MemberRange<'a> = &'a dyn Fn(&QualType, &str) -> Option<(u64, u64)>;

impl Effects {
    fn join(&mut self, o: &Self) {
        self.temps_read.extend(&o.temps_read);
        self.temps_written.extend(&o.temps_written);
        self.reads.join(&o.reads);
        self.writes.join(&o.writes);
        self.allocates |= o.allocates;
        self.calls_external |= o.calls_external;
        self.relies |= o.relies;
    }

    fn touches_memory(&self) -> bool {
        !self.reads.is_empty() || !self.writes.is_empty() || self.allocates || self.calls_external
    }

    fn interferes(&self, o: &Self) -> bool {
        let one_way = |a: &Self, b: &Self| {
            a.temps_written
                .iter()
                .any(|v| b.temps_read.contains(v) || b.temps_written.contains(v))
                || a.writes.overlaps(&b.reads)
                || a.writes.overlaps(&b.writes)
                || (!a.writes.is_empty() && b.calls_external)
                || (a.calls_external && b.calls_external)
        };
        one_way(self, o) || one_way(o, self)
    }

    /// An external call beside an operand that only reads memory.
    fn external_beside_read(&self, o: &Self) -> bool {
        (self.calls_external && !o.reads.is_empty()) || (o.calls_external && !self.reads.is_empty())
    }

    /// Both operands may create objects.
    fn both_allocate(&self, o: &Self) -> bool {
        (self.allocates || self.calls_external) && (o.allocates || o.calls_external)
    }
}

/// What the analysis needs to know about the world outside the expression.
pub(crate) struct OrderCx<'a> {
    pub(crate) temps: &'a BTreeSet<VarKey>,
    /// What a call may do, given the call expression.
    pub(crate) call_effect: &'a dyn Fn(&Expr) -> CallEffect,
    /// Offset and size of a member of a record type.
    pub(crate) member: MemberRange<'a>,
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

    /// The pointer value held in a Lean variable that `e` reads, through
    /// casts that keep the value.
    fn pointer_temp(&self, e: &Expr) -> Option<VarKey> {
        match &e.kind {
            ExprKind::Cast {
                kind: CastKind::NoOp | CastKind::BitCast,
                operand,
                ..
            } => self.pointer_temp(operand),
            ExprKind::Cast {
                kind: CastKind::LValueToRValue,
                operand,
                ..
            } => self.temp_of(operand),
            _ => None,
        }
    }

    /// The location an lvalue designates, when it is a member reached from
    /// a pointer held in a Lean variable: `p->a`, `p->a.b`.
    fn field(&self, lv: &Expr) -> Option<Field> {
        let ExprKind::Member { base, field, arrow } = &lv.kind else {
            return None;
        };
        let (start, record) = if *arrow {
            let Type::Pointer(record) = &base.ty.ty else {
                return None;
            };
            let k = self.pointer_temp(base)?;
            (
                Field {
                    base: k,
                    start: 0,
                    end: 0,
                },
                (**record).clone(),
            )
        } else {
            (self.field(base)?, base.ty.clone())
        };
        let (off, size) = (self.member)(&record, field)?;
        let first = start.start.checked_add(off)?;
        Some(Field {
            base: start.base,
            start: first,
            end: first.checked_add(size)?,
        })
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
            let f = self.field(lv);
            e.writes.add(f);
            if read {
                e.reads.add(f);
            }
        }
        e
    }

    fn unsequenced(parts: &[Effects], bad: &mut Verdict) -> Effects {
        let mut all = Effects::default();
        for (i, a) in parts.iter().enumerate() {
            for b in parts.iter().skip(i + 1) {
                if a.interferes(b) {
                    bad.refused = true;
                    continue;
                }
                if a.external_beside_read(b) {
                    bad.assumes.insert(Assume::ExternalOrder);
                }
                if a.both_allocate(b) {
                    bad.assumes.insert(Assume::BlockNumbering);
                }
                if (a.relies && b.touches_memory()) || (b.relies && a.touches_memory()) {
                    bad.assumes.insert(Assume::ExternalReads);
                }
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
                    None => x.reads.add(self.field(operand)),
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
                all.reads.any = true;
                match (self.call_effect)(e) {
                    CallEffect::Known(s) => {
                        if s.writes {
                            all.writes.any = true;
                        }
                        all.allocates |= s.allocates;
                        all.relies |= s.relies;
                    }
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
                all.reads.any = true;
                all.writes.any = true;
                all
            }
            ExprKind::VaArg(list) => {
                // Reads the list's position and advances it.
                let mut all = self.eval(list, bad);
                all.reads.any = true;
                all.writes.any = true;
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

/// What `f` may do to memory its caller can observe: stores through a
/// pointer or to a global, atomic stores, and what the calls it makes may
/// do. `call` gives the summary of one call expression.
pub(crate) fn summary(f: &Function, call: &dyn Fn(&Expr) -> Summary) -> Summary {
    let mut out = Summary::default();
    let mut expr = |e: &Expr| {
        let here = match &e.kind {
            ExprKind::Assign { lhs, .. } | ExprKind::CompoundAssign { lhs, .. } => {
                root(lhs).is_none()
            }
            ExprKind::Unary {
                op: UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec,
                operand,
            } => root(operand).is_none(),
            // The variadic macros write only the state of the list they are
            // given, which is the function's own when the list is a local.
            ExprKind::Call {
                direct: Some(name),
                args,
                ..
            } if matches!(
                name.as_str(),
                "__builtin_va_start" | "__builtin_va_end" | "__builtin_va_copy"
            ) =>
            {
                args.first().is_none_or(|a| decayed_root(a).is_none())
            }
            ExprKind::Call { .. } => {
                out = out.join(call(e));
                false
            }
            ExprKind::VaArg(list) => decayed_root(list).is_none(),
            ExprKind::Atomic { .. } | ExprKind::Unsupported(_) => true,
            _ => false,
        };
        out.writes |= here;
    };
    for_each_expr(&f.body, &mut expr);
    // A static local keeps its value across calls: memory the next call sees.
    let mut statics = false;
    for_each_decl(&f.body, &mut |v| statics |= v.storage == Storage::Static);
    // So does anything the IR does not represent.
    out.writes |= statics || unrepresented(&f.body);
    if out.writes {
        out.allocates = true;
    }
    out
}

fn unrepresented(s: &Stmt) -> bool {
    match s {
        Stmt::Unsupported(_) => true,
        Stmt::Compound(v) => v.iter().any(unrepresented),
        Stmt::Decl(ds) => ds.iter().any(|d| matches!(d, Decl::Unsupported(_))),
        Stmt::If { then, els, .. } => {
            unrepresented(then) || els.as_deref().is_some_and(unrepresented)
        }
        Stmt::While { body, .. }
        | Stmt::DoWhile { body, .. }
        | Stmt::Switch { body, .. }
        | Stmt::Case { body, .. }
        | Stmt::Default { body }
        | Stmt::Label { body, .. } => unrepresented(body),
        Stmt::For { init, body, .. } => {
            init.as_deref().is_some_and(unrepresented) || unrepresented(body)
        }
        _ => false,
    }
}

/// Calls `f` on every local variable the statement declares.
fn for_each_decl(s: &Stmt, f: &mut dyn FnMut(&crate::ir::LocalVar)) {
    match s {
        Stmt::Compound(v) => v.iter().for_each(|s| for_each_decl(s, f)),
        Stmt::Decl(ds) => {
            for d in ds {
                if let Decl::Var(v) = d {
                    f(v);
                }
            }
        }
        Stmt::If { then, els, .. } => {
            for_each_decl(then, f);
            if let Some(e) = els {
                for_each_decl(e, f);
            }
        }
        Stmt::While { body, .. }
        | Stmt::DoWhile { body, .. }
        | Stmt::Switch { body, .. }
        | Stmt::Case { body, .. }
        | Stmt::Default { body }
        | Stmt::Label { body, .. } => for_each_decl(body, f),
        Stmt::For { init, body, .. } => {
            if let Some(i) = init {
                for_each_decl(i, f);
            }
            for_each_decl(body, f);
        }
        _ => {}
    }
}

/// Every function whose address is taken in `f`, by C name, with the
/// number of parameters its type has: the functions a call through a
/// pointer may reach.
pub(crate) fn addresses_taken(e: &Expr, out: &mut BTreeSet<(String, usize)>) {
    match &e.kind {
        ExprKind::Func {
            name,
            builtin: false,
        } => {
            if let Type::Function(ft) = &e.ty.ty {
                out.insert((name.clone(), ft.params.len()));
            }
        }
        ExprKind::Call {
            args,
            direct: Some(_),
            ..
        } => {
            for a in args {
                addresses_taken(a, out);
            }
        }
        _ => {
            for c in crate::scan::children(e) {
                addresses_taken(c, out);
            }
        }
    }
}

/// The number of parameters of the function a call expression calls.
pub(crate) fn call_arity(callee: &Expr) -> Option<usize> {
    match &callee.ty.ty {
        Type::Pointer(p) => match &p.ty {
            Type::Function(ft) => Some(ft.params.len()),
            _ => None,
        },
        _ => None,
    }
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

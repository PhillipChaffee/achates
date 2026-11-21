//! Sizes, alignments and member offsets, all asked of clang: the emitter
//! computes no layout of its own beyond multiplying an element size by an
//! array length.

use std::collections::BTreeMap;

use anyhow::{Result, bail};

use crate::compdb::{ClangArgs, Entry};
use crate::ir::{RecordDef, TranslationUnit};
use crate::probe;
use crate::types::{QualType, RecordKind, TagName, Type, to_c};

pub(crate) type RecordKey = (RecordKind, TagName);

#[derive(Debug, Clone, Default)]
pub(crate) struct RecordLayout {
    pub(crate) size: Option<u64>,
    pub(crate) align: Option<u64>,
    /// Offset of each field within the record, in declaration order; `Err`
    /// says why clang could not be asked (a bit-field, for example).
    pub(crate) offsets: Vec<Result<u64, String>>,
}

#[derive(Debug, Default)]
pub(crate) struct Layouts {
    pub(crate) records: BTreeMap<RecordKey, RecordLayout>,
    /// The integer type clang chose for each enum.
    pub(crate) enums: BTreeMap<TagName, crate::types::IntType>,
}

/// The questions about one record, as indices into the list sent to clang.
struct Plan {
    key: RecordKey,
    size: Option<usize>,
    align: Option<usize>,
    fields: Vec<FieldPlan>,
}

struct FieldPlan {
    /// Absent for an anonymous member, which no designator can name.
    offset: Option<usize>,
    nested: Option<Plan>,
}

fn anon_record(t: &QualType) -> Option<RecordKey> {
    match &t.ty {
        Type::Record { kind, name } if matches!(name, TagName::Anon(_)) => {
            Some((*kind, name.clone()))
        }
        _ => None,
    }
}

struct Planner<'t> {
    tu: &'t TranslationUnit,
    questions: Vec<String>,
}

impl Planner<'_> {
    fn ask(&mut self, q: String) -> usize {
        self.questions.push(q);
        self.questions.len() - 1
    }

    /// `base` is a named record type; `prefix` is the designator path from
    /// it to the record being planned, empty or ending in a dot.
    fn plan(&mut self, def: &RecordDef, base: &str, prefix: &str, depth: usize) -> Plan {
        let key = (def.kind, def.name.clone());
        let (size, align) = if prefix.is_empty() {
            (
                Some(self.ask(format!("sizeof({base})"))),
                Some(self.ask(format!("_Alignof({base})"))),
            )
        } else if let Some(path) = prefix.strip_suffix('.') {
            let e = format!("(({base} *)0)->{path}");
            (
                Some(self.ask(format!("sizeof({e})"))),
                Some(self.ask(format!("_Alignof(__typeof__({e}))"))),
            )
        } else {
            (None, None)
        };
        let mut fields = Vec::new();
        for f in def.fields.iter().flatten() {
            let path = format!("{prefix}{}", f.name);
            let offset = (!f.name.is_empty() && f.bit_width.is_none())
                .then(|| self.ask(format!("__builtin_offsetof({base}, {path})")));
            let nested = anon_record(&f.ty)
                .filter(|_| depth < 8)
                .and_then(|k| self.tu.records.get(&k))
                .map(|d| {
                    let p = if f.name.is_empty() {
                        prefix.to_owned()
                    } else {
                        format!("{path}.")
                    };
                    self.plan(d, base, &p, depth + 1)
                });
            fields.push(FieldPlan { offset, nested });
        }
        Plan {
            key,
            size,
            align,
            fields,
        }
    }
}

type Answers = [Result<u64, String>];

fn answer(a: &Answers, i: Option<usize>) -> Result<u64, String> {
    i.and_then(|i| a.get(i))
        .cloned()
        .unwrap_or_else(|| Err("clang cannot be asked about an unnamed member".into()))
}

/// The offset, from the named record, of the first member that has a name:
/// where an anonymous member starts, since a struct's first member and
/// every member of a union sit at offset zero of it.
fn first_named(p: &Plan, a: &Answers) -> Result<u64, String> {
    let f = p.fields.first().ok_or("record without members")?;
    match (&f.offset, &f.nested) {
        (Some(_), _) => answer(a, f.offset),
        (None, Some(n)) => first_named(n, a),
        (None, None) => Err("member whose offset clang cannot be asked".into()),
    }
}

fn resolve(p: &Plan, base: u64, a: &Answers, out: &mut BTreeMap<RecordKey, RecordLayout>) {
    let mut offsets = Vec::new();
    for f in &p.fields {
        let abs = match (&f.offset, &f.nested) {
            (Some(_), _) => answer(a, f.offset),
            (None, Some(n)) => first_named(n, a),
            (None, None) => Err("bit-field or unnamed member".into()),
        };
        if let (Ok(abs), Some(n)) = (&abs, &f.nested) {
            resolve(n, *abs, a, out);
        }
        offsets.push(abs.and_then(|x| {
            x.checked_sub(base)
                .ok_or_else(|| "member before its record".to_owned())
        }));
    }
    out.entry(p.key.clone()).or_insert_with(|| RecordLayout {
        size: answer(a, p.size).ok(),
        align: answer(a, p.align).ok(),
        offsets,
    });
}

/// C spellings of the scalar types whose alignment the runtime takes to
/// equal their size.
const SCALARS: &[&str] = &[
    "_Bool",
    "char",
    "short",
    "int",
    "long",
    "long long",
    "float",
    "double",
    "void *",
    "void (*)(void)",
];

pub(crate) fn probe(entry: &Entry, args: &ClangArgs, tu: &TranslationUnit) -> Result<Layouts> {
    let mut pl = Planner {
        tu,
        questions: Vec::new(),
    };
    let mut plans = Vec::new();
    for def in tu.records.values() {
        let ty = QualType::plain(Type::Record {
            kind: def.kind,
            name: def.name.clone(),
        });
        if def.fields.is_some()
            && let Some(base) = to_c(&ty)
        {
            plans.push(pl.plan(def, &base, "", 0));
        }
    }
    let first_scalar = pl.questions.len();
    for s in SCALARS {
        pl.questions.push(format!("_Alignof({s}) == sizeof({s})"));
    }
    if tu.target.int128_bits.is_some() {
        pl.questions
            .push("_Alignof(__int128) == sizeof(__int128)".into());
    }
    let answers = probe::ask(entry, args, &pl.questions)?;
    for (q, a) in pl.questions.iter().zip(&answers).skip(first_scalar) {
        if *a != Ok(1) {
            bail!(
                "{}: the Lean runtime takes `{q}` to hold, and clang answered {a:?}",
                entry.file
            );
        }
    }
    let mut out = Layouts::default();
    for p in &plans {
        resolve(p, 0, &answers, &mut out.records);
    }
    Ok(out)
}

impl Layouts {
    /// Size and alignment in bytes of a complete object type.
    pub(crate) fn size_align(&self, t: &QualType) -> Result<(u64, u64), String> {
        match &t.ty {
            Type::Bool { bits } | Type::Float { bits, .. } => {
                Ok((u64::from(*bits / 8), u64::from(*bits / 8)))
            }
            Type::Int(i) => Ok((u64::from(i.bits / 8), u64::from(i.bits / 8))),
            Type::Pointer(_) => Ok((8, 8)),
            Type::Atomic(inner) => self.size_align(inner),
            Type::Array { elem, len } => {
                let (s, a) = self.size_align(elem)?;
                let n = len.ok_or("array of unknown length")?;
                Ok((s.checked_mul(n).ok_or("array size overflows")?, a))
            }
            Type::Record { kind, name } => {
                let l = self
                    .records
                    .get(&(*kind, name.clone()))
                    .ok_or_else(|| format!("no layout for {} {name}", kind.keyword()))?;
                match (l.size, l.align) {
                    (Some(s), Some(a)) => Ok((s, a)),
                    _ => Err(format!(
                        "clang could not be asked the size of {} {name}",
                        kind.keyword()
                    )),
                }
            }
            Type::Enum(n) => self.enums.get(n).map_or_else(
                || Err(format!("enum {n} without a known integer type")),
                |i| Ok((u64::from(i.bits / 8), u64::from(i.bits / 8))),
            ),
            Type::Void | Type::Function(_) | Type::Unsupported { .. } => {
                Err(format!("type {t} has no size"))
            }
        }
    }
}

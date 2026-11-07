//! The lean4export 3.1.0 NDJSON format.

use crate::{
    env::{Binder, Hints, QuotKind},
    error::{corrupt, Result},
    record::{
        Binding, Counts, Decl, Head, IndCtor, IndRec, IndRule, IndType, Record, Safety, Sink,
    },
};
use rayon::prelude::*;
use serde::{
    de::{self, MapAccess, Visitor},
    Deserialize, Deserializer,
};
use serde_json::value::RawValue;
use std::{
    fmt,
    io::{self, BufRead, Write},
};

/// Writes records as NDJSON lines, byte for byte as lean4export does.
#[derive(Debug)]
pub struct Ndjson<W: Write> {
    out: W,
    buf: Vec<u8>,
}

impl<W: Write> Ndjson<W> {
    pub const fn new(out: W) -> Self {
        Self {
            out,
            buf: Vec::new(),
        }
    }

    fn start(&mut self) -> &mut Self {
        self.buf.clear();
        self
    }

    fn emit(&mut self) -> Result<()> {
        self.buf.push(b'\n');
        self.out.write_all(&self.buf)?;
        Ok(())
    }

    fn s(&mut self, s: &str) -> &mut Self {
        self.buf.extend_from_slice(s.as_bytes());
        self
    }

    fn n(&mut self, n: impl itoa::Integer) -> &mut Self {
        self.s(itoa::Buffer::new().format(n))
    }

    fn b(&mut self, b: bool) -> &mut Self {
        self.s(if b { "true" } else { "false" })
    }

    fn list(&mut self, ids: &[u32]) -> &mut Self {
        self.s("[");
        for (i, &id) in ids.iter().enumerate() {
            if i > 0 {
                self.s(",");
            }
            self.n(id);
        }
        self.s("]")
    }

    fn q(&mut self, s: &str) -> &mut Self {
        self.s("\"");
        for c in s.chars() {
            match c {
                '"' => self.s("\\\""),
                '\\' => self.s("\\\\"),
                '\n' => self.s("\\n"),
                '\r' => self.s("\\r"),
                c if (c as u32) < 0x20 => self.s("\\u00").s(&format!("{:02x}", c as u32)),
                c => self.s(c.encode_utf8(&mut [0; 4])),
            };
        }
        self.s("\"")
    }

    /// `"levelParams":[..],"name":N` and, for `ty`, `"type":T`.
    fn lp_name(&mut self, h: &Head) -> &mut Self {
        self.s(r#""levelParams":"#)
            .list(&h.level_params)
            .s(r#","name":"#)
            .n(h.name)
    }

    fn unsafe_(&mut self, u: bool) -> &mut Self {
        self.s(r#""isUnsafe":"#).b(u)
    }

    fn ctor(&mut self, c: &IndCtor) {
        self.s(r#"{"cidx":"#)
            .n(c.cidx)
            .s(r#","induct":"#)
            .n(c.induct)
            .s(",")
            .unsafe_(c.is_unsafe)
            .s(",")
            .lp_name(&c.head)
            .s(r#","numFields":"#)
            .n(c.num_fields)
            .s(r#","numParams":"#)
            .n(c.num_params)
            .s(r#","type":"#)
            .n(c.head.ty)
            .s("}");
    }

    fn rec(&mut self, r: &IndRec) {
        self.s(r#"{"all":"#)
            .list(&r.all)
            .s(",")
            .unsafe_(r.is_unsafe)
            .s(r#","k":"#)
            .b(r.k)
            .s(",")
            .lp_name(&r.head)
            .s(r#","numIndices":"#)
            .n(r.num_indices)
            .s(r#","numMinors":"#)
            .n(r.num_minors)
            .s(r#","numMotives":"#)
            .n(r.num_motives)
            .s(r#","numParams":"#)
            .n(r.num_params)
            .s(r#","rules":["#);
        for (i, rule) in r.rules.iter().enumerate() {
            if i > 0 {
                self.s(",");
            }
            self.s(r#"{"ctor":"#)
                .n(rule.ctor)
                .s(r#","nfields":"#)
                .n(rule.nfields)
                .s(r#","rhs":"#)
                .n(rule.rhs)
                .s("}");
        }
        self.s(r#"],"type":"#).n(r.head.ty).s("}");
    }

    fn ty(&mut self, t: &IndType) {
        self.s(r#"{"all":"#)
            .list(&t.all)
            .s(r#","ctors":"#)
            .list(&t.ctors)
            .s(r#","isRec":"#)
            .b(t.is_rec)
            .s(r#","isReflexive":"#)
            .b(t.is_reflexive)
            .s(",")
            .unsafe_(t.is_unsafe)
            .s(",")
            .lp_name(&t.head)
            .s(r#","numIndices":"#)
            .n(t.num_indices)
            .s(r#","numNested":"#)
            .n(t.num_nested)
            .s(r#","numParams":"#)
            .n(t.num_params)
            .s(r#","type":"#)
            .n(t.head.ty)
            .s("}");
    }

    fn all_opt(&mut self, all: Option<&Vec<u32>>) -> &mut Self {
        if let Some(all) = all {
            self.s(r#""all":"#).list(all).s(",");
        }
        self
    }
}

const fn binder(b: Binder) -> &'static str {
    match b {
        Binder::Default => "default",
        Binder::Implicit => "implicit",
        Binder::StrictImplicit => "strictImplicit",
        Binder::InstImplicit => "instImplicit",
    }
}

impl<W: Write> Sink for Ndjson<W> {
    type Output = W;

    fn record(&mut self, id: Option<u32>, r: &Record<'_>) -> Result<()> {
        let Some(id) = id else {
            self.start();
            match r {
                Record::Meta(json) => {
                    self.start().s(r#"{"meta":"#).s(json).s("}");
                }
                Record::Decl(d) => self.decl(d),
                _ => return Ok(()),
            }
            return self.emit();
        };
        self.start();
        let level = |this: &mut Self, key: &str| {
            this.s(r#"{"il":"#).n(id).s(r#",""#).s(key).s(r#"":"#);
        };
        let binding = |this: &mut Self, b: &Binding| {
            this.s(r#"{"binderInfo":""#)
                .s(binder(b.info))
                .s(r#"","body":"#)
                .n(b.body)
                .s(r#","name":"#)
                .n(b.name)
                .s(r#","type":"#)
                .n(b.ty)
                .s("}");
        };
        match r {
            Record::NameStr { pre, str } => {
                self.s(r#"{"in":"#)
                    .n(id)
                    .s(r#","str":{"pre":"#)
                    .n(*pre)
                    .s(r#","str":"#)
                    .q(str)
                    .s("}}");
            }
            Record::NameNum { pre, i } => {
                self.s(r#"{"in":"#)
                    .n(id)
                    .s(r#","num":{"i":"#)
                    .n(*i)
                    .s(r#","pre":"#)
                    .n(*pre)
                    .s("}}");
            }
            Record::Succ(a) => {
                level(self, "succ");
                self.n(*a).s("}");
            }
            Record::Param(a) => {
                level(self, "param");
                self.n(*a).s("}");
            }
            Record::Max(a, b) | Record::IMax(a, b) => {
                level(
                    self,
                    if matches!(r, Record::Max(..)) {
                        "max"
                    } else {
                        "imax"
                    },
                );
                self.s("[").n(*a).s(",").n(*b).s("]}");
            }
            Record::BVar(i) => {
                self.s(r#"{"bvar":"#).n(*i).s(r#","ie":"#).n(id).s("}");
            }
            Record::Sort(l) => {
                self.s(r#"{"ie":"#).n(id).s(r#","sort":"#).n(*l).s("}");
            }
            Record::Const { name, us } => {
                self.s(r#"{"const":{"name":"#)
                    .n(*name)
                    .s(r#","us":"#)
                    .list(us)
                    .s(r#"},"ie":"#)
                    .n(id)
                    .s("}");
            }
            Record::App { fun, arg } => {
                self.s(r#"{"app":{"arg":"#)
                    .n(*arg)
                    .s(r#","fn":"#)
                    .n(*fun)
                    .s(r#"},"ie":"#)
                    .n(id)
                    .s("}");
            }
            Record::Lam(b) => {
                self.s(r#"{"ie":"#).n(id).s(r#","lam":"#);
                binding(self, b);
                self.s("}");
            }
            Record::Pi(b) => {
                self.s(r#"{"forallE":"#);
                binding(self, b);
                self.s(r#","ie":"#).n(id).s("}");
            }
            Record::Let {
                name,
                ty,
                value,
                body,
                nondep,
            } => {
                self.s(r#"{"ie":"#)
                    .n(id)
                    .s(r#","letE":{"body":"#)
                    .n(*body)
                    .s(r#","name":"#)
                    .n(*name)
                    .s(r#","nondep":"#)
                    .b(*nondep)
                    .s(r#","type":"#)
                    .n(*ty)
                    .s(r#","value":"#)
                    .n(*value)
                    .s("}}");
            }
            Record::Nat(v) => {
                self.s(r#"{"ie":"#)
                    .n(id)
                    .s(r#","natVal":""#)
                    .s(v)
                    .s(r#""}"#);
            }
            Record::Str(v) => {
                self.s(r#"{"ie":"#).n(id).s(r#","strVal":"#).q(v).s("}");
            }
            Record::Proj {
                type_name,
                idx,
                struct_,
            } => {
                self.s(r#"{"ie":"#)
                    .n(id)
                    .s(r#","proj":{"idx":"#)
                    .n(*idx)
                    .s(r#","struct":"#)
                    .n(*struct_)
                    .s(r#","typeName":"#)
                    .n(*type_name)
                    .s("}}");
            }
            Record::MData(x) => {
                self.s(r#"{"ie":"#)
                    .n(id)
                    .s(r#","mdata":{"expr":"#)
                    .n(*x)
                    .s("}}");
            }
            Record::Meta(_) | Record::Decl(_) | Record::End(_) => unreachable!(),
        }
        self.emit()
    }

    fn finish(mut self) -> Result<W> {
        self.out.flush()?;
        Ok(self.out)
    }
}

impl<W: Write> Ndjson<W> {
    fn decl(&mut self, d: &Decl) {
        match d {
            Decl::Axiom {
                head,
                is_unsafe,
                all,
            } => {
                self.s(r#"{"axiom":{"#)
                    .all_opt(all.as_ref())
                    .unsafe_(*is_unsafe)
                    .s(",")
                    .lp_name(head)
                    .s(r#","type":"#)
                    .n(head.ty)
                    .s("}}");
            }
            Decl::Def {
                head,
                value,
                hints,
                safety,
                all,
            } => {
                self.s(r#"{"def":{"all":"#).list(all).s(r#","hints":"#);
                match hints {
                    Hints::Opaque => self.s(r#""opaque""#),
                    Hints::Abbrev => self.s(r#""abbrev""#),
                    Hints::Regular(h) => self.s(r#"{"regular":"#).n(*h).s("}"),
                };
                let safety = match safety {
                    Safety::Safe => "safe",
                    Safety::Unsafe => "unsafe",
                    Safety::Partial => "partial",
                };
                self.s(",")
                    .lp_name(head)
                    .s(r#","safety":""#)
                    .s(safety)
                    .s(r#"","type":"#)
                    .n(head.ty)
                    .s(r#","value":"#)
                    .n(*value)
                    .s("}}");
            }
            Decl::Thm { head, value, all } => {
                self.s(r#"{"thm":{"all":"#)
                    .list(all)
                    .s(",")
                    .lp_name(head)
                    .s(r#","type":"#)
                    .n(head.ty)
                    .s(r#","value":"#)
                    .n(*value)
                    .s("}}");
            }
            Decl::Opaque {
                head,
                value,
                is_unsafe,
                all,
            } => {
                self.s(r#"{"opaque":{"#)
                    .all_opt(all.as_ref())
                    .unsafe_(*is_unsafe)
                    .s(",")
                    .lp_name(head)
                    .s(r#","type":"#)
                    .n(head.ty)
                    .s(r#","value":"#)
                    .n(*value)
                    .s("}}");
            }
            Decl::Quot { head, kind } => {
                let kind = match kind {
                    QuotKind::Type => "type",
                    QuotKind::Ctor => "ctor",
                    QuotKind::Lift => "lift",
                    QuotKind::Ind => "ind",
                };
                self.s(r#"{"quot":{"kind":""#)
                    .s(kind)
                    .s(r#"","#)
                    .lp_name(head)
                    .s(r#","type":"#)
                    .n(head.ty)
                    .s("}}");
            }
            Decl::Inductive { types, ctors, recs } => {
                self.s(r#"{"inductive":{"ctors":["#);
                for (i, c) in ctors.iter().enumerate() {
                    self.sep(i).ctor(c);
                }
                self.s(r#"],"recs":["#);
                for (i, r) in recs.iter().enumerate() {
                    self.sep(i).rec(r);
                }
                self.s(r#"],"types":["#);
                for (i, t) in types.iter().enumerate() {
                    self.sep(i).ty(t);
                }
                self.s("]}}");
            }
        }
    }

    fn sep(&mut self, i: usize) -> &mut Self {
        if i > 0 {
            self.s(",");
        }
        self
    }
}

/// Replay lean4export NDJSON into `sink`. Ids must be consecutive, as lean4export writes them.
///
/// Lines parse in parallel batches, each while `sink` takes the batch before it.
pub fn read<S: Sink>(mut input: impl BufRead, mut sink: S) -> Result<S::Output> {
    const BATCH: usize = 1 << 15;
    let mut next = Counts::default();
    let mut base = 0;
    let mut parsed = parse(&batch(&mut input, BATCH)?, base);
    while let Some(records) = parsed? {
        let lines = batch(&mut input, BATCH)?;
        let mut ahead = Ok(None);
        let mut fed = Ok(());
        rayon::in_place_scope(|s| {
            s.spawn(|_| ahead = parse(&lines, base + BATCH));
            fed = records.iter().try_for_each(|(n, id, r)| {
                let want = next.assign(r);
                if let (Some(id), Some(want)) = (id, want) {
                    if *id != want {
                        return Err(corrupt(format!("line {n}: id {id}, expected {want}")));
                    }
                }
                sink.record(want, r)
            });
        });
        fed?;
        parsed = ahead;
        base += BATCH;
    }
    sink.record(None, &Record::End(next))?;
    sink.finish()
}

fn batch(input: &mut impl BufRead, n: usize) -> Result<Vec<String>> {
    input
        .lines()
        .take(n)
        .collect::<io::Result<_>>()
        .map_err(Into::into)
}

type Parsed = Vec<(usize, Option<u32>, Record<'static>)>;

fn parse(lines: &[String], base: usize) -> Result<Option<Parsed>> {
    if lines.is_empty() {
        return Ok(None);
    }
    lines
        .par_iter()
        .enumerate()
        .filter(|(_, l)| !l.is_empty())
        .map(|(i, line)| {
            let n = base + i + 1;
            let at = |e: serde_json::Error| corrupt(format!("line {n}: {e}"));
            let (id, r) = if line.starts_with(r#"{"meta":"#) {
                let m: Meta<'_> = serde_json::from_str(line).map_err(at)?;
                (None, Record::Meta(m.meta.get().to_owned().into()))
            } else {
                let Line(id, r) = serde_json::from_str(line).map_err(at)?;
                (id, r)
            };
            Ok((n, id, r))
        })
        .collect::<Result<_>>()
        .map(Some)
}

#[derive(Deserialize)]
struct Meta<'a> {
    #[serde(borrow)]
    meta: &'a RawValue,
}

/// One non-meta line: its id, if it is not a declaration, and its record.
struct Line(Option<u32>, Record<'static>);

impl<'de> Deserialize<'de> for Line {
    fn deserialize<D: Deserializer<'de>>(d: D) -> std::result::Result<Self, D::Error> {
        d.deserialize_map(LineVisitor)
    }
}

const KEYS: &[&str] = &[
    "in",
    "il",
    "ie",
    "str",
    "num",
    "succ",
    "max",
    "imax",
    "param",
    "bvar",
    "sort",
    "const",
    "app",
    "lam",
    "forallE",
    "letE",
    "natVal",
    "strVal",
    "proj",
    "mdata",
    "axiom",
    "def",
    "thm",
    "opaque",
    "quot",
    "inductive",
];

struct LineVisitor;

impl<'de> Visitor<'de> for LineVisitor {
    type Value = Line;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a lean4export record")
    }

    /// Each key names the shape of its value, so the line parses in one pass whatever order
    /// its keys come in.
    fn visit_map<A: MapAccess<'de>>(self, mut m: A) -> std::result::Result<Line, A::Error> {
        let (mut id, mut rec) = (None, None);
        while let Some(k) = m.next_key::<&str>()? {
            let r = match k {
                "in" | "il" | "ie" => {
                    id = Some(m.next_value()?);
                    continue;
                }
                "str" => {
                    let JStr { pre, str } = m.next_value()?;
                    Record::NameStr {
                        pre,
                        str: str.into(),
                    }
                }
                "num" => {
                    let JNum { pre, i } = m.next_value()?;
                    Record::NameNum { pre, i }
                }
                "succ" => Record::Succ(m.next_value()?),
                "max" => {
                    let (a, b) = m.next_value()?;
                    Record::Max(a, b)
                }
                "imax" => {
                    let (a, b) = m.next_value()?;
                    Record::IMax(a, b)
                }
                "param" => Record::Param(m.next_value()?),
                "bvar" => Record::BVar(m.next_value()?),
                "sort" => Record::Sort(m.next_value()?),
                "const" => {
                    let JConst { name, us } = m.next_value()?;
                    Record::Const { name, us }
                }
                "app" => {
                    let JApp { fun, arg } = m.next_value()?;
                    Record::App { fun, arg }
                }
                "lam" => Record::Lam(m.next_value::<JBinding>()?.into()),
                "forallE" => Record::Pi(m.next_value::<JBinding>()?.into()),
                "letE" => {
                    let JLet {
                        name,
                        ty,
                        value,
                        body,
                        nondep,
                    } = m.next_value()?;
                    Record::Let {
                        name,
                        ty,
                        value,
                        body,
                        nondep,
                    }
                }
                "natVal" => Record::Nat(m.next_value::<String>()?.into()),
                "strVal" => Record::Str(m.next_value::<String>()?.into()),
                "proj" => {
                    let JProj {
                        type_name,
                        idx,
                        struct_,
                    } = m.next_value()?;
                    Record::Proj {
                        type_name,
                        idx,
                        struct_,
                    }
                }
                "mdata" => Record::MData(m.next_value::<JMdata>()?.expr),
                "axiom" => Record::Decl(m.next_value::<JAxiom>()?.into()),
                "def" => Record::Decl(m.next_value::<JDef>()?.into()),
                "thm" => Record::Decl(m.next_value::<JThm>()?.into()),
                "opaque" => Record::Decl(m.next_value::<JOpaque>()?.into()),
                "quot" => Record::Decl(m.next_value::<JQuot>()?.into()),
                "inductive" => Record::Decl(m.next_value::<JInductive>()?.into()),
                _ => return Err(de::Error::unknown_field(k, KEYS)),
            };
            if rec.replace(r).is_some() {
                return Err(de::Error::custom("more than one record on a line"));
            }
        }
        let rec = rec.ok_or_else(|| de::Error::custom("no record on the line"))?;
        match (&rec, id) {
            (Record::Decl(_), Some(_)) => Err(de::Error::custom("a declaration has no id")),
            (Record::Decl(_), None) | (_, Some(_)) => Ok(Line(id, rec)),
            (_, None) => Err(de::Error::custom("missing id")),
        }
    }
}

#[derive(Deserialize)]
struct JStr {
    pre: u32,
    str: String,
}

#[derive(Deserialize)]
struct JNum {
    pre: u32,
    i: u64,
}

#[derive(Deserialize)]
struct JConst {
    name: u32,
    us: Vec<u32>,
}

#[derive(Deserialize)]
struct JApp {
    #[serde(rename = "fn")]
    fun: u32,
    arg: u32,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct JBinding {
    binder_info: Binder,
    name: u32,
    #[serde(rename = "type")]
    ty: u32,
    body: u32,
}

#[derive(Deserialize)]
struct JLet {
    name: u32,
    #[serde(rename = "type")]
    ty: u32,
    value: u32,
    body: u32,
    #[serde(default)]
    nondep: bool,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct JProj {
    type_name: u32,
    idx: u64,
    #[serde(rename = "struct")]
    struct_: u32,
}

#[derive(Deserialize)]
struct JMdata {
    expr: u32,
}

#[derive(Deserialize)]
#[serde(rename_all = "lowercase")]
enum JSafety {
    Safe,
    Unsafe,
    Partial,
}

/// The fields every declaration starts with, spelled out in each one since `flatten` would
/// buffer the whole object.
macro_rules! head {
    ($d:ident) => {
        Head {
            name: $d.name,
            level_params: $d.level_params,
            ty: $d.ty,
        }
    };
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct JAxiom {
    name: u32,
    level_params: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    #[serde(default)]
    is_unsafe: bool,
    all: Option<Vec<u32>>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct JDef {
    name: u32,
    level_params: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    value: u32,
    hints: Hints,
    safety: JSafety,
    all: Vec<u32>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct JThm {
    name: u32,
    level_params: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    value: u32,
    all: Vec<u32>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct JOpaque {
    name: u32,
    level_params: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    value: u32,
    #[serde(default)]
    is_unsafe: bool,
    all: Option<Vec<u32>>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct JQuot {
    name: u32,
    level_params: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    kind: QuotKind,
}

#[derive(Deserialize)]
struct JInductive {
    types: Vec<JType>,
    ctors: Vec<JCtor>,
    recs: Vec<JRec>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct JType {
    name: u32,
    level_params: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    #[serde(default)]
    is_unsafe: bool,
    num_params: u64,
    num_indices: u64,
    all: Vec<u32>,
    ctors: Vec<u32>,
    num_nested: u64,
    is_rec: bool,
    is_reflexive: bool,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct JCtor {
    name: u32,
    level_params: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    #[serde(default)]
    is_unsafe: bool,
    induct: u32,
    cidx: u64,
    num_params: u64,
    num_fields: u64,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct JRec {
    name: u32,
    level_params: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    #[serde(default)]
    is_unsafe: bool,
    all: Vec<u32>,
    num_params: u64,
    num_indices: u64,
    num_motives: u64,
    num_minors: u64,
    rules: Vec<IndRule>,
    k: bool,
}

impl From<JBinding> for Binding {
    fn from(b: JBinding) -> Self {
        Self {
            info: b.binder_info,
            name: b.name,
            ty: b.ty,
            body: b.body,
        }
    }
}

impl From<JAxiom> for Decl {
    fn from(d: JAxiom) -> Self {
        Self::Axiom {
            is_unsafe: d.is_unsafe,
            all: d.all,
            head: head!(d),
        }
    }
}

impl From<JDef> for Decl {
    fn from(d: JDef) -> Self {
        Self::Def {
            value: d.value,
            hints: d.hints,
            safety: match d.safety {
                JSafety::Safe => Safety::Safe,
                JSafety::Unsafe => Safety::Unsafe,
                JSafety::Partial => Safety::Partial,
            },
            all: d.all,
            head: head!(d),
        }
    }
}

impl From<JThm> for Decl {
    fn from(d: JThm) -> Self {
        Self::Thm {
            value: d.value,
            all: d.all,
            head: head!(d),
        }
    }
}

impl From<JOpaque> for Decl {
    fn from(d: JOpaque) -> Self {
        Self::Opaque {
            value: d.value,
            is_unsafe: d.is_unsafe,
            all: d.all,
            head: head!(d),
        }
    }
}

impl From<JQuot> for Decl {
    fn from(d: JQuot) -> Self {
        Self::Quot {
            kind: d.kind,
            head: head!(d),
        }
    }
}

impl From<JInductive> for Decl {
    fn from(d: JInductive) -> Self {
        Self::Inductive {
            types: d
                .types
                .into_iter()
                .map(|t| IndType {
                    is_unsafe: t.is_unsafe,
                    num_params: t.num_params,
                    num_indices: t.num_indices,
                    all: t.all,
                    ctors: t.ctors,
                    num_nested: t.num_nested,
                    is_rec: t.is_rec,
                    is_reflexive: t.is_reflexive,
                    head: head!(t),
                })
                .collect(),
            ctors: d
                .ctors
                .into_iter()
                .map(|c| IndCtor {
                    is_unsafe: c.is_unsafe,
                    induct: c.induct,
                    cidx: c.cidx,
                    num_params: c.num_params,
                    num_fields: c.num_fields,
                    head: head!(c),
                })
                .collect(),
            recs: d
                .recs
                .into_iter()
                .map(|r| IndRec {
                    is_unsafe: r.is_unsafe,
                    all: r.all,
                    num_params: r.num_params,
                    num_indices: r.num_indices,
                    num_motives: r.num_motives,
                    num_minors: r.num_minors,
                    rules: r.rules,
                    k: r.k,
                    head: head!(r),
                })
                .collect(),
        }
    }
}

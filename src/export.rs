use crate::{
    env::{
        Binder, Const, Ctor, Env, Expr, ExprId, Hints, Inductive, Kind, Level, LevelId, Name,
        NameId, QuotKind, Rec, ANON, ZERO,
    },
    error::{corrupt, Result},
};
use rustc_hash::FxHashSet;
use std::{fmt::Write as _, io::Write};

const UNSEEN: u32 = u32::MAX;

/// Lines written so far for each table, which is also the next id each hands out.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Counts {
    pub names: u32,
    pub levels: u32,
    pub exprs: u32,
}

/// Streams an [`Env`] in the lean4export 3.1.0 NDJSON format. Ids are assigned on first
/// use and every line only refers to lines already written.
///
/// Exporting recurses once per nested subterm, which overflows the default stack on large
/// libraries such as Mathlib, so run it inside [`crate::with_big_stack`].
#[derive(Debug)]
pub struct Exporter<'a, W: Write> {
    env: &'a Env,
    out: W,
    names: Vec<u32>,
    levels: Vec<u32>,
    exprs: Vec<u32>,
    next: Counts,
    scanned: Vec<bool>,
    visited: FxHashSet<NameId>,
    nat: Option<NameId>,
    str_deps: [Option<NameId>; 2],
    quot: [Option<NameId>; 5],
    buf: Line,
}

/// A reusable output line, since `format!` per record dominated export time.
#[derive(Debug, Default)]
struct Line(Vec<u8>);

impl Line {
    fn s(&mut self, s: &str) -> &mut Self {
        self.0.extend_from_slice(s.as_bytes());
        self
    }

    fn n(&mut self, n: impl itoa::Integer) -> &mut Self {
        self.s(itoa::Buffer::new().format(n))
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
                '\t' => self.s("\\t"),
                c if (c as u32) < 0x20 || c == '\u{7f}' => {
                    self.s("\\u00").s(&format!("{:02x}", c as u32))
                }
                c => self.s(c.encode_utf8(&mut [0; 4])),
            };
        }
        self.s("\"")
    }
}

impl<'a, W: Write> Exporter<'a, W> {
    pub fn new(env: &'a Env, out: W) -> Self {
        let mut names = vec![UNSEEN; env.names.bound()];
        let mut levels = vec![UNSEEN; env.levels.bound()];
        names[ANON.index()] = 0;
        levels[ZERO.index()] = 0;
        let find = |s| env.find_name(s);
        Self {
            env,
            out,
            names,
            levels,
            exprs: vec![UNSEEN; env.exprs.bound()],
            next: Counts {
                names: 1,
                levels: 1,
                exprs: 0,
            },
            scanned: vec![false; env.exprs.bound()],
            visited: FxHashSet::default(),
            nat: find("Nat"),
            str_deps: [find("Char.ofNat"), find("String.ofList")],
            quot: [
                find("Eq"),
                find("Quot"),
                find("Quot.mk"),
                find("Quot.lift"),
                find("Quot.ind"),
            ],
            buf: Line::default(),
        }
    }

    pub fn meta(&mut self) -> Result<()> {
        let h = &self.env.header;
        writeln!(
            self.out,
            r#"{{"meta":{{"exporter":{{"name":"olean-export","version":"{}"}},"format":{{"version":"3.1.0"}},"lean":{{"githash":"{}","version":"{}"}}}}}}"#,
            env!("CARGO_PKG_VERSION"),
            h.githash,
            h.version
        )?;
        Ok(())
    }

    /// Export every non-internal constant in load order, like `lean4export` with no `--`.
    pub fn all(&mut self) -> Result<()> {
        self.env.roots().try_for_each(|c| self.constant(c))
    }

    #[must_use]
    pub const fn counts(&self) -> Counts {
        self.next
    }

    pub fn finish(mut self) -> Result<W> {
        self.out.flush()?;
        Ok(self.out)
    }

    fn start(&mut self) -> &mut Line {
        self.buf.0.clear();
        &mut self.buf
    }

    fn emit(&mut self) -> Result<()> {
        self.buf.0.push(b'\n');
        self.out.write_all(&self.buf.0)?;
        Ok(())
    }

    fn line(&mut self, s: &str) -> Result<()> {
        self.out.write_all(s.as_bytes())?;
        self.out.write_all(b"\n")?;
        Ok(())
    }

    fn name(&mut self, n: NameId) -> Result<u32> {
        if self.names[n.index()] != UNSEEN {
            return Ok(self.names[n.index()]);
        }
        let id = match &self.env.names[n] {
            Name::Anon => unreachable!(),
            Name::Str(p, s) => {
                let p = self.name(*p)?;
                let id = fresh(&mut self.next.names);
                self.start()
                    .s(r#"{"in":"#)
                    .n(id)
                    .s(r#","str":{"pre":"#)
                    .n(p);
                self.buf.s(r#","str":"#).q(s).s("}}");
                id
            }
            Name::Num(p, i) => {
                let p = self.name(*p)?;
                let id = fresh(&mut self.next.names);
                self.start().s(r#"{"in":"#).n(id).s(r#","num":{"i":"#).n(*i);
                self.buf.s(r#","pre":"#).n(p).s("}}");
                id
            }
        };
        self.emit()?;
        self.names[n.index()] = id;
        Ok(id)
    }

    fn name_list(&mut self, ns: &[NameId]) -> Result<String> {
        let ids = ns
            .iter()
            .map(|&n| self.name(n))
            .collect::<Result<Vec<_>>>()?;
        Ok(json_list(&ids))
    }

    fn level_params(&mut self, ps: &[NameId]) -> Result<String> {
        let list = self.name_list(ps)?;
        for &p in ps {
            let l = self
                .env
                .levels
                .get(&Level::Param(p))
                .expect("level params are interned at load");
            self.level(l)?;
        }
        Ok(list)
    }

    fn level(&mut self, l: LevelId) -> Result<u32> {
        if self.levels[l.index()] != UNSEEN {
            return Ok(self.levels[l.index()]);
        }
        let (key, a, b) = match self.env.levels[l] {
            Level::Zero => unreachable!(),
            Level::Succ(a) => ("succ", self.level(a)?, None),
            Level::Max(a, b) => ("max", self.level(a)?, Some(self.level(b)?)),
            Level::IMax(a, b) => ("imax", self.level(a)?, Some(self.level(b)?)),
            Level::Param(n) => ("param", self.name(n)?, None),
        };
        let id = fresh(&mut self.next.levels);
        let line = self
            .start()
            .s(r#"{"il":"#)
            .n(id)
            .s(r#",""#)
            .s(key)
            .s(r#"":"#);
        match b {
            None => line.n(a),
            Some(b) => line.s("[").n(a).s(",").n(b).s("]"),
        }
        .s("}");
        self.emit()?;
        self.levels[l.index()] = id;
        Ok(id)
    }

    fn expr(&mut self, e: ExprId) -> Result<u32> {
        if self.exprs[e.index()] != UNSEEN {
            return Ok(self.exprs[e.index()]);
        }
        let id = match &self.env.exprs[e] {
            Expr::BVar(i) => {
                let id = fresh(&mut self.next.exprs);
                self.start()
                    .s(r#"{"bvar":"#)
                    .n(*i)
                    .s(r#","ie":"#)
                    .n(id)
                    .s("}");
                id
            }
            Expr::Sort(l) => {
                let l = self.level(*l)?;
                let id = fresh(&mut self.next.exprs);
                self.start()
                    .s(r#"{"ie":"#)
                    .n(id)
                    .s(r#","sort":"#)
                    .n(l)
                    .s("}");
                id
            }
            Expr::Const(n, us) => {
                let n = self.name(*n)?;
                let us = us
                    .iter()
                    .map(|&u| self.level(u))
                    .collect::<Result<Vec<_>>>()?;
                let id = fresh(&mut self.next.exprs);
                self.start().s(r#"{"const":{"name":"#).n(n).s(r#","us":"#);
                self.buf.list(&us).s(r#"},"ie":"#).n(id).s("}");
                id
            }
            Expr::App(f, a) => {
                let (f, a) = (self.expr(*f)?, self.expr(*a)?);
                let id = fresh(&mut self.next.exprs);
                self.start().s(r#"{"app":{"arg":"#).n(a).s(r#","fn":"#).n(f);
                self.buf.s(r#"},"ie":"#).n(id).s("}");
                id
            }
            Expr::Lam(n, t, b, bi) | Expr::Pi(n, t, b, bi) => {
                let (n, t, b) = (self.name(*n)?, self.expr(*t)?, self.expr(*b)?);
                let id = fresh(&mut self.next.exprs);
                let lam = matches!(self.env.exprs[e], Expr::Lam(..));
                let line = self.start();
                if lam {
                    line.s(r#"{"ie":"#).n(id).s(r#","lam":"#);
                } else {
                    line.s(r#"{"forallE":"#);
                }
                line.s(r#"{"binderInfo":""#)
                    .s(binder(*bi))
                    .s(r#"","body":"#)
                    .n(b);
                line.s(r#","name":"#).n(n).s(r#","type":"#).n(t).s("}");
                if lam {
                    line.s("}");
                } else {
                    line.s(r#","ie":"#).n(id).s("}");
                }
                id
            }
            Expr::Let(n, t, v, b) => {
                let (n, t, v, b) = (
                    self.name(*n)?,
                    self.expr(*t)?,
                    self.expr(*v)?,
                    self.expr(*b)?,
                );
                let id = fresh(&mut self.next.exprs);
                self.start()
                    .s(r#"{"ie":"#)
                    .n(id)
                    .s(r#","letE":{"body":"#)
                    .n(b);
                self.buf
                    .s(r#","name":"#)
                    .n(n)
                    // Lean marks most `let`s nondep, but lean4export writes false for all of
                    // them so that terms differing only in the flag share one index.
                    .s(r#","nondep":false,"type":"#)
                    .n(t);
                self.buf.s(r#","value":"#).n(v).s("}}");
                id
            }
            Expr::Nat(v) => {
                if let Some(nat) = self.nat {
                    self.constant(nat)?;
                }
                let id = fresh(&mut self.next.exprs);
                self.start()
                    .s(r#"{"ie":"#)
                    .n(id)
                    .s(r#","natVal":""#)
                    .s(v)
                    .s(r#""}"#);
                id
            }
            Expr::Str(v) => {
                for c in self.str_deps.into_iter().flatten() {
                    self.constant(c)?;
                }
                let id = fresh(&mut self.next.exprs);
                self.start()
                    .s(r#"{"ie":"#)
                    .n(id)
                    .s(r#","strVal":"#)
                    .q(v)
                    .s("}");
                id
            }
            Expr::Proj(n, i, x) => {
                let (n, x) = (self.name(*n)?, self.expr(*x)?);
                let id = fresh(&mut self.next.exprs);
                self.start()
                    .s(r#"{"ie":"#)
                    .n(id)
                    .s(r#","proj":{"idx":"#)
                    .n(*i);
                self.buf
                    .s(r#","struct":"#)
                    .n(x)
                    .s(r#","typeName":"#)
                    .n(n)
                    .s("}}");
                id
            }
        };
        self.emit()?;
        self.exprs[e.index()] = id;
        Ok(id)
    }

    fn deps(&mut self, e: ExprId) -> Result<()> {
        if self.scanned[e.index()] {
            return Ok(());
        }
        match &self.env.exprs[e] {
            Expr::Const(n, _) => self.constant(*n)?,
            Expr::App(a, b) | Expr::Lam(_, a, b, _) | Expr::Pi(_, a, b, _) => {
                self.deps(*a)?;
                self.deps(*b)?;
            }
            Expr::Let(_, t, v, b) => {
                self.deps(*t)?;
                self.deps(*v)?;
                self.deps(*b)?;
            }
            Expr::Proj(_, _, x) => self.deps(*x)?,
            Expr::BVar(_) | Expr::Sort(_) | Expr::Nat(_) | Expr::Str(_) => {}
        }
        self.scanned[e.index()] = true;
        Ok(())
    }

    /// Export a constant and, first, everything it mentions.
    pub fn constant(&mut self, c: NameId) -> Result<()> {
        if !self.visited.insert(c) {
            return Ok(());
        }
        let env = self.env;
        let Some(k) = env.consts.get(&c) else {
            return Ok(());
        };
        match &k.kind {
            Kind::Axiom => {
                self.deps(k.ty)?;
                let (n, lp, t) = self.header(k)?;
                self.line(&format!(
                    r#"{{"axiom":{{"isUnsafe":false,"levelParams":{lp},"name":{n},"type":{t}}}}}"#
                ))
            }
            Kind::Defn(d) => {
                self.deps(k.ty)?;
                self.deps(d.value)?;
                let (n, lp, t) = self.header(k)?;
                let v = self.expr(d.value)?;
                let all = self.name_list(&d.all)?;
                let hints = match d.hints {
                    Hints::Opaque => r#""opaque""#.to_owned(),
                    Hints::Abbrev => r#""abbrev""#.to_owned(),
                    Hints::Regular(h) => format!(r#"{{"regular":{h}}}"#),
                };
                self.line(&format!(
                    r#"{{"def":{{"all":{all},"hints":{hints},"levelParams":{lp},"name":{n},"safety":"safe","type":{t},"value":{v}}}}}"#
                ))
            }
            Kind::Thm(b) | Kind::Opaque(b) => {
                self.deps(k.ty)?;
                self.deps(b.value)?;
                let (n, lp, t) = self.header(k)?;
                let v = self.expr(b.value)?;
                let all = self.name_list(&b.all)?;
                if matches!(k.kind, Kind::Thm(_)) {
                    self.line(&format!(r#"{{"thm":{{"all":{all},"levelParams":{lp},"name":{n},"type":{t},"value":{v}}}}}"#))
                } else {
                    self.line(&format!(
                        r#"{{"opaque":{{"all":{all},"isUnsafe":false,"levelParams":{lp},"name":{n},"type":{t},"value":{v}}}}}"#
                    ))
                }
            }
            Kind::Quot(_) => self.quot(),
            Kind::Induct(ind) => self.inductive(k, ind),
            Kind::Ctor(ctor) => self.constant(ctor.induct),
            Kind::Rec(rec) => rec.all.iter().try_for_each(|&i| self.constant(i)),
        }
    }

    fn header(&mut self, k: &Const) -> Result<(u32, String, u32)> {
        Ok((
            self.name(k.name)?,
            self.level_params(&k.level_params)?,
            self.expr(k.ty)?,
        ))
    }

    fn quot(&mut self) -> Result<()> {
        let env = self.env;
        let [eq, rest @ ..] = self.quot;
        if let Some(eq) = eq {
            self.constant(eq)?;
        }
        for c in rest.into_iter().flatten() {
            self.visited.insert(c);
            let (k, kind) = lookup(env, c, "quotient", |k| match k {
                Kind::Quot(q) => Some(q),
                _ => None,
            })?;
            let (n, lp, t) = self.header(k)?;
            let kind = match kind {
                QuotKind::Type => "type",
                QuotKind::Ctor => "ctor",
                QuotKind::Lift => "lift",
                QuotKind::Ind => "ind",
            };
            self.line(&format!(
                r#"{{"quot":{{"kind":"{kind}","levelParams":{lp},"name":{n},"type":{t}}}}}"#
            ))?;
        }
        Ok(())
    }

    fn inductive(&mut self, base: &Const, ind: &Inductive) -> Result<()> {
        let env = self.env;
        let types = ind
            .all
            .iter()
            .map(|&n| {
                lookup(env, n, "inductive", |k| match k {
                    Kind::Induct(i) => Some(i),
                    _ => None,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let mut ctors = Vec::new();
        for &(t, i) in &types {
            for &c in &i.ctors {
                ctors.push(lookup(env, c, "constructor", |k| match k {
                    Kind::Ctor(c) => Some(c),
                    _ => None,
                })?);
            }
            self.visited.insert(t.name);
            self.deps(t.ty)?;
        }
        for &(c, _) in &ctors {
            self.visited.insert(c.name);
            self.deps(c.ty)?;
        }
        let recs = env
            .recursors
            .get(&base.name)
            .map_or(&[][..], Vec::as_slice)
            .iter()
            .map(|&r| {
                lookup(env, r, "recursor", |k| match k {
                    Kind::Rec(r) => Some(r),
                    _ => None,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        for &(r, _) in &recs {
            self.visited.insert(r.name);
            self.deps(r.ty)?;
        }
        for (_, rec) in &recs {
            for rule in &rec.rules {
                self.deps(rule.rhs)?;
            }
        }
        let mut out = String::from(r#"{"inductive":{"ctors":["#);
        for (i, &(c, ctor)) in ctors.iter().enumerate() {
            let Ctor {
                induct,
                cidx,
                num_params,
                num_fields,
            } = *ctor;
            let (n, lp, t) = self.header(c)?;
            let induct = self.name(induct)?;
            sep(&mut out, i);
            let _ = write!(
                out,
                r#"{{"cidx":{cidx},"induct":{induct},"isUnsafe":false,"levelParams":{lp},"name":{n},"numFields":{num_fields},"numParams":{num_params},"type":{t}}}"#
            );
        }
        out.push_str(r#"],"recs":["#);
        for (i, &(r, rec)) in recs.iter().enumerate() {
            let Rec {
                all,
                num_params,
                num_indices,
                num_motives,
                num_minors,
                rules,
                k,
            } = rec;
            let (n, lp, t) = self.header(r)?;
            let all = self.name_list(all)?;
            let mut rs = String::new();
            for (j, rule) in rules.iter().enumerate() {
                let (ctor, rhs) = (self.name(rule.ctor)?, self.expr(rule.rhs)?);
                sep(&mut rs, j);
                let _ = write!(
                    rs,
                    r#"{{"ctor":{ctor},"nfields":{},"rhs":{rhs}}}"#,
                    rule.nfields
                );
            }
            sep(&mut out, i);
            let _ = write!(
                out,
                r#"{{"all":{all},"isUnsafe":false,"k":{k},"levelParams":{lp},"name":{n},"numIndices":{num_indices},"numMinors":{num_minors},"numMotives":{num_motives},"numParams":{num_params},"rules":[{rs}],"type":{t}}}"#
            );
        }
        out.push_str(r#"],"types":["#);
        for (i, &(ty, ind)) in types.iter().enumerate() {
            let Inductive {
                num_params,
                num_indices,
                all,
                ctors,
                num_nested,
                is_rec,
                is_reflexive,
            } = ind;
            let (n, lp, t) = self.header(ty)?;
            let (all, ctors) = (self.name_list(all)?, self.name_list(ctors)?);
            sep(&mut out, i);
            let _ = write!(
                out,
                r#"{{"all":{all},"ctors":{ctors},"isRec":{is_rec},"isReflexive":{is_reflexive},"isUnsafe":false,"levelParams":{lp},"name":{n},"numIndices":{num_indices},"numNested":{num_nested},"numParams":{num_params},"type":{t}}}"#
            );
        }
        out.push_str("]}}");
        self.line(&out)
    }
}

/// The constant `n` and the part of its kind that `pick` selects, or an error saying it is
/// not the `what` the referring constant claims.
fn lookup<'e, T>(
    env: &'e Env,
    n: NameId,
    what: &str,
    pick: impl Fn(&'e Kind) -> Option<&'e T>,
) -> Result<(&'e Const, &'e T)> {
    env.consts
        .get(&n)
        .and_then(|c| Some((c, pick(&c.kind)?)))
        .ok_or_else(|| corrupt(format!("{} is not a known {what}", env.display(n))))
}

const fn fresh(next: &mut u32) -> u32 {
    *next += 1;
    *next - 1
}

const fn binder(b: Binder) -> &'static str {
    match b {
        Binder::Default => "default",
        Binder::Implicit => "implicit",
        Binder::StrictImplicit => "strictImplicit",
        Binder::InstImplicit => "instImplicit",
    }
}

fn sep(s: &mut String, i: usize) {
    if i > 0 {
        s.push(',');
    }
}

fn json_list(ids: &[u32]) -> String {
    let mut s = String::from("[");
    for (i, id) in ids.iter().enumerate() {
        sep(&mut s, i);
        let _ = write!(s, "{id}");
    }
    s.push(']');
    s
}

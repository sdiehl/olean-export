use crate::{
    env::{
        Const, Ctor, Env, Expr, ExprId, Inductive, Kind, Level, LevelId, Name, NameId, Rec, ANON,
        ZERO,
    },
    error::{corrupt, Result},
    ndjson::Ndjson,
    record::{
        Binding, Counts, Decl, Head, IndCtor, IndRec, IndRule, IndType, Record, Safety, Sink,
    },
};
use rustc_hash::FxHashSet;
use std::io::Write;

const UNSEEN: u32 = u32::MAX;

/// Streams an [`Env`] in lean4export 3.1.0 order to a [`Sink`], NDJSON by default. Ids are
/// assigned on first use and every record only refers to records already written.
///
/// Exporting recurses once per nested subterm, which overflows the default stack on large
/// libraries such as Mathlib, so run it inside [`crate::with_big_stack`].
#[derive(Debug)]
pub struct Exporter<'a, S: Sink> {
    env: &'a Env,
    sink: S,
    names: Vec<u32>,
    levels: Vec<u32>,
    exprs: Vec<u32>,
    next: Counts,
    scanned: Vec<bool>,
    visited: FxHashSet<NameId>,
    nat: Option<NameId>,
    str_deps: [Option<NameId>; 2],
    quot: [Option<NameId>; 5],
}

impl<'a, W: Write> Exporter<'a, Ndjson<W>> {
    pub fn new(env: &'a Env, out: W) -> Self {
        Self::with_sink(env, Ndjson::new(out))
    }
}

impl<'a, S: Sink> Exporter<'a, S> {
    pub fn with_sink(env: &'a Env, sink: S) -> Self {
        let mut names = vec![UNSEEN; env.names.bound()];
        let mut levels = vec![UNSEEN; env.levels.bound()];
        names[ANON.index()] = 0;
        levels[ZERO.index()] = 0;
        let find = |s| env.find_name(s);
        Self {
            env,
            sink,
            names,
            levels,
            exprs: vec![UNSEEN; env.exprs.bound()],
            next: Counts::default(),
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
        }
    }

    pub fn meta(&mut self) -> Result<()> {
        let h = &self.env.header;
        let meta = format!(
            r#"{{"exporter":{{"name":"olean-export","version":"{}"}},"format":{{"version":"3.1.0"}},"lean":{{"githash":"{}","version":"{}"}}}}"#,
            env!("CARGO_PKG_VERSION"),
            h.githash,
            h.version
        );
        self.sink.record(&Record::Meta(meta.into()))
    }

    /// Export every non-internal constant in load order, like `lean4export` with no `--`.
    pub fn all(&mut self) -> Result<()> {
        self.env.roots().try_for_each(|c| self.constant(c))
    }

    #[must_use]
    pub const fn counts(&self) -> Counts {
        self.next
    }

    /// Write the end record and hand back the sink's output.
    pub fn finish(mut self) -> Result<S::Output> {
        self.sink.record(&Record::End(self.next))?;
        self.sink.finish()
    }

    fn name(&mut self, n: NameId) -> Result<u32> {
        if self.names[n.index()] != UNSEEN {
            return Ok(self.names[n.index()]);
        }
        let id = match &self.env.names[n] {
            Name::Anon => unreachable!(),
            Name::Str(p, s) => {
                let p = self.name(*p)?;
                self.emit(&Record::NameStr {
                    pre: p,
                    str: s.as_ref().into(),
                })?
            }
            Name::Num(p, i) => {
                let p = self.name(*p)?;
                self.emit(&Record::NameNum { pre: p, i: *i })?
            }
        };
        self.names[n.index()] = id;
        Ok(id)
    }

    fn name_list(&mut self, ns: &[NameId]) -> Result<Vec<u32>> {
        ns.iter().map(|&n| self.name(n)).collect()
    }

    fn level_params(&mut self, ps: &[NameId]) -> Result<Vec<u32>> {
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
        let r = match self.env.levels[l] {
            Level::Zero => unreachable!(),
            Level::Succ(a) => Record::Succ(self.level(a)?),
            Level::Max(a, b) => Record::Max(self.level(a)?, self.level(b)?),
            Level::IMax(a, b) => Record::IMax(self.level(a)?, self.level(b)?),
            Level::Param(n) => Record::Param(self.name(n)?),
        };
        let id = self.emit(&r)?;
        self.levels[l.index()] = id;
        Ok(id)
    }

    fn expr(&mut self, e: ExprId) -> Result<u32> {
        if self.exprs[e.index()] != UNSEEN {
            return Ok(self.exprs[e.index()]);
        }
        let env = self.env;
        let r = match &env.exprs[e] {
            Expr::BVar(i) => Record::BVar(*i),
            Expr::Sort(l) => Record::Sort(self.level(*l)?),
            Expr::Const(n, us) => Record::Const {
                name: self.name(*n)?,
                us: us.iter().map(|&u| self.level(u)).collect::<Result<_>>()?,
            },
            Expr::App(f, a) => Record::App {
                fun: self.expr(*f)?,
                arg: self.expr(*a)?,
            },
            Expr::Lam(n, t, b, bi) => Record::Lam(self.binding(*n, *t, *b, *bi)?),
            Expr::Pi(n, t, b, bi) => Record::Pi(self.binding(*n, *t, *b, *bi)?),
            Expr::Let(n, t, v, b) => {
                let (n, t, v, b) = (
                    self.name(*n)?,
                    self.expr(*t)?,
                    self.expr(*v)?,
                    self.expr(*b)?,
                );
                // Lean marks most `let`s nondep, but lean4export writes false for all of
                // them so that terms differing only in the flag share one index.
                Record::Let {
                    name: n,
                    ty: t,
                    value: v,
                    body: b,
                    nondep: false,
                }
            }
            Expr::Nat(v) => {
                if let Some(nat) = self.nat {
                    self.constant(nat)?;
                }
                Record::Nat(v.as_ref().into())
            }
            Expr::Str(v) => {
                for c in self.str_deps.into_iter().flatten() {
                    self.constant(c)?;
                }
                Record::Str(v.as_ref().into())
            }
            Expr::Proj(n, i, x) => {
                let (n, x) = (self.name(*n)?, self.expr(*x)?);
                Record::Proj {
                    type_name: n,
                    idx: *i,
                    struct_: x,
                }
            }
        };
        let id = self.emit(&r)?;
        self.exprs[e.index()] = id;
        Ok(id)
    }

    fn binding(
        &mut self,
        n: NameId,
        t: ExprId,
        b: ExprId,
        info: crate::env::Binder,
    ) -> Result<Binding> {
        Ok(Binding {
            info,
            name: self.name(n)?,
            ty: self.expr(t)?,
            body: self.expr(b)?,
        })
    }

    /// Write a name, level or expression record and return its id.
    fn emit(&mut self, r: &Record<'_>) -> Result<u32> {
        self.sink.record(r)?;
        Ok(self
            .next
            .assign(r)
            .expect("emit takes only id-bearing records"))
    }

    fn decl(&mut self, d: Decl) -> Result<()> {
        self.sink.record(&Record::Decl(d))
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
                let head = self.header(k)?;
                self.decl(Decl::Axiom {
                    head,
                    is_unsafe: false,
                    all: None,
                })
            }
            Kind::Defn(d) => {
                self.deps(k.ty)?;
                self.deps(d.value)?;
                let head = self.header(k)?;
                let value = self.expr(d.value)?;
                let all = self.name_list(&d.all)?;
                self.decl(Decl::Def {
                    head,
                    value,
                    hints: d.hints,
                    all,
                    safety: Safety::Safe,
                })
            }
            Kind::Thm(b) | Kind::Opaque(b) => {
                self.deps(k.ty)?;
                self.deps(b.value)?;
                let head = self.header(k)?;
                let value = self.expr(b.value)?;
                let all = self.name_list(&b.all)?;
                self.decl(if matches!(k.kind, Kind::Thm(_)) {
                    Decl::Thm { head, value, all }
                } else {
                    Decl::Opaque {
                        head,
                        value,
                        is_unsafe: false,
                        all: Some(all),
                    }
                })
            }
            Kind::Quot(_) => self.quot(),
            Kind::Induct(ind) => self.inductive(k, ind),
            Kind::Ctor(ctor) => self.constant(ctor.induct),
            Kind::Rec(rec) => rec.all.iter().try_for_each(|&i| self.constant(i)),
        }
    }

    fn header(&mut self, k: &Const) -> Result<Head> {
        Ok(Head {
            name: self.name(k.name)?,
            level_params: self.level_params(&k.level_params)?,
            ty: self.expr(k.ty)?,
        })
    }

    fn quot(&mut self) -> Result<()> {
        let env = self.env;
        let [eq, rest @ ..] = self.quot;
        if let Some(eq) = eq {
            self.constant(eq)?;
        }
        for c in rest.into_iter().flatten() {
            self.visited.insert(c);
            let (k, &kind) = lookup(env, c, "quotient", |k| match k {
                Kind::Quot(q) => Some(q),
                _ => None,
            })?;
            let head = self.header(k)?;
            self.decl(Decl::Quot { head, kind })?;
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
        let mut out_ctors = Vec::with_capacity(ctors.len());
        for &(c, ctor) in &ctors {
            let Ctor {
                induct,
                cidx,
                num_params,
                num_fields,
            } = *ctor;
            let head = self.header(c)?;
            out_ctors.push(IndCtor {
                head,
                is_unsafe: false,
                induct: self.name(induct)?,
                cidx,
                num_params,
                num_fields,
            });
        }
        let mut out_recs = Vec::with_capacity(recs.len());
        for &(r, rec) in &recs {
            let Rec {
                all,
                num_params,
                num_indices,
                num_motives,
                num_minors,
                rules,
                k,
            } = rec;
            let head = self.header(r)?;
            let all = self.name_list(all)?;
            let rules = rules
                .iter()
                .map(|rule| {
                    Ok(IndRule {
                        ctor: self.name(rule.ctor)?,
                        nfields: rule.nfields,
                        rhs: self.expr(rule.rhs)?,
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            out_recs.push(IndRec {
                head,
                is_unsafe: false,
                all,
                num_params: *num_params,
                num_indices: *num_indices,
                num_motives: *num_motives,
                num_minors: *num_minors,
                rules,
                k: *k,
            });
        }
        let mut out_types = Vec::with_capacity(types.len());
        for &(ty, ind) in &types {
            let Inductive {
                num_params,
                num_indices,
                all,
                ctors,
                num_nested,
                is_rec,
                is_reflexive,
            } = ind;
            let head = self.header(ty)?;
            let (all, ctors) = (self.name_list(all)?, self.name_list(ctors)?);
            out_types.push(IndType {
                head,
                is_unsafe: false,
                num_params: *num_params,
                num_indices: *num_indices,
                all,
                ctors,
                num_nested: *num_nested,
                is_rec: *is_rec,
                is_reflexive: *is_reflexive,
            });
        }
        self.decl(Decl::Inductive {
            types: out_types,
            ctors: out_ctors,
            recs: out_recs,
        })
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

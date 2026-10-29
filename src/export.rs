use crate::{
    env::{
        Binder, Body, Const, Ctor, Defn, Env, Expr, ExprId, Inductive, Kind, Level, LevelId, Name,
        NameId, Rec, Reload, ANON, ZERO,
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

/// Where an export stopped, so that a later one on the same [`Env`], reloaded or not,
/// continues its ids and writes only records the earlier one did not.
#[derive(Debug)]
pub struct Mark {
    lineage: u64,
    names: Vec<u32>,
    levels: Vec<u32>,
    exprs: Vec<u32>,
    scanned: Vec<bool>,
    visited: FxHashSet<NameId>,
    next: Counts,
}

impl Mark {
    fn fresh(env: &Env) -> Self {
        let mut names = vec![UNSEEN; env.names.bound()];
        let mut levels = vec![UNSEEN; env.levels.bound()];
        names[ANON.index()] = 0;
        levels[ZERO.index()] = 0;
        Self {
            lineage: env.lineage,
            names,
            levels,
            exprs: Vec::new(),
            scanned: Vec::new(),
            visited: FxHashSet::default(),
            next: Counts::default(),
        }
    }
}

/// Streams an [`Env`] in lean4export 3.1.0 order to a [`Sink`], NDJSON by default. Ids are
/// assigned on first use and every record only refers to records already written.
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

/// One step of [`Exporter::constant`]'s depth-first walk over dependencies.
enum Task {
    Const(NameId),
    Scan(ExprId),
    Scanned(ExprId),
    Emit(NameId),
}

/// The constants of one mutual inductive block.
struct Family<'e> {
    types: Vec<(&'e Const, &'e Inductive)>,
    ctors: Vec<(&'e Const, &'e Ctor)>,
    recs: Vec<(&'e Const, &'e Rec)>,
}

impl<'e> Family<'e> {
    fn consts(&self) -> impl DoubleEndedIterator<Item = &'e Const> + '_ {
        let (t, c, r) = (&self.types, &self.ctors, &self.recs);
        let ctors = c.iter().map(|&(k, _)| k);
        let recs = r.iter().map(|&(k, _)| k);
        t.iter().map(|&(k, _)| k).chain(ctors).chain(recs)
    }

    /// Every term of the block, in the order lean4export visits them.
    fn terms(&self) -> impl DoubleEndedIterator<Item = ExprId> + '_ {
        let rules = self
            .recs
            .iter()
            .flat_map(|(_, r)| r.rules.iter().map(|rule| rule.rhs));
        self.consts().map(|k| k.ty).chain(rules)
    }
}

impl<'a, W: Write> Exporter<'a, Ndjson<W>> {
    pub fn new(env: &'a Env, out: W) -> Self {
        Self::with_sink(env, Ndjson::new(out))
    }
}

impl<'a, S: Sink> Exporter<'a, S> {
    pub fn with_sink(env: &'a Env, sink: S) -> Self {
        Self::from_mark(env, sink, Mark::fresh(env))
    }

    /// Continue the export `mark` was taken from, on the same environment.
    pub fn resume(env: &'a Env, sink: S, mark: Mark) -> Result<Self> {
        if mark.lineage != env.lineage {
            return Err(corrupt("the mark is from another environment"));
        }
        Ok(Self::from_mark(env, sink, mark))
    }

    fn from_mark(env: &'a Env, sink: S, mut m: Mark) -> Self {
        m.names.resize(env.names.bound(), UNSEEN);
        m.levels.resize(env.levels.bound(), UNSEEN);
        m.exprs.resize(env.exprs.bound(), UNSEEN);
        m.scanned.resize(env.exprs.bound(), false);
        let find = |s| env.find_name(s);
        Self {
            env,
            sink,
            names: m.names,
            levels: m.levels,
            exprs: m.exprs,
            next: m.next,
            scanned: m.scanned,
            visited: m.visited,
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
    pub fn finish(self) -> Result<S::Output> {
        self.suspend().map(|(out, _)| out)
    }

    /// Like [`Exporter::finish`], with a [`Mark`] to [`Exporter::resume`] from.
    pub fn suspend(mut self) -> Result<(S::Output, Mark)> {
        self.sink.record(&Record::End(self.next))?;
        let mark = Mark {
            lineage: self.env.lineage,
            names: self.names,
            levels: self.levels,
            exprs: self.exprs,
            scanned: self.scanned,
            visited: self.visited,
            next: self.next,
        };
        Ok((self.sink.finish()?, mark))
    }

    /// After [`Env::reload`], export the reloaded constants again as [`Exporter::all`] would.
    /// The end record counts every record since the first export.
    pub fn update(&mut self, r: &Reload) -> Result<()> {
        for c in r.consts.iter().chain(&r.removed) {
            self.visited.remove(c);
        }
        let env = self.env;
        r.consts
            .iter()
            .filter(|&&c| !env.is_internal(c))
            .try_for_each(|&c| self.constant(c))
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

    /// Export `root` after its subterms. The worklist visits each term twice: first to
    /// export the names and levels it mentions and queue its subterms, then to write it.
    fn expr(&mut self, root: ExprId) -> Result<u32> {
        let env = self.env;
        let mut work = vec![(root, false)];
        while let Some((e, ready)) = work.pop() {
            if self.exprs[e.index()] != UNSEEN {
                continue;
            }
            let x = &env.exprs[e];
            if !ready {
                work.push((e, true));
                match x {
                    Expr::BVar(_) => {}
                    Expr::Sort(l) => {
                        self.level(*l)?;
                    }
                    Expr::Const(n, us) => {
                        self.name(*n)?;
                        us.iter().try_for_each(|&u| self.level(u).map(drop))?;
                    }
                    Expr::App(f, a) => work.extend([(*a, false), (*f, false)]),
                    Expr::Lam(n, t, b, _) | Expr::Pi(n, t, b, _) => {
                        self.name(*n)?;
                        work.extend([(*b, false), (*t, false)]);
                    }
                    Expr::Let(n, t, v, b) => {
                        self.name(*n)?;
                        work.extend([(*b, false), (*v, false), (*t, false)]);
                    }
                    Expr::Nat(_) => {
                        if let Some(nat) = self.nat {
                            self.constant(nat)?;
                        }
                    }
                    Expr::Str(_) => {
                        for c in self.str_deps.into_iter().flatten() {
                            self.constant(c)?;
                        }
                    }
                    Expr::Proj(n, _, x) => {
                        self.name(*n)?;
                        work.push((*x, false));
                    }
                }
                continue;
            }
            let (names, levels, exprs) = (&self.names, &self.levels, &self.exprs);
            let name = |n: &NameId| names[n.index()];
            let level = |l: &LevelId| levels[l.index()];
            let expr = |e: &ExprId| exprs[e.index()];
            let bind = |n: &NameId, t: &ExprId, b: &ExprId, bi: &Binder| Binding {
                info: *bi,
                name: name(n),
                ty: expr(t),
                body: expr(b),
            };
            let r = match x {
                Expr::BVar(i) => Record::BVar(*i),
                Expr::Sort(l) => Record::Sort(level(l)),
                Expr::Const(n, us) => Record::Const {
                    name: name(n),
                    us: us.iter().map(level).collect(),
                },
                Expr::App(f, a) => Record::App {
                    fun: expr(f),
                    arg: expr(a),
                },
                Expr::Lam(n, t, b, bi) => Record::Lam(bind(n, t, b, bi)),
                Expr::Pi(n, t, b, bi) => Record::Pi(bind(n, t, b, bi)),
                // Lean marks most `let`s nondep, but lean4export writes false for all of
                // them so that terms differing only in the flag share one index.
                Expr::Let(n, t, v, b) => Record::Let {
                    name: name(n),
                    ty: expr(t),
                    value: expr(v),
                    body: expr(b),
                    nondep: false,
                },
                Expr::Nat(v) => Record::Nat(v.as_ref().into()),
                Expr::Str(v) => Record::Str(v.as_ref().into()),
                Expr::Proj(n, i, x) => Record::Proj {
                    type_name: name(n),
                    idx: *i,
                    struct_: expr(x),
                },
            };
            let id = self.emit(&r)?;
            self.exprs[e.index()] = id;
        }
        Ok(self.exprs[root.index()])
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

    /// Export a constant and, first, everything it mentions. Dependencies are walked
    /// depth-first on an explicit stack, so no term depth or dependency chain can overflow
    /// the thread's stack.
    pub fn constant(&mut self, c: NameId) -> Result<()> {
        let env = self.env;
        let mut work = vec![Task::Const(c)];
        while let Some(task) = work.pop() {
            match task {
                Task::Scan(e) => {
                    if self.scanned[e.index()] {
                        continue;
                    }
                    work.push(Task::Scanned(e));
                    match &env.exprs[e] {
                        Expr::Const(n, _) => work.push(Task::Const(*n)),
                        Expr::App(a, b) | Expr::Lam(_, a, b, _) | Expr::Pi(_, a, b, _) => {
                            work.extend([Task::Scan(*b), Task::Scan(*a)]);
                        }
                        Expr::Let(_, t, v, b) => {
                            work.extend([Task::Scan(*b), Task::Scan(*v), Task::Scan(*t)]);
                        }
                        Expr::Proj(_, _, x) => work.push(Task::Scan(*x)),
                        Expr::BVar(_) | Expr::Sort(_) | Expr::Nat(_) | Expr::Str(_) => {}
                    }
                }
                Task::Scanned(e) => self.scanned[e.index()] = true,
                Task::Const(c) => {
                    if !self.visited.insert(c) {
                        continue;
                    }
                    let Some(k) = env.consts.get(&c) else {
                        continue;
                    };
                    match &k.kind {
                        Kind::Axiom => work.extend([Task::Emit(c), Task::Scan(k.ty)]),
                        Kind::Defn(Defn { value, .. })
                        | Kind::Thm(Body { value, .. })
                        | Kind::Opaque(Body { value, .. }) => {
                            work.extend([Task::Emit(c), Task::Scan(*value), Task::Scan(k.ty)]);
                        }
                        Kind::Quot(_) => {
                            work.push(Task::Emit(c));
                            work.extend(self.quot[0].map(Task::Const));
                        }
                        Kind::Induct(ind) => {
                            let fam = self.family(k, ind)?;
                            self.visited.extend(fam.consts().map(|k| k.name));
                            work.push(Task::Emit(c));
                            work.extend(fam.terms().rev().map(Task::Scan));
                        }
                        Kind::Ctor(ctor) => work.push(Task::Const(ctor.induct)),
                        Kind::Rec(rec) => {
                            work.extend(rec.all.iter().rev().map(|&i| Task::Const(i)));
                        }
                    }
                }
                Task::Emit(c) => self.write(c)?,
            }
        }
        Ok(())
    }

    /// Write the declaration of `c`, whose dependencies are already out.
    fn write(&mut self, c: NameId) -> Result<()> {
        let k = &self.env.consts[&c];
        match &k.kind {
            Kind::Axiom => {
                let head = self.header(k)?;
                self.decl(Decl::Axiom {
                    head,
                    is_unsafe: false,
                    all: None,
                })
            }
            Kind::Defn(d) => {
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
            Kind::Ctor(_) | Kind::Rec(_) => unreachable!("exported through their inductive"),
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
        let [_, rest @ ..] = self.quot;
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

    /// The mutual block of `base`: its types, their constructors and their recursors.
    fn family(&self, base: &Const, ind: &Inductive) -> Result<Family<'a>> {
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
        let ctors = types
            .iter()
            .flat_map(|(_, i)| &i.ctors)
            .map(|&c| {
                lookup(env, c, "constructor", |k| match k {
                    Kind::Ctor(c) => Some(c),
                    _ => None,
                })
            })
            .collect::<Result<Vec<_>>>()?;
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
        Ok(Family { types, ctors, recs })
    }

    fn inductive(&mut self, base: &Const, ind: &Inductive) -> Result<()> {
        let Family { types, ctors, recs } = self.family(base, ind)?;
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

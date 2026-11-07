use crate::{
    env::{
        Binder, Builtins, Const, Ctor, Dep, Depth, Env, Expr, ExprId, Family, Inductive, Kind,
        Level, LevelId, Name, NameId, Rec, Reload, ANON, ZERO,
    },
    error::{corrupt, Error, Result},
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
    builtins: Builtins,
    depth: Depth,
}

/// One step of [`Exporter::constant`]'s depth-first walk over dependencies.
enum Task {
    Const(NameId),
    Scan(ExprId),
    Scanned(ExprId),
    Emit(NameId),
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
            return Err(Error::Misuse("the mark is from another environment"));
        }
        Ok(Self::from_mark(env, sink, mark))
    }

    fn from_mark(env: &'a Env, sink: S, mut m: Mark) -> Self {
        m.names.resize(env.names.bound(), UNSEEN);
        m.levels.resize(env.levels.bound(), UNSEEN);
        m.exprs.resize(env.exprs.bound(), UNSEEN);
        m.scanned.resize(env.exprs.bound(), false);
        Self {
            env,
            sink,
            names: m.names,
            levels: m.levels,
            exprs: m.exprs,
            next: m.next,
            scanned: m.scanned,
            visited: m.visited,
            builtins: Builtins::find(env),
            depth: Depth::Full,
        }
    }

    /// Write every theorem as an axiom over its type, so an environment from
    /// [`Env::load_statements`] exports its statements and what they rest on, with no
    /// proofs.
    #[must_use]
    pub const fn statements(mut self) -> Self {
        self.depth = Depth::Statements;
        self
    }

    pub fn meta(&mut self) -> Result<()> {
        let h = &self.env.header;
        let meta = serde_json::json!({
            "exporter": {"name": "olean-export", "version": env!("CARGO_PKG_VERSION")},
            "format": {"version": "3.1.0"},
            "lean": {"githash": h.githash, "version": h.version},
        });
        self.sink
            .record(None, &Record::Meta(meta.to_string().into()))
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
        self.sink.record(None, &Record::End(self.next))?;
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
    /// An internal constant is written again if it was written before, since terms
    /// already scanned will not lead back to it.
    pub fn update(&mut self, r: &Reload) -> Result<()> {
        for c in &r.removed {
            self.visited.remove(c);
        }
        let env = self.env;
        let again: Vec<NameId> = r
            .consts
            .iter()
            .copied()
            .filter(|c| self.visited.remove(c) | !env.is_internal(*c))
            .collect();
        again.into_iter().try_for_each(|c| self.constant(c))
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
                    Expr::Nat(_) | Expr::Str(_) => {
                        let mut lits = Vec::new();
                        self.env.children(e, &self.builtins, |d| lits.push(d));
                        for d in lits {
                            if let Dep::Literal(c) = d {
                                self.constant(c)?;
                            }
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
        let id = self.next.assign(r);
        self.sink.record(id, r)?;
        Ok(id.expect("emit takes only id-bearing records"))
    }

    fn decl(&mut self, d: Decl) -> Result<()> {
        self.sink.record(None, &Record::Decl(d))
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
                    if !self.scanned[e.index()] {
                        work.push(Task::Scanned(e));
                        let at = work.len();
                        env.children(e, &self.builtins, |d| match d {
                            Dep::Expr(x) => work.push(Task::Scan(x)),
                            Dep::Const(c) => work.push(Task::Const(c)),
                            Dep::Member(_) | Dep::Literal(_) | Dep::Unloaded(_) => {}
                        });
                        work[at..].reverse();
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
                    if !matches!(k.kind, Kind::Ctor(_) | Kind::Rec(_)) {
                        work.push(Task::Emit(c));
                    }
                    let at = work.len();
                    let mut unloaded = None;
                    env.mentions(k, self.depth, &self.builtins, |d| match d {
                        Dep::Expr(e) => work.push(Task::Scan(e)),
                        Dep::Const(c) => work.push(Task::Const(c)),
                        Dep::Member(c) => {
                            self.visited.insert(c);
                        }
                        Dep::Literal(_) => {}
                        Dep::Unloaded(c) => unloaded = Some(c),
                    })?;
                    if let Some(c) = unloaded {
                        return Err(corrupt(format!(
                            "the value of {} was not loaded",
                            env.display(c)
                        )));
                    }
                    work[at..].reverse();
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
            Kind::Thm(_) if self.depth == Depth::Statements => {
                let head = self.header(k)?;
                self.decl(Decl::Axiom {
                    head,
                    is_unsafe: false,
                    all: None,
                })
            }
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
            Kind::Thm(t) => {
                let head = self.header(k)?;
                let value = self.expr(t.value.expect("scanned"))?;
                let all = self.name_list(&t.all)?;
                self.decl(Decl::Thm { head, value, all })
            }
            Kind::Opaque(b) => {
                let head = self.header(k)?;
                let value = self.expr(b.value)?;
                let all = self.name_list(&b.all)?;
                self.decl(Decl::Opaque {
                    head,
                    value,
                    is_unsafe: false,
                    all: Some(all),
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
        let [_, rest @ ..] = self.builtins.quot;
        for c in rest.into_iter().flatten() {
            let (k, &kind) = env.lookup(c, "quotient", |k| match k {
                Kind::Quot(q) => Some(q),
                _ => None,
            })?;
            let head = self.header(k)?;
            self.decl(Decl::Quot { head, kind })?;
        }
        Ok(())
    }

    fn inductive(&mut self, base: &Const, ind: &Inductive) -> Result<()> {
        let Family { types, ctors, recs } = self.env.family(base, ind)?;
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

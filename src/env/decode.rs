use super::{
    escape,
    reload::Live,
    table::Tables,
    term::{
        Binder, Body, Const, Ctor, Defn, Expr, ExprId, Hints, Id, Inductive, Kind, Level, LevelId,
        Name, NameId, QuotKind, Rec, Rule, Theorem, ANON, ZERO,
    },
    Env,
};
use crate::{
    error::{at, corrupt, Error, Result},
    inspect::Import,
    olean::{
        is_scalar, small_nat, Header, Image, Safety, AXIOM, CTOR, DEFN, INDUCT, OPAQUE, QUOT, REC,
        THM,
    },
};
use rayon::prelude::*;
use rustc_hash::FxHashMap;
use std::{
    path::Path,
    sync::atomic::{AtomicUsize, Ordering::Relaxed},
};

/// What one module adds besides table entries.
pub(super) struct Module {
    pub(super) consts: Vec<Const>,
    pub(super) recursors: FxHashMap<NameId, Vec<NameId>>,
    pub(super) skipped: usize,
    pub(super) header: Header,
    pub(super) imports: Vec<Import>,
    pub(super) exported: Option<FxHashMap<NameId, bool>>,
    /// Theorems whose values were left in the olean, with the values' addresses.
    pub(super) pending: Vec<(NameId, u64)>,
}

fn decode(
    tables: &Tables,
    rank: u32,
    cursor: &mut Option<usize>,
    path: &Path,
    lazy: bool,
) -> Result<Module> {
    let img = Image::open_module(path)?;
    let mut dec = Decoder::new(&img, tables, rank, cursor, lazy);
    dec.run().map_err(at(path))?;
    dec.module.imports = img.imports().map_err(at(path))?;
    Ok(dec.module)
}

/// Decode the modules at `paths`, each with its rank in import order, on `jobs` threads.
pub(super) fn decode_all(
    tables: &Tables,
    paths: &[(usize, &Path)],
    jobs: usize,
    progress: &(dyn Fn(usize, usize) + Sync),
    lazy: bool,
) -> Result<Vec<Module>> {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(jobs.max(1))
        .build()?;
    let (done, consts) = (AtomicUsize::new(0), AtomicUsize::new(0));
    pool.install(|| {
        paths
            .par_iter()
            .map_init(
                || None,
                |cursor, &(rank, path)| {
                    let rank = u32::try_from(rank).expect("module count");
                    let m = decode(tables, rank, cursor, path, lazy)?;
                    let n = consts.fetch_add(m.consts.len(), Relaxed) + m.consts.len();
                    progress(done.fetch_add(1, Relaxed) + 1, n);
                    Ok(m)
                },
            )
            .collect()
    })
}

impl Image {
    pub(crate) fn imports(&self) -> Result<Vec<Import>> {
        let imports = self.array(self.field(self.root, 0)?)?;
        imports
            .into_iter()
            .map(|i| {
                Ok(Import {
                    module: self.str_name(self.field(i, 0)?)?,
                    all: self.scalar_u8(i, 0)? != 0,
                    exported: self.scalar_u8(i, 1)? != 0,
                    meta: self.scalar_u8(i, 2)? != 0,
                })
            })
            .collect()
    }

    pub(crate) fn str_name(&self, o: u64) -> Result<String> {
        self.join_name(o, false)
    }

    /// The name at `o` as [`Env::display`] writes it.
    pub(crate) fn display_name(&self, o: u64) -> Result<String> {
        self.join_name(o, true)
    }

    fn join_name(&self, mut o: u64, escaped: bool) -> Result<String> {
        let mut parts = Vec::new();
        while !is_scalar(o) && self.tag(o)? != 0 {
            parts.push(if self.tag(o)? == 1 {
                let s = self.str(self.field(o, 1)?)?;
                if escaped {
                    escape(s).into_owned()
                } else {
                    s.to_owned()
                }
            } else {
                self.nat_decimal(self.field(o, 1)?)?
            });
            o = self.field(o, 0)?;
        }
        parts.reverse();
        Ok(parts.join("."))
    }
}

/// Translates one module's objects into the shared tables, memoized by address since the
/// compactor already maximally shares structurally equal objects within a module.
struct Decoder<'a> {
    img: &'a Image,
    tables: &'a Tables,
    /// The module's position in import order.
    rank: u32,
    /// The expression chunk this thread is filling.
    cursor: &'a mut Option<usize>,
    module: Module,
    /// Table id plus one for each decoded object, by slot. An object is only ever decoded as
    /// one of name, level or expression, so the kinds can share it.
    memo: Vec<u32>,
    /// Leave theorem values in the olean.
    lazy: bool,
}

/// The memo mark of an expression whose subterms are still being decoded.
const PENDING: u32 = u32::MAX;

impl<'a> Decoder<'a> {
    fn new(
        img: &'a Image,
        tables: &'a Tables,
        rank: u32,
        cursor: &'a mut Option<usize>,
        lazy: bool,
    ) -> Self {
        Self {
            img,
            tables,
            rank,
            cursor,
            memo: vec![0; img.slots()],
            module: Module {
                consts: Vec::new(),
                recursors: FxHashMap::default(),
                skipped: 0,
                header: img.header.clone(),
                imports: Vec::new(),
                exported: None,
                pending: Vec::new(),
            },
            lazy,
        }
    }

    fn run(&mut self) -> Result<()> {
        let img = self.img;
        for c in img.array(img.field(img.root, 2)?)? {
            self.constant(c)?;
        }
        if img.parts.len() > 1 {
            self.exported()?;
        }
        Ok(())
    }

    /// The public part holds a hidden proof or body as an axiom over the same type.
    fn exported(&mut self) -> Result<()> {
        let img = self.img;
        let own: FxHashMap<NameId, usize> = (self.module.consts.iter().map(|c| c.name))
            .zip(0..)
            .collect();
        let mut exported = FxHashMap::default();
        for info in img.array(img.field(img.public, 2)?)? {
            if img.safety(info)? != Safety::Safe {
                continue;
            }
            let cv = img.field(img.field(info, 0)?, 0)?;
            let name = self.name(img.field(cv, 0)?)?;
            let Some(&i) = own.get(&name) else { continue };
            let ty = self.expr(img.field(cv, 2)?)?;
            let k = &self.module.consts[i];
            if ty != k.ty {
                return Err(corrupt("a constant is exported at another type"));
            }
            let hidden = img.tag(info)? == AXIOM && !matches!(k.kind, Kind::Axiom);
            exported.insert(name, hidden);
        }
        self.module.exported = Some(exported);
        Ok(())
    }

    /// The memo slot of `o`, and its id if it was already decoded.
    fn seen<T>(&self, o: u64) -> Result<(usize, Option<Id<T>>)> {
        let slot = self.img.slot(o)?;
        Ok((slot, self.memo[slot].checked_sub(1).map(Id::new)))
    }

    fn remember<T>(&mut self, slot: usize, id: Id<T>) -> Id<T> {
        self.memo[slot] = id.0 + 1;
        id
    }

    fn name(&mut self, o: u64) -> Result<NameId> {
        let img = self.img;
        if is_scalar(o) || img.tag(o)? == 0 {
            return Ok(ANON);
        }
        let (slot, seen) = self.seen(o)?;
        if let Some(id) = seen {
            return Ok(id);
        }
        let pre = self.name(img.field(o, 0)?)?;
        let arg = img.field(o, 1)?;
        let n = match img.tag(o)? {
            1 => Name::Str(pre, img.str(arg)?.into()),
            _ => Name::Num(pre, small_nat(arg)?),
        };
        let id = self.tables.names.intern(n);
        Ok(self.remember(slot, id))
    }

    fn names(&mut self, o: u64) -> Result<Vec<NameId>> {
        self.img
            .list(o)?
            .into_iter()
            .map(|n| self.name(n))
            .collect()
    }

    fn level(&mut self, o: u64) -> Result<LevelId> {
        let img = self.img;
        if is_scalar(o) || img.tag(o)? == 0 {
            return Ok(ZERO);
        }
        let (slot, seen) = self.seen(o)?;
        if let Some(id) = seen {
            return Ok(id);
        }
        let f = |i| img.field(o, i);
        let l = match img.tag(o)? {
            1 => Level::Succ(self.level(f(0)?)?),
            2 => Level::Max(self.level(f(0)?)?, self.level(f(1)?)?),
            3 => Level::IMax(self.level(f(0)?)?, self.level(f(1)?)?),
            4 => Level::Param(self.name(f(0)?)?),
            t => return Err(corrupt(format!("unexpected level tag {t}"))),
        };
        let id = self.tables.levels.intern(l);
        Ok(self.remember(slot, id))
    }

    /// Decode `root` after its subterms, on a worklist rather than the stack. A slot is
    /// [`PENDING`] while its subterms are queued, which catches cyclic images.
    fn expr(&mut self, root: u64) -> Result<ExprId> {
        let img = self.img;
        let mut work = vec![(root, false)];
        while let Some((o, ready)) = work.pop() {
            let slot = img.slot(o)?;
            let f = |i| img.field(o, i);
            let tag = img.tag(o)?;
            if !ready {
                match self.memo[slot] {
                    0 => {}
                    PENDING => return Err(corrupt("cyclic expression")),
                    _ => continue,
                }
                self.memo[slot] = PENDING;
                work.push((o, true));
                let subs: &[u64] = match tag {
                    5 => &[0, 1],
                    6 | 7 => &[1, 2],
                    8 => &[1, 2, 3],
                    10 => &[1],
                    11 => &[2],
                    _ => &[],
                };
                for &i in subs.iter().rev() {
                    work.push((f(i)?, false));
                }
                continue;
            }
            let binder = || {
                Ok::<_, Error>(match img.scalar_u8(o, 8)? {
                    0 => Binder::Default,
                    1 => Binder::Implicit,
                    2 => Binder::StrictImplicit,
                    _ => Binder::InstImplicit,
                })
            };
            let e = match tag {
                0 => Expr::BVar(small_nat(f(0)?)?),
                3 => Expr::Sort(self.level(f(0)?)?),
                4 => {
                    let us = img.list(f(1)?)?;
                    let us = us
                        .into_iter()
                        .map(|l| self.level(l))
                        .collect::<Result<_>>()?;
                    Expr::Const(self.name(f(0)?)?, us)
                }
                5 => Expr::App(self.done(f(0)?)?, self.done(f(1)?)?),
                6 => Expr::Lam(
                    self.name(f(0)?)?,
                    self.done(f(1)?)?,
                    self.done(f(2)?)?,
                    binder()?,
                ),
                7 => Expr::Pi(
                    self.name(f(0)?)?,
                    self.done(f(1)?)?,
                    self.done(f(2)?)?,
                    binder()?,
                ),
                8 => Expr::Let(
                    self.name(f(0)?)?,
                    self.done(f(1)?)?,
                    self.done(f(2)?)?,
                    self.done(f(3)?)?,
                ),
                9 => {
                    let lit = f(0)?;
                    let val = img.field(lit, 0)?;
                    if img.tag(lit)? == 0 {
                        Expr::Nat(img.nat_decimal(val)?.into())
                    } else {
                        Expr::Str(img.str(val)?.into())
                    }
                }
                10 => {
                    let id = self.done(f(1)?)?;
                    self.remember(slot, id);
                    continue;
                }
                11 => Expr::Proj(self.name(f(0)?)?, small_nat(f(1)?)?, self.done(f(2)?)?),
                t => {
                    return Err(corrupt(format!(
                        "unexpected expression tag {t} (free or meta variable in a declaration)"
                    )))
                }
            };
            let id = self.tables.exprs.intern(e, self.rank, self.cursor);
            self.remember(slot, id);
        }
        self.done(root)
    }

    /// The id of an already decoded subterm.
    fn done(&self, o: u64) -> Result<ExprId> {
        self.seen(o)?
            .1
            .ok_or_else(|| corrupt("subterm decoded out of order"))
    }

    fn constant(&mut self, info: u64) -> Result<()> {
        let img = self.img;
        let tag = img.tag(info)?;
        let val = img.field(info, 0)?;
        if img.safety(info)? != Safety::Safe {
            self.module.skipped += 1;
            return Ok(());
        }
        let f = |i| img.field(val, i);
        let nat = |i| small_nat(f(i)?);
        let cv = f(0)?;
        let name = self.name(img.field(cv, 0)?)?;
        let level_params = self.names(img.field(cv, 1)?)?;
        for &p in &level_params {
            self.tables.levels.intern(Level::Param(p));
        }
        let ty = self.expr(img.field(cv, 2)?)?;
        let kind = match tag {
            AXIOM => Kind::Axiom,
            DEFN => {
                let h = f(2)?;
                let hints = if !is_scalar(h) {
                    Hints::Regular(img.scalar_u32(h)?)
                } else if h >> 1 == 0 {
                    Hints::Opaque
                } else {
                    Hints::Abbrev
                };
                Kind::Defn(Defn {
                    value: self.expr(f(1)?)?,
                    hints,
                    all: self.names(f(3)?)?,
                })
            }
            THM => Kind::Thm(Theorem {
                value: if self.lazy {
                    self.module.pending.push((name, f(1)?));
                    None
                } else {
                    Some(self.expr(f(1)?)?)
                },
                all: self.names(f(2)?)?,
            }),
            OPAQUE => Kind::Opaque(Body {
                value: self.expr(f(1)?)?,
                all: self.names(f(2)?)?,
            }),
            QUOT => Kind::Quot(match img.scalar_u8(val, 0)? {
                0 => QuotKind::Type,
                1 => QuotKind::Ctor,
                2 => QuotKind::Lift,
                _ => QuotKind::Ind,
            }),
            INDUCT => Kind::Induct(Inductive {
                num_params: nat(1)?,
                num_indices: nat(2)?,
                all: self.names(f(3)?)?,
                ctors: self.names(f(4)?)?,
                num_nested: nat(5)?,
                is_rec: img.scalar_u8(val, 0)? != 0,
                is_reflexive: img.scalar_u8(val, 2)? != 0,
            }),
            CTOR => Kind::Ctor(Ctor {
                induct: self.name(f(1)?)?,
                cidx: nat(2)?,
                num_params: nat(3)?,
                num_fields: nat(4)?,
            }),
            REC => {
                let all = self.names(f(1)?)?;
                for &ind in &all {
                    self.module.recursors.entry(ind).or_default().push(name);
                }
                let mut rules = Vec::new();
                for r in img.list(f(6)?)? {
                    rules.push(Rule {
                        ctor: self.name(img.field(r, 0)?)?,
                        nfields: small_nat(img.field(r, 1)?)?,
                        rhs: self.expr(img.field(r, 2)?)?,
                    });
                }
                Kind::Rec(Rec {
                    all,
                    num_params: nat(2)?,
                    num_indices: nat(3)?,
                    num_motives: nat(4)?,
                    num_minors: nat(5)?,
                    rules,
                    k: img.scalar_u8(val, 0)? != 0,
                })
            }
            t => return Err(corrupt(format!("unexpected constant tag {t}"))),
        };
        self.module.consts.push(Const {
            name,
            level_params,
            ty,
            kind,
        });
        Ok(())
    }
}

impl Env {
    /// Decode the theorem values `due`, sorted by module, into the tables.
    pub(super) fn decode_values(
        &mut self,
        live: &mut Live,
        due: &[((usize, u64), NameId)],
    ) -> Result<Vec<(NameId, ExprId)>> {
        let tables = self.thaw(live);
        let groups: Vec<_> = due.chunk_by(|a, b| a.0 .0 == b.0 .0).collect();
        let loaded = &live.loaded;
        let decoded = rayon::ThreadPoolBuilder::new()
            .num_threads(live.jobs.max(1))
            .build()
            .map_err(Error::from)
            .and_then(|pool| {
                pool.install(|| {
                    groups
                        .par_iter()
                        .map_init(
                            || None,
                            |cursor, group| {
                                let path = &loaded[group[0].0 .0].path;
                                let img = Image::open_module(path)?;
                                let rank = u32::try_from(group[0].0 .0).expect("module count");
                                let mut dec = Decoder::new(&img, &tables, rank, cursor, false);
                                group
                                    .iter()
                                    .map(|&((_, o), n)| Ok((n, dec.expr(o)?)))
                                    .collect::<Result<Vec<_>>>()
                                    .map_err(at(path))
                            },
                        )
                        .collect::<Result<Vec<_>>>()
                })
            });
        self.freeze(tables, live);
        Ok(decoded?.into_iter().flatten().collect())
    }
}

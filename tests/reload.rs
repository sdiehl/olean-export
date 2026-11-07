use olean_export::{
    ndjson::{self, Ndjson},
    Env, Exporter, Record, Result, Sink,
};
use std::{env, fs, path::PathBuf, process};

fn cases() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases/build")
}

#[derive(Default)]
struct Tally {
    records: usize,
    decls: usize,
}

impl Sink for &mut Tally {
    type Output = ();
    fn record(&mut self, _: Option<u32>, r: &Record<'_>) -> Result<()> {
        self.records += 1;
        self.decls += usize::from(matches!(r, Record::Decl(_)));
        Ok(())
    }
    fn finish(self) -> Result<()> {
        Ok(())
    }
}

fn full(env: &Env) -> String {
    let mut ex = Exporter::new(env, Vec::new());
    ex.meta().unwrap();
    ex.all().unwrap();
    String::from_utf8(ex.finish().unwrap()).unwrap()
}

fn decls(env: &Env) -> usize {
    let mut t = Tally::default();
    let mut ex = Exporter::with_sink(env, &mut t);
    ex.all().unwrap();
    ex.finish().unwrap();
    t.decls
}

fn scratch(name: &str, top: &str) -> PathBuf {
    let dir = env::temp_dir().join(format!("olean-export-{name}-{}", process::id()));
    fs::create_dir_all(&dir).unwrap();
    for m in ["Base", top] {
        let olean = format!("{m}.olean");
        fs::copy(cases().join(&olean), dir.join(&olean)).unwrap();
    }
    dir
}

#[test]
fn reload_writes_only_the_changed_module() {
    let dir = scratch("reload", "Top");
    let search = [dir.clone()];
    let mut env = Env::open(&search, &["Top"], 2).unwrap();
    let mut ex = Exporter::new(&env, Vec::new());
    ex.all().unwrap();
    let (_, mark) = ex.suspend().unwrap();
    assert!(env.reload().unwrap().is_empty());

    fs::copy(cases().join("edit/Top.olean"), dir.join("Top.olean")).unwrap();
    let r = env.reload().unwrap();
    assert_eq!(r.modules, ["Top"]);
    let removed: Vec<_> = r.removed.iter().map(|&c| env.display(c)).collect();
    assert_eq!(removed, ["letty"]);
    assert_eq!(full(&env), full(&Env::load(&search, &["Top"]).unwrap()));

    let mut delta = Tally::default();
    let mut ex = Exporter::resume(&env, &mut delta, mark).unwrap();
    ex.update(&r).unwrap();
    ex.finish().unwrap();
    let base = Env::load(&search, &["Base"]).unwrap();
    assert_eq!(delta.decls, decls(&env) - decls(&base));
    let other = Exporter::new(&env, Vec::new()).suspend().unwrap().1;
    assert!(Exporter::resume(&base, &mut Tally::default(), other).is_err());
    fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn reload_rewrites_changed_private_dependencies() {
    let dir = scratch("hidden", "Hidden");
    let search = [dir.clone()];
    let mut env = Env::open(&search, &["Hidden"], 2).unwrap();
    let mut ex = Exporter::new(&env, Vec::new());
    ex.all().unwrap();
    let (mut stream, mark) = ex.suspend().unwrap();

    fs::copy(cases().join("edit/Hidden.olean"), dir.join("Hidden.olean")).unwrap();
    let r = env.reload().unwrap();
    let mut ex = Exporter::resume(&env, Ndjson::new(Vec::new()), mark).unwrap();
    ex.update(&r).unwrap();
    let delta = ex.finish().unwrap();

    let count = |bytes: &[u8]| {
        let mut t = Tally::default();
        ndjson::read(bytes, &mut t).unwrap();
        t.decls
    };
    let before = count(&stream);
    stream.extend(delta);
    let base = Env::load(&search, &["Base"]).unwrap();
    assert_eq!(count(&stream) - before, decls(&env) - decls(&base));
    fs::remove_dir_all(&dir).unwrap();
}

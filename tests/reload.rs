use olean_export::{Env, Exporter, Record, Result, Sink};
use std::path::PathBuf;

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
    fn record(&mut self, r: &Record<'_>) -> Result<()> {
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

#[test]
fn reload_writes_only_the_changed_module() {
    let dir = std::env::temp_dir().join(format!("olean-export-reload-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let search = [dir.clone()];
    for m in ["Base", "Top"] {
        let olean = format!("{m}.olean");
        std::fs::copy(cases().join(&olean), dir.join(&olean)).unwrap();
    }
    let mut env = Env::open(&search, &["Top"], 2).unwrap();
    let mut ex = Exporter::new(&env, Vec::new());
    ex.all().unwrap();
    let (_, mark) = ex.suspend().unwrap();
    assert!(env.reload().unwrap().is_empty());

    std::fs::copy(cases().join("edit/Top.olean"), dir.join("Top.olean")).unwrap();
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
    std::fs::remove_dir_all(&dir).unwrap();
}

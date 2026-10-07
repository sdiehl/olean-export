use olean_export::{
    blean::{self, Blean},
    ndjson::{self, Ndjson},
    record::{Decl, Table},
    Env, Exporter, Record,
};
use std::path::PathBuf;

fn exports(module: &str) -> (Vec<u8>, Vec<u8>, olean_export::Counts) {
    let build = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases/build");
    let env = Env::load(&[build], &[module]).unwrap();
    let mut ex = Exporter::new(&env, Vec::new());
    ex.meta().unwrap();
    ex.all().unwrap();
    let json = ex.finish().unwrap();
    let mut ex = Exporter::with_sink(&env, Blean::new(Vec::new()));
    ex.meta().unwrap();
    ex.all().unwrap();
    let counts = ex.counts();
    (json, ex.finish().unwrap(), counts)
}

#[test]
fn round_trip() {
    for module in ["Base", "Extra", "Top"] {
        let (json, bin, counts) = exports(module);
        assert!(blean::sniff(&bin));
        assert_eq!(blean::counts(&bin).unwrap(), counts);
        assert_eq!(blean::read(&bin, Ndjson::new(Vec::new())).unwrap(), json);
        assert_eq!(
            ndjson::read(&json[..], Blean::new(Vec::new())).unwrap(),
            bin
        );
        assert!(
            bin.len() < json.len() / 3,
            "{module}: {} vs {}",
            bin.len(),
            json.len()
        );
    }
}

#[test]
fn info() {
    let (_, bin, counts) = exports("Top");
    let mut infos = Vec::new();
    for e in blean::entries(&bin).unwrap() {
        let (r, info) = e.unwrap();
        assert_eq!(info.is_some(), r.table() == Some(Table::Exprs));
        infos.extend(info);
        if let Record::Decl(Decl::Thm { head, .. } | Decl::Def { head, .. }) = &r {
            assert_eq!(infos[head.ty as usize].loose_bvar_range, 0);
        }
    }
    assert_eq!(infos.len(), counts.exprs as usize);
    let mut hashes: Vec<u64> = infos.iter().map(|i| i.hash).collect();
    hashes.sort_unstable();
    hashes.dedup();
    assert_eq!(hashes.len(), infos.len(), "distinct terms hash apart");
}

#[test]
fn truncated() {
    let (_, bin, _) = exports("Base");
    for cut in [8, bin.len() / 2, bin.len() - 1] {
        assert!(blean::read(&bin[..cut], Ndjson::new(Vec::new())).is_err());
    }
    let mut extra = bin;
    extra.push(0);
    assert!(blean::read(&extra, Ndjson::new(Vec::new())).is_err());
}

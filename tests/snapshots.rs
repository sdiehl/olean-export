use std::path::PathBuf;
use tiny_olean::{Env, Exporter};

#[test]
fn export() {
    let build = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases/build");
    insta::glob!("cases/*.lean", |path| {
        let module = path.file_stem().unwrap().to_str().unwrap();
        let env = Env::load(std::slice::from_ref(&build), &[module]).unwrap();
        let mut ex = Exporter::new(&env, Vec::new());
        ex.meta().unwrap();
        ex.all().unwrap();
        insta::assert_snapshot!(String::from_utf8(ex.finish().unwrap()).unwrap());
    });
}

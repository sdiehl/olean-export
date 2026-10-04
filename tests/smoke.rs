use tiny_olean::greet;

#[test]
fn greet_includes_name() {
    assert!(greet("world").contains("world"));
}

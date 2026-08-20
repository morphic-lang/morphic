use morphic_common::{config as cfg, file_cache, progress_ui};

fn compile(src: &str) -> Result<morphic_common::data::mono_ast::Program, morphic_frontend::error::Error> {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("test.mor");
    std::fs::write(&path, src).unwrap();

    let mut files = file_cache::FileCache::new();
    morphic_frontend::compile_to_mono_ast(
        &path,
        &[],
        cfg::ProfileMode::NoRecordRc,
        None,
        &mut files,
        progress_ui::ProgressMode::Hidden,
        cfg::PurityMode::Checked,
    )
}

#[test]
fn polymorphic_recursion_on_a_value_is_rejected() {
    let src = r#"
type Nested a {
  Single(a),
  Nest(Nested (a, a)),
}

depth(n: Nested a): Int =
  match n {
    Single(_) -> 0,
    Nest(inner) -> 1 + depth(inner),
  }

mk_nested(): Nested Int =
  panic("unreachable")

proc main(): () =
  let _ = depth(mk_nested()) in
  ()
"#;

    let err = compile(src).expect_err("expected polymorphic recursion to be rejected");
    assert!(matches!(
        err,
        morphic_frontend::error::Error::CheckPolymorphicRecursionFailed(_)
    ));
}

#[test]
fn polymorphic_recursion_on_a_type_is_rejected() {
    let src = r#"
type Nested a {
  Single(a),
  Nest(Nested (a, a)),
}

proc main(): () =
  ()
"#;

    let err = compile(src).expect_err("expected polymorphic recursion to be rejected");
    assert!(matches!(
        err,
        morphic_frontend::error::Error::CheckPolymorphicRecursionFailed(_)
    ));
}

#[test]
fn ordinary_generic_recursion_is_accepted() {
    let src = r#"
type List a {
  Nil,
  Cons(a, List a),
}

len(xs: List a): Int =
  match xs {
    Nil -> 0,
    Cons(_, rest) -> 1 + len(rest),
  }

mk_list(): List Int =
  Cons(1, Cons(2, Nil))

proc main(): () =
  let _ = len(mk_list()) in
  ()
"#;

    compile(src).expect("ordinary generic recursion should compile");
}

#[test]
fn mutually_recursive_type_parameter_swap_is_accepted() {
    let src = r#"
type Pair a b {
  MkPair(a, Other b a),
}

type Other a b {
  MkOther(b, Pair b a),
}

proc main(): () =
  ()
"#;

    compile(src).expect("a non-growing mutually recursive type swap should compile");
}

use crate::driver::commands::verify::verify_test;
use crate::servers::TestServer;

fn diagnostics_text(server: &mut TestServer) -> String {
    let diagnostics = std::mem::take(&mut server.diagnostics);
    let files = server.files.lock().unwrap();
    diagnostics
        .into_iter()
        .map(|diag| diag.into_string(&files))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn test_unsound_proof() {
    let source = r#"
    @wp
    proc main() -> ()
        pre 0
        post 0
    {
        @invariant(1)
        while true {}
    }
    "#;

    let (res, mut server) = verify_test(source);
    assert!(res.unwrap());

    let diagnostics = diagnostics_text(&mut server);
    assert!(diagnostics.contains("Unsound verification"));
    assert!(diagnostics.contains("over-approximated"));
}

#[test]
fn test_unsound_refutation() {
    let source = r#"
    @wp
    proc main() -> ()
        pre 1
        post 0
    {
        @unroll(1, 0)
        while true {}
    }
    "#;

    let (res, mut server) = verify_test(source);
    assert!(!res.unwrap());

    let diagnostics = diagnostics_text(&mut server);
    assert!(diagnostics.contains("Counter-example to verification found"));
    assert!(diagnostics.contains("pre-quantity evaluated to"));
}

#[test]
fn test_wp_with_kind_ok() {
    let source = r#"
    @wp
    coproc main() -> () {
        var x: UInt
        @k_induction(1, x)
        while 1 <= x {
            x = x - 1
        }
    }
    "#;
    let res = verify_test(source).0.unwrap();
    assert!(!res)
}

#[test]
fn test_wlp_with_kind_ok() {
    let source = r#"
    @wlp
    proc main() -> () {
        var x: UInt
        @k_induction(1, x)
        while 1 <= x {
            x = x - 1
        }
    }
    "#;
    let res = verify_test(source).0.unwrap();
    assert!(!res)
}

#[test]
fn test_wrong_annotation_usage() {
    // this should produce an error
    let source = r#"
        proc main() -> () {
            @invariant(1) // must be on a loop
            var x: UInt
        }
    "#;
    let res = verify_test(source).0; // should fail
    assert!(res.is_err());
    let err = res.unwrap_err();
    assert!(err
        .to_string()
        .contains("The proof rule `invariant` must be used on a while loop."));
}

#[test]
fn test_calculus_mismatch() {
    // this should produce an error
    let source = r#"
        @wp
        proc wp_proc() -> () {}
        @wlp
        proc wlp_proc() -> () {
            wp_proc() // this should not be called inside a @wlp annotated procedure
        }
    "#;

    let res = verify_test(source).0;
    assert!(res.is_err());
    let err = res.unwrap_err();
    assert!(err
        .to_string()
        .contains("Cannot call `wp` proc from `wlp` proc."));
}

#[test]
fn test_correct_calculus_call() {
    let source = r#"
        @wp
        proc wp_proc() -> () {}
        @wp
        proc main() -> () {
            wp_proc() // this should be allowed
        }
    "#;
    let res = verify_test(source).0;
    assert!(res.is_ok());
}

#[test]
fn test_missing_calculus_call() {
    let source = r#"

            proc default_proc() -> () {}

            @wp
            proc wp_proc() -> () {
                default_proc() // this should be allowed
            }
        "#;
    let res = verify_test(source).0;
    assert!(res.is_ok());
}

#[test]
fn test_recursion_with_wp_proc() {
    let source = r#"
    @wp
    proc A() -> () {
        var x: UInt
        A()
    }

    "#;
    let res = verify_test(source).0;
    assert!(res.is_err());
    let err = res.unwrap_err();
    assert!(err
        .to_string()
        .contains("Potentially recursive calls are not allowed in a proc with the `wp` calculus."));
}

#[test]
fn test_indirect_recursion_with_wlp_coproc() {
    let source = r#"
    @wlp
    coproc A() -> () {
        var x: UInt
        B()
    }

    coproc B() -> () {
        var x: UInt
        A()
    }

    "#;
    let res = verify_test(source).0;
    assert!(res.is_err());
    let err = res.unwrap_err();
    assert!(err.to_string().contains(
        "Potentially recursive calls are not allowed in a coproc with the `wlp` calculus."
    ));
}

#[test]
fn test_call_to_recursion() {
    let source = r#"
    @wp
    proc A() -> () {
        var x: UInt
        B() // this should be allowed
    }

    proc B() -> () {
        var y: UInt
        C()
    }

    proc C() -> () {
        var z: UInt
        B()
    }
    "#;
    let res = verify_test(source).0;
    assert!(res.is_ok());
}

#[test]
fn test_recursion_without_calculus() {
    let source = r#"
    proc A() -> () {
        var x: UInt
        A() // this should be allowed
    }

    "#;
    let res = verify_test(source).0;

    assert!(res.is_ok());
}

#[test]
fn test_recursion_with_wlp_proc() {
    let source = r#"
    @wlp
    proc A() -> () {
        var x: UInt
        B() // this should be allowed
    }

    proc B() -> () {
        var y: UInt
        A()
    }

    "#;
    let res = verify_test(source).0;

    assert!(res.is_ok());
}

#[test]
fn test_recursion_with_wlp_coproc() {
    let source = r#"
    @wlp
    coproc A() -> () {
        var x: UInt
        A()
    }

    "#;
    let res = verify_test(source).0;
    assert!(res.is_err());
    let err = res.unwrap_err();
    assert!(err.to_string().contains(
        "Potentially recursive calls are not allowed in a coproc with the `wlp` calculus."
    ));
}

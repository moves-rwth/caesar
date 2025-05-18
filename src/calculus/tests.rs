use crate::verify_test;
use crate::VerifyError;

#[test]
fn test_wp_with_kind_fail() {
    let source = r#"
    @wp
    proc main() -> () {
        var x: UInt
        @k_induction(1, x)
        while 1 <= x {
            x = x - 1
        }
    }
    "#;
    let res = matches!(verify_test(source).0, Err(VerifyError::Diagnostic(_)));

    assert!(res);
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
    assert_eq!(res, false)
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
    assert_eq!(res, false)
}

#[test]
fn test_calculus_encoding_mismatch() {
    // this should produce an error
    let source = r#"
        @wp
        proc main() -> () {
            var x: UInt
            @invariant(x) // invariant encoding within wp reasoning is not sound!
            while 1 <= x {
                x = x - 1
            }
        }
    "#;
    let res = verify_test(source).0;
    assert!(res.is_err());
    let err = res.unwrap_err();
    assert_eq!(
        err.to_string(),
        "Error: In procs, the 'wp' calculus does not support the 'invariant' encoding."
    );
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
    assert_eq!(
        err.to_string(),
        "Error: The proof rule `invariant` must be used on a while loop."
    );
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
    assert_eq!(
        err.to_string(),
        "Error: Cannot call 'wp' proc from 'wlp' proc."
    );
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
fn test_looping_with_wp() {
    let source = r#"
    @wp
    proc A() -> () {
        var x: UInt
        B()
    }

    @wp
    proc B() -> () {
        var y: UInt
        B()
    }

    "#;
    let res = verify_test(source).0;
    assert!(res.is_err());
    let err = res.unwrap_err();
    assert_eq!(
        err.to_string(),
        "Error: Potential recursive calls are not allowed in a proc with the 'wp' calculus."
    );
}

#[test]
fn test_recursive_with_wp() {
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
    assert_eq!(
        err.to_string(),
        "Error: Potential recursive calls are not allowed in a proc with the 'wp' calculus."
    );
}

#[test]
fn test_indirect_looping() {
    let source = r#"
    @wp
    proc A() -> () {
        var x: UInt
        B()
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
    assert!(res.is_err());
    let err = res.unwrap_err();
    assert_eq!(
        err.to_string(),
        "Error: Potential recursive calls are not allowed in a proc with the 'wp' calculus."
    );
}

#[test]
fn test_looping_without_calculus() {
    let source = r#"
    proc A() -> () {
        var x: UInt
        B()
    }

    proc B() -> () {
        var y: UInt
        B()
    }

    "#;
    let res = verify_test(source).0;

    assert!(res.is_ok());
}

#[test]
fn test_looping_with_wlp_proc() {
    let source = r#"
    @wlp
    proc A() -> () {
        var x: UInt
        B() // this should be allowed
    }

    proc B() -> () {
        var y: UInt
        B()
    }

    "#;
    let res = verify_test(source).0;

    assert!(res.is_ok());
}

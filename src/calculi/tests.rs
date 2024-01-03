use crate::{verify_test, VerifyError};

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

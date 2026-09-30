//! Prove equality with the expected VC by checking both bounds for arbitrary f.

use crate::driver::commands::verify::verify_test;

#[test]
fn test_validate_vc_semantics() {
    for direction in ["proc", "coproc"] {
        let source = format!(
            "{direction} main(f: EUReal) -> () pre ite(f == ∞, ∞, 0) post f {{ validate }}"
        );
        assert!(verify_test(&source).0.unwrap(), "{source}");
    }
}

#[test]
fn test_covalidate_vc_semantics() {
    for direction in ["proc", "coproc"] {
        let source = format!(
            "{direction} main(f: EUReal) -> () pre ite(f == 0, 0, ∞) post f {{ covalidate }}"
        );
        assert!(verify_test(&source).0.unwrap(), "{source}");
    }
}

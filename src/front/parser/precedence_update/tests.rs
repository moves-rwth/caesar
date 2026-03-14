use crate::{
    ast::FileId,
    front::parser::{parse_expr, ParseError},
    pretty::pretty_string,
};

type Case = (
    &'static str, // input
    &'static str, // expected_old
    &'static str, // expected_new
);

fn assert_case(case: Case, should_error: bool) {
    let (input, expected_old, expected_new) = case;

    let old_pretty = super::old_expr_pretty(FileId::DUMMY, input)
        .unwrap_or_else(|err| panic!("old parser failed for `{}`: {err}", input));
    assert_eq!(
        old_pretty, expected_old,
        "unexpected old pretty for `{}`",
        input
    );

    match parse_expr(FileId::DUMMY, input) {
        Err(ParseError::ChangedPrecedence(data)) => {
            assert!(
                should_error,
                "expected no changed-precedence error for `{}`",
                input
            );
            assert_eq!(
                data.top_new_expr, expected_new,
                "unexpected changed-precedence new pretty for `{}`",
                input
            );
            assert_eq!(
                data.top_old_expr, expected_old,
                "unexpected changed-precedence old pretty for `{}`",
                input
            );
        }
        Ok(expr) => {
            assert!(
                !should_error,
                "expected changed-precedence error for `{}`",
                input
            );
            assert_eq!(
                pretty_string(&expr),
                expected_new,
                "unexpected new pretty for `{}`",
                input
            );
        }
        Err(err) => panic!("unexpected parse error for `{}`: {err:?}", input),
    }
}

fn assert_cases(cases: &[Case], should_error: bool) {
    for &case in cases {
        assert_case(case, should_error);
    }
}

#[test]
fn test_expr_precedence_matrix() {
    #[rustfmt::skip]
    let should_not_error: &[Case] = &[
        ("a + b + c", "(a + (b + c))", "((a + b) + c)"),
        ("a * b * c", "(a * (b * c))", "((a * b) * c)"),
        ("a && b && c", "(a && (b && c))", "((a && b) && c)"),
        ("a || b || c", "((a || b) || c)", "((a || b) || c)"), // unchanged
        ("a ⊓ b ⊓ c", "(a ⊓ (b ⊓ c))", "((a ⊓ b) ⊓ c)"),
        ("a ⊔ b ⊔ c", "(a ⊔ (b ⊔ c))", "((a ⊔ b) ⊔ c)"),
        ("a && b ⊓ c", "(a && (b ⊓ c))", "(a && (b ⊓ c))"), // unchanged
        ("a ⊓ b && c", "((a ⊓ b) && c)", "((a ⊓ b) && c)"), // unchanged
        ("a || b ⊔ c", "(a || (b ⊔ c))", "(a || (b ⊔ c))"), // unchanged
        ("a ⊔ b || c", "((a ⊔ b) || c)", "((a ⊔ b) || c)"), // unchanged
        ("a == b < c", "(a == (b < c))", "(a == (b < c))"), // unchanged
        ("a ==> b ==> c", "(a → (b → c))", "(a → (b → c))"), // unchanged
        ("a ==> b ↘ c", "(a → (b ↘ c))", "(a → (b ↘ c))"), // unchanged
        ("a ↘ b ↖ c", "(a ↘ (b ↖ c))", "(a ↘ (b ↖ c))"), // unchanged
        ("forall x: Int. a == b < c", "forall x: Int. (a == (b < c))", "forall x: Int. (a == (b < c))"), // unchanged
    ];

    #[rustfmt::skip]
    let should_error: &[Case] = &[
        ("n - i + x", "(n - (i + x))", "((n - i) + x)"),
        ("3 / 5 * x", "(3 / (5 * x))", "((3 / 5) * x)"),
        ("1 - p + p * X", "(1 - (p + (p * X)))", "((1 - p) + (p * X))"),
        ("1 + 1 - p + p * X", "(1 + (1 - (p + (p * X))))", "(((1 + 1) - p) + (p * X))"),
        ("a < b == c", "(a < (b == c))", "((a < b) == c)"),
        ("a < b != c", "(a < (b != c))", "((a < b) != c)"),
        ("a <= b == c < d", "(a <= (b == (c < d)))", "((a <= b) == (c < d))"),
        ("a && b ==> c", "(a && (b → c))", "((a && b) → c)"),
        ("a ==> b && c", "((a → b) && c)", "(a → (b && c))"),
        ("a && b ↘ c", "(a && (b ↘ c))", "((a && b) ↘ c)"),
        ("a ↘ b && c", "((a ↘ b) && c)", "(a ↘ (b && c))"),
        ("a == b ↘ c", "(a == (b ↘ c))", "((a == b) ↘ c)"),
        ("a ↘ b == c", "((a ↘ b) == c)", "(a ↘ (b == c))"),
        ("a || b ↘ c", "(a || (b ↘ c))", "((a || b) ↘ c)"),
        ("a ↘ b || c", "((a ↘ b) || c)", "(a ↘ (b || c))"),
        ("forall x: Int. a ==> b && c", "forall x: Int. ((a → b) && c)", "forall x: Int. (a → (b && c))"),
        ("forall x: Int. a <= b == c < d", "forall x: Int. (a <= (b == (c < d)))", "forall x: Int. ((a <= b) == (c < d))"),
        ("f(a) ↘ g(b) || h(c)", "((f(a) ↘ g(b)) || h(c))", "(f(a) ↘ (g(b) || h(c)))"),
        ("f(a) || g(b) ↘ h(c)", "(f(a) || (g(b) ↘ h(c)))", "((f(a) || g(b)) ↘ h(c))"),
        ("!f(a) ==> g(b) && h(c)", "((! (f(a)) → g(b)) && h(c))", "(! (f(a)) → (g(b) && h(c)))"),
        ("n*(n+1)/2", "(n * (((n + 1)) / 2))", "((n * ((n + 1))) / 2)"),
    ];

    assert_cases(should_not_error, false);
    assert_cases(should_error, true);
}

#[test]
fn test_expr_precedence_mismatch_reports_subexpression_span() {
    let input = "forall x: Int. a ==> b && c";
    match parse_expr(FileId::DUMMY, input) {
        Err(ParseError::ChangedPrecedence(data)) => {
            assert_eq!(data.top_span.start, 0);
            assert_eq!(data.top_span.end, input.len());
            assert_eq!(data.subexpr.span.start, 15);
            assert_eq!(data.subexpr.span.end, input.len());
            assert_eq!(data.top_old_expr, "forall x: Int. ((a → b) && c)");
            assert_eq!(data.top_new_expr, "forall x: Int. (a → (b && c))");
            assert_eq!(data.subexpr.old_expr, "((a → b) && c)");
            assert_eq!(data.subexpr.new_expr, "(a → (b && c))");
        }
        res => panic!("expected changed-precedence error, got {res:?}"),
    }
}

#[test]
fn test_expr_precedence_mismatch_reports_full_add_sub_subexpression() {
    let input = "1 + 1 - p + p * X";
    match parse_expr(FileId::DUMMY, input) {
        Err(ParseError::ChangedPrecedence(data)) => {
            assert_eq!(data.subexpr.old_expr, "(1 + (1 - (p + (p * X))))");
            assert_eq!(data.subexpr.new_expr, "(((1 + 1) - p) + (p * X))");
        }
        res => panic!("expected changed-precedence error, got {res:?}"),
    }
}

#[test]
fn test_nonassoc_relational_and_equality_chains_are_parse_errors() {
    let invalid = ["a < b < c", "a <= b >= c", "a == b == c", "a != b != c"];

    for input in invalid {
        match parse_expr(FileId::DUMMY, input) {
            Err(ParseError::UnrecognizedToken { .. } | ParseError::UnrecognizedEof { .. }) => {}
            res => panic!("expected parse error for `{input}`, got {res:?}"),
        }
    }
}

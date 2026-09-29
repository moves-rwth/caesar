use ariadne::ReportKind;
use pretty_assertions::assert_eq;

use crate::driver::{
    commands::verify::{single_desugar_test, single_desugar_test_with_werr, verify_test},
    error::CaesarError,
};

/// Remove trailing whitespace from each line of the string, remove newlines
/// before and after the string, and remove the common indentation from each line.
fn remove_whitespace(s: &mut String) {
    let mut lines: Vec<&str> = s.lines().map(|line| line.trim_end()).collect();

    // Remove newlines before
    while let Some(line) = lines.first() {
        if line.is_empty() {
            lines.remove(0);
        } else {
            break;
        }
    }

    // Remove newlines after
    while let Some(line) = lines.last() {
        if line.is_empty() {
            lines.pop();
        } else {
            break;
        }
    }

    // Find the minimum indentation
    let min_indent = lines
        .iter()
        .filter(|line| !line.is_empty())
        .map(|line| line.chars().take_while(|c| c.is_ascii_whitespace()).count())
        .min()
        .unwrap_or(0);

    // Remove min_indent spaces from each line
    let new_string = lines
        .iter()
        .map(|line| {
            if line.len() >= min_indent {
                &line[min_indent..]
            } else {
                line
            }
        })
        .collect::<Vec<_>>()
        .join("\n");

    *s = new_string;
}

#[test]
fn test_k_induction_transform() {
    let mut test_string = String::from(
        r#"
            proc main() -> () {
                var x: UInt
                {
                    @error_msg("pre might not entail the invariant (pre ≰ I)")
                    assert cast(EUReal, x)
                    havoc x
                    validate
                    @success_msg("invariant not necessary for inductivity")
                    assume cast(EUReal, x)
                    if (1 <= x) {
                        x = (x - 1)
                        @error_msg("invariant might not be inductive (I ≰ 𝚽(I))")
                        assert cast(EUReal, x)
                        @success_msg("while could be an if statement")
                        assume cast(EUReal, 0)
                    } else {

                    }
                }
            }
        "#,
    );
    let source = r#"
            proc main() -> () {
                var x: UInt
                @k_induction(1, x)
                while 1 <= x {
                    x = x - 1
                }
            }
        "#;
    let mut res = single_desugar_test(source).unwrap();
    remove_whitespace(&mut test_string);
    remove_whitespace(&mut res);
    assert_eq!(test_string, res);
}

#[test]
fn test_unroll_transform() {
    let mut test_string = String::from(
        r#"
            proc main() -> () {
                var x: UInt
                {
                    if (1 <= x) {
                        x = (x - 1)
                        assert cast(EUReal, 1)
                        assume cast(EUReal, 0)
                    } else {

                    }
                }
            }
        "#,
    );
    let source = r#"
            proc main() -> () {
                var x: UInt
                @unroll(1, 1)
                while 1 <= x {
                    x = x - 1
                }
            }
        "#;
    let mut res = single_desugar_test(source).unwrap();
    remove_whitespace(&mut test_string);
    remove_whitespace(&mut res);
    assert_eq!(test_string, res);
}

fn normalized_desugar(source: &str) -> String {
    let (result, server) = single_desugar_test_with_werr(source, true);
    assert!(server.diagnostics.is_empty(), "{source}");
    result
        .unwrap()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

#[test]
fn test_optional_terminators_match_explicit_defaults() {
    // The calculus must determine the default even when the procedure direction is used for refutation.
    for direction in ["proc", "coproc"] {
        for (calculus, terminator) in [
            ("@wp", "0"),
            ("@ert", "0"),
            ("@wlp", "1"),
            ("@uwlp", "∞"),
            ("", if direction == "proc" { "0" } else { "∞" }),
        ] {
            for (rule, required_args) in [
                ("unroll", "0"), // Zero unrollings produce only the terminator.
                ("unroll", "2"),
                ("omega_invariant", "n, [n > 0]"),
            ] {
                let source = |args: &str| {
                    format!(
                        "{calculus} {direction} main() -> () {{ @{rule}({args}) while true {{}} }}"
                    )
                };
                let implicit = source(required_args);
                let explicit = source(&format!("{required_args}, {terminator}"));
                assert_eq!(
                    normalized_desugar(&implicit),
                    normalized_desugar(&explicit),
                    "{implicit}"
                );
            }
        }
    }
}

#[test]
fn test_omega_explicit_terminator_selects_fixed_point_semantics() {
    // An explicit terminator must select the same omega encoding as the corresponding calculus.
    for direction in ["proc", "coproc"] {
        for (calculus, terminator) in [("wp", "0"), ("wlp", "1"), ("uwlp", "∞")] {
            let source = format!(
                "{direction} main() -> () {{ @omega_invariant(n, [n > 0], {terminator}) while true {{}} }}"
            );
            // Desugared procedures omit calculus annotations when printed.
            assert_eq!(
                normalized_desugar(&source),
                normalized_desugar(&format!("@{calculus} {source}")),
                "{source}"
            );
        }
    }
}

#[test]
fn test_explicit_terminator_expressions_are_preserved() {
    // Keep the supplied expression even though wp would otherwise choose 0.
    for (rule, required_args) in [("unroll", "0"), ("omega_invariant", "n, [n > 0]")] {
        let source = format!(
            "@wp proc main(x: EUReal) -> () {{
                @{rule}({required_args}, x + 2)
                while true {{}}
            }}"
        );
        let (result, mut server) = single_desugar_test_with_werr(&source, false);
        let result = result.unwrap();
        assert!(result.contains("assert (x + cast(EUReal, 2))"), "{result}");
        assert_eq!(server.diagnostics.len(), 1);
        let diagnostic = server.diagnostics.pop().unwrap();
        assert_eq!(diagnostic.kind(), ReportKind::Warning);
        let span = diagnostic.span();
        assert_eq!(&source[span.start..span.end], "x + 2");
        let text = diagnostic.into_string(&server.files.lock().unwrap());
        assert!(text.contains("[terminator-mismatch]"), "{text}");
        assert!(
            text.contains(&format!("Terminator for `@{rule}`")),
            "{text}"
        );
        assert!(text.contains("Expected `0`"), "{text}");
        assert!(text.contains("Inferred fixed-point kind: least."), "{text}");
    }
}

#[test]
fn test_terminator_warning_reports_greatest_fixed_point_kind() {
    for (context, kind, expected) in [
        ("@wlp proc", "greatest (one-bounded)", "1"),
        ("@uwlp proc", "greatest (unbounded)", "∞"),
    ] {
        let source = format!("{context} main() -> () {{ @unroll(0, 2) while true {{}} }}");
        let (result, mut server) = single_desugar_test_with_werr(&source, false);
        result.unwrap();
        assert_eq!(server.diagnostics.len(), 1);
        let diagnostic = server.diagnostics.pop().unwrap();
        let text = diagnostic.into_string(&server.files.lock().unwrap());
        assert!(
            text.contains(&format!("Inferred fixed-point kind: {kind}.")),
            "{text}"
        );
        assert!(text.contains(&format!("Expected `{expected}`")), "{text}");
    }
}

#[test]
fn test_terminator_mismatch_is_fatal_with_werr() {
    for rule in ["@unroll(0, 1)", "@omega_invariant(n, 0, 1)"] {
        let source = format!("@wp proc main() -> () {{ {rule} while true {{}} }}");
        let (result, server) = single_desugar_test_with_werr(&source, true);
        assert!(matches!(
            result,
            Err(CaesarError::Diagnostic(ref diagnostic))
                if diagnostic.kind() == ReportKind::Warning
                    && diagnostic.to_string().contains("[terminator-mismatch]")
        ));
        // Fatal diagnostics are returned to the caller instead of being queued.
        assert!(server.diagnostics.is_empty());
    }
}

#[test]
fn test_optional_terminators_reject_invalid_argument_counts() {
    for (annotation, expected) in [
        ("@unroll()", "Expected 1 to 2 arguments, got 0"),
        ("@unroll(1, 0, 0)", "Expected 1 to 2 arguments, got 3"),
        ("@omega_invariant()", "Expected 2 to 3 arguments, got 0"),
        ("@omega_invariant(n)", "Expected 2 to 3 arguments, got 1"),
        (
            "@omega_invariant(n, 0, 0, 0)",
            "Expected 2 to 3 arguments, got 4",
        ),
    ] {
        let source = format!("proc main() -> () {{ {annotation} while true {{}} }}");
        let err = single_desugar_test(&source).unwrap_err();
        assert!(err.to_string().contains(expected), "{annotation}: {err}");
    }
}

#[test]
fn test_optional_terminators_preserve_argument_type_checks() {
    for (annotation, expected) in [
        ("@unroll(true)", "Cannot cast expression to type UInt"),
        ("@unroll(1, true)", "Cannot cast expression to type EUReal"),
        (
            "@omega_invariant(n, 1, true)",
            "Cannot cast expression to type EUReal",
        ),
        ("@unroll(k)", "Expected a literal here"),
        ("@unroll(k, 0)", "Expected a literal here"),
    ] {
        let source = format!("proc main(k: UInt) -> () {{ {annotation} while true {{}} }}");
        let err = single_desugar_test(&source).unwrap_err();
        assert!(err.to_string().contains(expected), "{annotation}: {err}");
    }
}

#[test]
fn test_omega_terminator_uses_outer_scope() {
    // The invariant's index must not leak into the terminator.
    let source = "proc main() -> () { @omega_invariant(n, [n > 0], n) while true {} }";
    let err = single_desugar_test(source).unwrap_err();
    assert!(err.to_string().contains("Name `n` is not declared"));

    // Different types distinguish the outer Bool n from the invariant's UInt n.
    let source = r#"
        proc main(n: Bool) -> () {
            @omega_invariant(n, [n > 0], ite(n, 2, 3))
            while true {}
        }
    "#;
    let (result, server) = single_desugar_test_with_werr(source, false);
    let result = result.unwrap();
    assert_eq!(server.diagnostics.len(), 1);
    assert!(
        result.contains("assert cast(EUReal, ite(n, 2, 3))"),
        "{result}"
    );
}

#[test]
fn test_omega_transform() {
    let mut test_string = String::from(
        r#"
            proc main() -> () {
                var x: UInt
                {
                    assert sup n. [(n > x)]
                    havoc x
                    if ⊓ {
                        validate
                        assume ([(n > x)])[n -> 0]
                        if (1 <= x) {
                            x = (x - 1)
                            assert cast(EUReal, 0)
                            assume cast(EUReal, 0)
                        } else {

                        }
                    } else {
                        havoc n
                        validate
                        assume ([(n > x)])[n -> (n + 1)]
                        if (1 <= x) {
                            x = (x - 1)
                            assert [(n > x)]
                            assume cast(EUReal, 0)
                        } else {

                        }
                    }
                }
            }
        "#,
    );
    let source = r#"
            proc main() -> () {
                var x: UInt
                @omega_invariant(n,[n > x])
                while 1 <= x {
                    x = x - 1
                }
            }
        "#;
    let mut res = single_desugar_test(source).unwrap();
    remove_whitespace(&mut test_string);
    remove_whitespace(&mut res);
    assert_eq!(test_string, res);
}

#[test]
fn test_omega_index_is_scoped_to_annotation() {
    for loop_and_continuation in [
        "while true { n = n + 1 }",
        "while n > 0 {}",
        "while false {} assert [n == 0]",
    ] {
        let source =
            format!("proc main() -> () {{ @omega_invariant(n, [n > 0]) {loop_and_continuation} }}");
        let err = verify_test(&source).0.unwrap_err();
        assert!(err.to_string().contains("Name `n` is not declared"));
    }
}

#[test]
fn test_omega_index_can_be_reused() {
    let source = r#"
        @wp
        proc main() -> ()
            pre 1
            post 1
        {
            @omega_invariant(n, [n >= 0])
            while false {}
            @omega_invariant(n, [n >= 0])
            while false {}
        }
    "#;
    assert!(verify_test(source).0.unwrap());
}

#[test]
fn test_omega_preserves_assumptions_about_unmodified_parameters() {
    let source = r#"
        @wp
        proc main(a: UInt) -> ()
            pre [a == 0]
            post 1
        {
            var x: UInt = 1
            @omega_invariant(n, [a == 0 && x <= n] + [a != 0])
            while x > 0 {
                x = x - 1
            }
        }
    "#;
    assert!(verify_test(source).0.unwrap());
}

fn assert_omega_counterexample(source: &str) -> String {
    let (result, mut server) = verify_test(source);
    assert!(!result.unwrap());
    let diagnostics = std::mem::take(&mut server.diagnostics);
    let files = server.files.lock().unwrap();
    let diagnostics = diagnostics
        .into_iter()
        .map(|diagnostic| diagnostic.into_string(&files))
        .collect::<Vec<_>>()
        .join("\n");
    assert!(diagnostics.contains("Counter-example to"), "{diagnostics}");
    assert!(
        diagnostics.contains("pre-quantity evaluated to"),
        "{diagnostics}"
    );
    diagnostics
}

#[test]
fn test_omega_wlp_refutation_uses_greatest_fixed_point() {
    let diagnostics = assert_omega_counterexample(
        r#"
            @wlp
            proc main() -> ()
                pre 1
                post 0
            {
                @omega_invariant(n, 0)
                while false {}
            }
        "#,
    );
    assert!(diagnostics.contains("Counter-example to property found"));
}

#[test]
fn test_omega_wp_refutation_uses_least_fixed_point() {
    let diagnostics = assert_omega_counterexample(
        r#"
            @wp
            coproc main() -> ()
                pre 0
                post 1
            {
                @omega_invariant(n, 1)
                while false {}
            }
        "#,
    );
    assert!(diagnostics.contains("Counter-example to property found"));
}

#[test]
fn test_omega_unbounded_upper_bound_starts_at_top() {
    assert_omega_counterexample(
        r#"
            coproc main() -> ()
                pre 1
                post 0
            {
                @omega_invariant(n, 1)
                while true {}
            }
        "#,
    );
}

#[test]
fn test_omega_uwlp_starts_at_infinity_instead_of_one() {
    let source = r#"
        @wlp
        coproc main() -> ()
            pre 1
            post 0
        {
            @omega_invariant(n, 1)
            while true {}
        }
    "#;
    let (result, server) = verify_test(source);
    assert!(result.unwrap());
    assert!(server.diagnostics.is_empty());
    let diagnostics = assert_omega_counterexample(&source.replace("@wlp", "@uwlp"));
    assert!(diagnostics.contains("Counter-example to verification found"));
}

#[test]
fn test_omega_uwlp_finite_upper_bound_on_terminating_loop() {
    let source = r#"
        @uwlp
        coproc main() -> ()
            pre 2
            post 2
        {
            var b: Bool = true
            @omega_invariant(n, ite(n == 0 && b, ∞, 2))
            while b {
                b = false
            }
        }
    "#;
    let (result, server) = verify_test(source);
    assert!(result.unwrap());
    assert!(server.diagnostics.is_empty());
}

#[test]
fn test_omega_collects_variables_modified_by_cohavoc() {
    assert_omega_counterexample(
        r#"
            proc main() -> ()
                pre 1
                post 1
            {
                var x: UInt = 0
                @omega_invariant(n, [x > 0 || n > 0])
                while true {
                    cohavoc x
                }
            }
        "#,
    );
}

#[test]
fn test_ost_transform() {
    let mut test_string = String::from(
        r#"
            proc optional_stopping(init_b: UInt, init_a: Bool) -> (b: UInt, a: Bool)
                pre (cast(EUReal, init_b) + [init_a])
                post cast(EUReal, b)
            {
                var prob_choice: Bool
                var k: UInt
                b = init_b
                a = init_a
                {
                    prob_choice, a, b, k = optional_stopping_lower_bound_0(
                        prob_choice, a, b, k
                    )
                }
            }
            proc optional_stopping_lt_infinity_0(a: Bool) -> () {
                assert ?(((cast(EUReal, 2) * [a]) < ∞))
            }
            coproc optional_stopping_past_0(
                init_prob_choice: Bool, init_a: Bool, init_b: UInt, init_k: UInt
            ) -> (prob_choice: Bool, a: Bool, b: UInt, k: UInt)
                pre ((cast(EUReal, 2) * [a]))[a -> init_a]
                post cast(EUReal, 0)
            {
                prob_choice = init_prob_choice
                a = init_a
                b = init_b
                k = init_k
                if a {
                    prob_choice = flip(((cast(UReal, 1) / cast(UReal, 2))))
                    if prob_choice { a = false } else { b = (b + 1) }
                    k = (k + 1)
                    tick cast(EUReal, 1)
                    coassert (cast(EUReal, 2) * [a])
                    coassume ∞
                } else {

                }
            }
            coproc optional_stopping_conditional_difference_bounded_0(
                init_prob_choice: Bool, init_a: Bool, init_b: UInt, init_k: UInt
            ) -> (prob_choice: Bool, a: Bool, b: UInt, k: UInt)
                pre cast(EUReal, cast(UReal, 1))
                post ite(
                    (
                        (((cast(EUReal, b) + [a]))[b -> init_b])[a -> init_a] <= (
                            cast(EUReal, b) + [a]
                        )
                    ),
                    (
                        (cast(EUReal, b) + [a]) - (
                            ((cast(EUReal, b) + [a]))[b -> init_b]
                        )[a -> init_a]
                    ),
                    (
                        (((cast(EUReal, b) + [a]))[b -> init_b])[a -> init_a] - (
                            cast(EUReal, b) + [a]
                        )
                    )
                )
            {
                prob_choice = init_prob_choice
                a = init_a
                b = init_b
                k = init_k
                prob_choice = flip(((cast(UReal, 1) / cast(UReal, 2))))
                if prob_choice { a = false } else { b = (b + 1) }
                k = (k + 1)
            }
            proc optional_stopping_harmonize_I_f_0(a: Bool, b: UInt) -> () {
                assert ?((! (a) → ((cast(EUReal, b) + [a]) == cast(EUReal, b))))
            }
            coproc optional_stopping_loopiter_lt_infty_0(
                init_prob_choice: Bool, init_a: Bool, init_b: UInt, init_k: UInt
            ) -> (prob_choice: Bool, a: Bool, b: UInt, k: UInt)
                pre cast(EUReal, 0)
                post cast(EUReal, b)
            {
                prob_choice = init_prob_choice
                a = init_a
                b = init_b
                k = init_k
                validate
                assume ∞
                if a {
                    prob_choice = flip(((cast(UReal, 1) / cast(UReal, 2))))
                    if prob_choice { a = false } else { b = (b + 1) }
                    k = (k + 1)
                    coassert (cast(EUReal, b) + [a])
                    coassume ∞
                } else {

                }
            }
            proc optional_stopping_lower_bound_0(
                init_prob_choice: Bool, init_a: Bool, init_b: UInt, init_k: UInt
            ) -> (prob_choice: Bool, a: Bool, b: UInt, k: UInt)
                pre (((cast(EUReal, b) + [a]))[b -> init_b])[a -> init_a]
                post cast(EUReal, b)
            {
                prob_choice = init_prob_choice
                a = init_a
                b = init_b
                k = init_k
                if a {
                    prob_choice = flip(((cast(UReal, 1) / cast(UReal, 2))))
                    if prob_choice { a = false } else { b = (b + 1) }
                    k = (k + 1)
                    assert (cast(EUReal, b) + [a])
                    assume cast(EUReal, 0)
                } else {

                }
            }
        "#,
    );
    let source = r#"
        proc optional_stopping(init_b: UInt, init_a: Bool) -> (b: UInt, a: Bool)
            pre init_b + [init_a]
            post b
        {
            var prob_choice: Bool
            var k: UInt

            b = init_b
            a = init_a

            @ost(b + [a], 2 * [a], 1, b)
            while a {
                prob_choice = flip((1/2))
                if prob_choice {
                    a = false
                } else {
                   b = b + 1
                }
                k = k + 1
            }
        }
        "#;
    let mut res = single_desugar_test(source).unwrap();
    remove_whitespace(&mut test_string);
    remove_whitespace(&mut res);
    assert_eq!(test_string, res);
}

#[test]
fn test_past_transform() {
    let mut test_string = String::from(
        r#"
            proc main() -> () {
                var x: UInt
                {  }
            }
            proc main_past_bounded_on_exit_0(x: UInt) -> () {
                assert ?((([! ((1 <= x))] * cast(EUReal, (x + 1))) <= cast(EUReal, 10/10)))
            }
            proc main_past_k_bounded_by_invariant_0(x: UInt) -> () {
                assert (
                    ([(1 <= x)] * cast(EUReal, 10/10)) <= (
                        ([(1 <= x)] * cast(EUReal, (x + 1))) + [! ((1 <= x))]
                    )
                )
            }
            coproc main_past_decreases_0(init_x: UInt) -> (x: UInt)
                pre (
                    [((1 <= x))[x -> init_x]] * (
                        (cast(EUReal, (x + 1)))[x -> init_x] - cast(EUReal, 5/10)
                    )
                )
                post cast(EUReal, 0)
            {
                x = init_x
                if (1 <= x) {
                    x = (x - 1)
                    assert cast(EUReal, (x + 1))
                    assume cast(EUReal, 0)
                } else {

                }
            }
        "#,
    );
    let source = r#"
            proc main() -> () {
                var x: UInt
                @past(x+1, 0.5, 1.0)
                while 1 <= x {
                    x = x - 1
                }
            }
        "#;
    let mut res = single_desugar_test(source).unwrap();
    remove_whitespace(&mut test_string);
    remove_whitespace(&mut res);
    assert_eq!(test_string, res);
}

#[test]
fn test_past_rejects_infinite_loop() {
    // Issue #122 also fails without tick, isolating the required decrease.
    for body in ["tick 1", ""] {
        let source = format!(
            r#"
                @ert coproc main() -> ()
                    pre 0
                    post 0
                {{
                    @past(1, 0.5, 1)
                    while true {{ {body} }}
                }}
            "#
        );
        let (result, mut server) = verify_test(&source);
        assert!(!result.unwrap(), "{source}");
        let diagnostics = std::mem::take(&mut server.diagnostics);
        let files = server.files.lock().unwrap();
        let diagnostics = diagnostics
            .into_iter()
            .map(|diagnostic| diagnostic.into_string(&files))
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            diagnostics.contains("Counter-example to property found"),
            "{diagnostics}"
        );
    }
}

#[test]
fn test_past_accepts_deterministic_countdown() {
    let source = r#"
        proc main(init_x: UInt) -> (x: UInt)
        {
            x = init_x
            @past(x + 1, 0.5, 1)
            while 0 < x {
                x = x - 1
            }
        }
    "#;
    assert!(verify_test(source).0.unwrap());
}

#[test]
fn test_past_accepts_probabilistic_countdown() {
    let source = r#"
        proc main(init_x: UInt) -> (x: UInt)
        {
            var prob_choice: Bool
            x = init_x
            @past(x + 1, 0.5, 1)
            while 0 < x {
                prob_choice = flip(0.5)
                if prob_choice {
                    x = x - 1
                } else {}
            }
        }
    "#;
    assert!(verify_test(source).0.unwrap());
}

#[test]
fn test_ast_transform() {
    let mut test_string = String::from(
        r#"
        proc main() -> () {
            var x: UInt
            { assert [true]; havoc x; validate; assume [true] }
        }
        proc main_prob_conditions_0(v_0: UReal, v_1: UReal) -> ()
            pre ?((true && (v_0 <= v_1)))
            post ?(((5/10)[v -> v_1] > cast(UReal, 0)))
            post ?(((v_0 > cast(UReal, 0)) → ((5/10)[v -> v_1] <= (5/10)[v -> v_0])))
            post ?(((5/10)[v -> v_0] <= cast(UReal, 1)))
        {

        }
        proc main_decrease_conditions_0(v_0: UReal, v_1: UReal) -> ()
            pre ?((true && (v_0 <= v_1)))
            post ?(((cast(UReal, 1))[v -> v_1] > cast(UReal, 0)))
            post ?((
                (v_0 > cast(UReal, 0)) → (
                    (cast(UReal, 1))[v -> v_1] <= (cast(UReal, 1))[v -> v_0]
                )
            ))
        {

        }
        proc main_I_wp_subinvariant_0(init_x: UInt) -> (x: UInt)
            pre ([true])[x -> init_x]
            post [true]
        {
            x = init_x
            if (1 <= x) { x = (x - 1) } else {  }
        }
        coproc main_V_awp_superinvariant_0(init_x: UInt) -> (x: UInt)
            pre ! (?((true)[x -> init_x]))
            pre cast(EUReal, (cast(UReal, x))[x -> init_x])
            post ([(1 <= x)] * cast(EUReal, cast(UReal, x)))
        {
            x = init_x
            if (1 <= x) { x = (x - 1) } else {  }
        }
        proc main_progress_condition_0(init_x: UInt) -> (x: UInt)
            pre ?((true)[x -> init_x])
            pre ?(((1 <= x))[x -> init_x])
            pre cast(EUReal, (5/10)[v -> (cast(UReal, x))[x -> init_x]])
            post [(
                ! ((1 <= x)) || (
                    (
                        cast(UReal, x) + (cast(UReal, 1))[v -> (
                            cast(UReal, x)
                        )[x -> init_x]]
                    ) <= (cast(UReal, x))[x -> init_x]
                )
            )]
        {
            x = init_x
            x = (x - 1)
        }
        "#,
    );
    let source = r#"
            proc main() -> () {
                var x: UInt
                @ast(true, x, v, 0.5, 1)
                while 1 <= x {
                    x = x - 1
                }
            }
        "#;
    let mut res = single_desugar_test(source).unwrap();
    remove_whitespace(&mut test_string);
    remove_whitespace(&mut res);
    assert_eq!(test_string, res);
}

#[test]
fn test_ast_pre_and_post() {
    for (pre, post, assertion, expected) in [
        ("[init_x == 1]", "[init_x == 1 && x <= 1]", "[x <= 1]", true),
        ("1", "1", "1", false),
        ("[init_x == 1]", "[x == 1]", "1", false),
        ("[init_x == 1]", "1", "0", false),
    ] {
        let source = format!(
            r#"
                @wp proc main(init_x: UInt) -> (x: UInt)
                    pre {pre}
                    post {post}
                {{
                    x = init_x
                    @ast(x <= 1, x, v, 1, 1)
                    while x > 0 {{
                        var amount: UInt = init_x + 1
                        x = x - amount
                    }}
                    assert {assertion}
                }}
            "#
        );
        assert_eq!(verify_test(&source).0.unwrap(), expected, "{source}");
    }
}

#[test]
fn test_ast_variant_at_exit() {
    for (variant, body, expected) in [
        ("0", "done = flip(0.5)", true),
        ("1", "done = flip(0.5)", true),
        ("x", "x = x + 1; done = true", true),
        ("0", "", false),
    ] {
        let source = format!(
            r#"
                @wp proc main() -> ()
                    pre 1
                    post 1
                {{
                    var x: UReal = 0
                    var done: Bool = false
                    @ast(true, {variant}, v, ite(v == 0, 0.25, 0.5), ite(v == 0, 0.5, 1))
                    while !done {{ {body} }}
                }}
            "#
        );
        assert_eq!(verify_test(&source).0.unwrap(), expected, "{source}");
    }
}

#[test]
fn test_ast_function_conditions() {
    for (invariant, prob, decrease, expected) in [
        ("true", "0", "1", false),
        ("true", "2", "1", false),
        ("true", "ite(v == 0, 0, 1)", "1", false),
        ("true", "ite(v == 0, 2, 1)", "1", false),
        ("true", "1", "0", false),
        ("true", "1", "v + 1", false),
        ("true", "ite(v <= 1, 0.5, 1)", "1", false),
        ("x <= 1", "ite(v <= 1, 1, 0)", "1", false),
        ("true", "1", "ite(v == 0, 0, 1)", false),
        ("bound > 0 && bound <= 1", "bound", "1", true),
        ("bound > 0", "1", "bound", true),
        ("true", "bound", "1", false),
        ("true", "let(x, 1, x)", "let(v, 1, v)", true),
    ] {
        let source = format!(
            r#"
                @wp proc main() -> ()
                    pre 1
                    post 1
                {{
                    var x: UReal = 1
                    var bound: UReal = 1
                    var v: UInt = 7
                    @ast({invariant}, x, v, {prob}, {decrease})
                    while x > 0 {{ x = 0 }}
                    assert [v == 7]
                }}
            "#
        );
        assert_eq!(verify_test(&source).0.unwrap(), expected, "{source}");
    }
}

#[test]
fn test_ast_function_dependencies() {
    for (prob, decrease, body, following, reason) in [
        (
            "x",
            "1",
            "x = 0",
            "",
            "`prob` must not depend on loop-modified variable `x`.",
        ),
        (
            "1",
            "x",
            "x = 0",
            "",
            "`decrease` must not depend on loop-modified variable `x`.",
        ),
        (
            "let(t, x, t)",
            "1",
            "@unroll(0) while true { x = 0 }",
            "",
            "`prob` must not depend on loop-modified variable `x`.",
        ),
        (
            "1",
            "1",
            "x = 0",
            "assert [v == 0]",
            "Name `v` is not declared",
        ),
    ] {
        let source = format!(
            r#"
                @wp proc main() -> () {{
                    var x: UReal = 1
                    @ast(true, x, v, {prob}, {decrease})
                    while x > 0 {{ {body} }}
                    {following}
                }}
            "#
        );
        let (result, server) = verify_test(&source);
        let CaesarError::Diagnostic(diagnostic) = result.unwrap_err() else {
            panic!("expected an annotation-argument or resolution diagnostic");
        };
        let text = diagnostic.into_string(&server.files.lock().unwrap());
        assert!(text.contains(reason), "{source}\n{text}");
    }
}

#[test]
fn test_ast_rejects_demonically_biased_random_walks() {
    // Every choice has positive progress, but a demon can select upward drift.
    for body in [
        r#"
            if \cap {
                x = x - 1
            } else {
                var b: Bool = flip(0.25)
                if b { x = x - 1 } else { x = x + 1 }
            }
        "#,
        r#"
            var choice: Bool = false
            havoc choice
            if choice {
                x = x - 1
            } else {
                var b: Bool = flip(0.25)
                if b { x = x - 1 } else { x = x + 1 }
            }
        "#,
        r#"
            var sampled: Bool = flip(0.5)
            var choice: Bool = false
            if \cap { choice = sampled } else { choice = !sampled }
            if choice {
                x = x - 1
            } else {
                var b: Bool = flip(0.25)
                if b { x = x - 1 } else { x = x + 1 }
            }
        "#,
    ] {
        let source = format!(
            r#"
                @wp proc main() -> (x: UInt)
                    pre 1
                    post 1
                {{
                    x = 1
                    @ast(true, x, v, 0.25, 1)
                    while x > 0 {{ {body} }}
                }}
            "#
        );
        assert!(!verify_test(&source).0.unwrap(), "{source}");
    }
}

#[test]
fn test_ast_requires_progress_for_every_demonic_choice() {
    let source = r#"
        @wp proc main() -> ()
            pre 1
            post 1
        {
            var x: UInt = 1
            @ast(true, x, v, 1, 1)
            while x > 0 {
                if \cap { x = x - 1 } else {}
            }
        }
    "#;
    assert!(!verify_test(source).0.unwrap());
}

#[test]
fn test_ast_rejects_unsupported_source_statements() {
    for (body, reason) in [
        // Check before an inner annotation can erase the source.
        (
            r"@unroll(0) while true { if \cup {} else {} }",
            "Angelic choice is not allowed.",
        ),
        ("if + {} else {}", "Additive choice is not allowed."),
        (
            "var choice: Bool = false; cohavoc choice",
            "Angelic havoc is not allowed.",
        ),
        ("helper()", "Procedure calls are not allowed."),
        (
            "var local: Bool",
            "Loop-local variables must be initialized.",
        ),
    ] {
        let source = format!(
            r#"
                proc helper() -> () {{}}
                @wp proc main() -> ()
                    pre 1
                    post 1
                {{
                    var x: UInt = 1
                    @ast(true, x, v, 1, 1)
                    while x > 0 {{ {body} }}
                }}
            "#
        );
        let (result, server) = verify_test(&source);
        let CaesarError::Diagnostic(diagnostic) = result.unwrap_err() else {
            panic!("expected an unsupported-statement diagnostic");
        };
        assert_eq!(diagnostic.kind(), ReportKind::Error);
        let text = diagnostic.into_string(&server.files.lock().unwrap());
        assert!(text.contains(reason), "{source}\n{text}");
        if body.contains("if ") || body.contains("cohavoc") {
            assert!(
                text.contains("Only probabilistic or demonic choices are allowed."),
                "{text}"
            );
        }
    }
}

#[test]
fn test_ast_warns_about_possibly_infinite_havoc_domains() {
    let source = r#"
        @wp proc main() -> () {
            var x: UInt = 1
            var y: UReal = 0
            var flag: Bool = false
            @ast(true, x, v, 1, 1)
            while x > 0 {
                havoc flag
                @unroll(0) while true { havoc flag, x, y }
            }
        }
    "#;
    let (result, mut server) = single_desugar_test_with_werr(source, false);
    result.unwrap();
    assert_eq!(server.diagnostics.len(), 1);
    let diagnostic = server.diagnostics.pop().unwrap();
    assert_eq!(diagnostic.kind(), ReportKind::Warning);
    let text = diagnostic.into_string(&server.files.lock().unwrap());
    assert!(text.contains("Havoc domain may be infinite"), "{text}");
    assert!(text.contains("`x` has type `UInt`"), "{text}");
    assert!(text.contains("`y` has type `UReal`"), "{text}");
    assert!(!text.contains("`flag` has type"), "{text}");

    let (result, server) = single_desugar_test_with_werr(source, true);
    assert!(matches!(
        result,
        Err(CaesarError::Diagnostic(ref diagnostic))
            if diagnostic.kind() == ReportKind::Warning
                && diagnostic.to_string().contains("Havoc domain may be infinite")
    ));
    assert!(server.diagnostics.is_empty());
}

#[test]
fn test_ast_accepts_pure_functions_and_distributions() {
    let source = r#"
        domain Helpers {
            func predecessor(n: UInt): UInt = n - 1
        }
        @wp proc main() -> ()
            pre 1
            post 1
        {
            var x: UInt = 1
            @ast(true, x, v, 0.5, 1)
            while x > 0 {
                var choice: Bool = flip(0.5)
                if choice { x = predecessor(x) } else {}
            }
        }
    "#;
    assert!(verify_test(source).0.unwrap());
}

/// Test if the fresh identifier generation works correctly
/// when there are multiple instances of the annotation type on the same procedure
#[test]
fn test_double_annotation() {
    let source = r#"
    proc main() -> ()
        pre 1
        post 1
    {
        var x: UInt
        @ast(true, (3 * ite(!(x % 2 == 0), 1, 0)) + ite(x >= 10, x - 10, 10 - x), v, 0.5, 2)
        while x != 10 {
            if x % 2 == 0{
                var prob_choice: Bool = flip(1/2)
                if prob_choice {
                    x = x - 2
                } else {
                    x = x + 2
                }
            } else {
                x = x + 1
            }
        }

        @ast(true, (3 * ite(!(x % 2 == 0), 1, 0)) + ite(x >= 10, x - 10, 10 - x), t, 0.5, 2)
        while x != 10 {
            if x % 2 == 0{
                var prob_choice: Bool = flip(1/2)
                if prob_choice {
                    x = x - 2
                } else {
                    x = x + 2
                }
            } else {
                x = x + 1
            }
        }

    }
        "#;

    let res = verify_test(source).0.unwrap();
    assert_eq!(res, true)
}
#[test]
fn test_k_induction_nested_transform() {
    let source = r#"
            proc main() -> () {
                var x: UInt
                var y: UInt
                @k_induction(1, x)
                while 1 <= x {
                    x = x - 1
                    @k_induction(1, y)
                    while 1 <= y {
                        y = y - 1
                    }
                }
            }
        "#;

    let mut test_string = String::from(
        r#"
            proc main() -> () {
                var x: UInt
                var y: UInt
                {
                    @error_msg("pre might not entail the invariant (pre ≰ I)")
                    assert cast(EUReal, x)
                    havoc x, y
                    validate
                    @success_msg("invariant not necessary for inductivity")
                    assume cast(EUReal, x)
                    if (1 <= x) {
                        x = (x - 1)
                        {
                            @error_msg("pre might not entail the invariant (pre ≰ I)")
                            assert cast(EUReal, y)
                            havoc y
                            validate
                            @success_msg("invariant not necessary for inductivity")
                            assume cast(EUReal, y)
                            if (1 <= y) {
                                y = (y - 1)
                                @error_msg("invariant might not be inductive (I ≰ 𝚽(I))")
                                assert cast(EUReal, y)
                                @success_msg("while could be an if statement")
                                assume cast(EUReal, 0)
                            } else {

                            }
                        }
                        @error_msg("invariant might not be inductive (I ≰ 𝚽(I))")
                        assert cast(EUReal, x)
                        @success_msg("while could be an if statement")
                        assume cast(EUReal, 0)
                    } else {

                    }
                }
            }
        "#,
    );
    let mut res = single_desugar_test(source).unwrap();
    remove_whitespace(&mut test_string);
    remove_whitespace(&mut res);
    assert_eq!(test_string, res);
}

#[test]
fn test_past_not_on_while() {
    let source = r#"
    proc main() -> () {
        var x: UInt
        @past(x+1, 0.5, 1.0)
        x= x+1;
    }
"#;

    let err = verify_test(source).0.unwrap_err();
    assert_eq!(
        err.to_string(),
        "Error: The proof rule `past` must be used on a while loop."
    );
}
#[test]
fn test_invariant_not_on_while() {
    let source = r#"
        proc main2() -> () {
            var x: UInt
            @invariant(x)
            x = x + 1
        }
        "#;
    let err = verify_test(source).0.unwrap_err();
    assert_eq!(
        err.to_string(),
        "Error: The proof rule `invariant` must be used on a while loop."
    );
}

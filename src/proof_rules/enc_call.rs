//! Replacement of calls to procedures by their specification.

use std::rc::Rc;

use crate::{
    ast::{visit::VisitorMut, DeclKind, Direction, SourceFilePath, Span, Stmt, StmtKind},
    driver::{Item, SourceUnit},
    intrinsic::annotations::{AnnotationError, AnnotationKind},
    tyctx::TyCtx,
};

use super::Encoding;
pub struct EncCall<'tcx, 'sunit> {
    tcx: &'tcx mut TyCtx,
    source_units_buf: &'sunit mut Vec<Item<SourceUnit>>,
    direction: Option<Direction>,
}

impl<'tcx, 'sunit> EncCall<'tcx, 'sunit> {
    pub fn new(tcx: &'tcx mut TyCtx, source_units_buf: &'sunit mut Vec<Item<SourceUnit>>) -> Self {
        EncCall {
            tcx,
            source_units_buf,
            direction: Option::None,
        }
    }
}

impl<'tcx, 'sunit> VisitorMut for EncCall<'tcx, 'sunit> {
    type Err = AnnotationError;

    fn visit_decl(&mut self, decl: &mut DeclKind) -> Result<(), Self::Err> {
        if let DeclKind::ProcDecl(decl_ref) = decl {
            self.direction = Some(decl_ref.borrow().direction);
            self.visit_proc(decl_ref)?;
        }
        Ok(())
    }

    fn visit_stmts(&mut self, stmts: &mut Vec<Stmt>) -> Result<(), Self::Err> {
        // Check if the program consists of only one loop
        let mut encoding: Option<(Rc<dyn Encoding>, Span)> = None;

        let mut is_one_loop = true;
        for s in &mut *stmts {
            match &mut s.node {
                StmtKind::Annotation(ident, _, _) => {
                    if let DeclKind::AnnotationDecl(AnnotationKind::Encoding(anno_ref)) =
                        self.tcx.get(*ident).unwrap().as_ref()
                    {
                        encoding = Some((anno_ref.clone(), s.span));
                    }
                }
                StmtKind::Var(_) => {}
                _ => {
                    is_one_loop = false;
                }
            }
        }
        // If the annotated encoding only supports one loop programs throw an error
        if let Some((enc, span)) = encoding {
            if enc.is_one_loop() && !is_one_loop {
                return Err(AnnotationError::OneLoopOnly(span, enc.name()));
            }
        }

        for s in stmts {
            self.visit_stmt(s)?;
        }
        Ok(())
    }

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Self::Err> {
        if let StmtKind::Annotation(ident, inputs, inner_stmt) = &mut s.node {
            if let DeclKind::AnnotationDecl(AnnotationKind::Encoding(anno_ref)) =
                self.tcx.get(*ident).unwrap().as_ref()
            {
                if let StmtKind::While(_, _) = inner_stmt.node {
                } else {
                    return Err(AnnotationError::NotOnWhile(s.span, *ident, s.clone()));
                }

                let (span, stmts, decls_opt) = anno_ref.transform(
                    self.tcx,
                    s.span,
                    inputs,
                    inner_stmt,
                    self.direction
                        .ok_or(AnnotationError::NotInProcedure(s.span, *ident))?,
                )?;
                s.span = span;
                s.node = StmtKind::Block(stmts);
                if let Some(decls) = decls_opt {
                    let items: Vec<Item<SourceUnit>> = decls
                        .into_iter()
                        .map(|decl| SourceUnit::Decl(decl).wrap_item(&SourceFilePath::Generated))
                        .collect();

                    self.source_units_buf.extend(items)
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {

    use pretty_assertions::assert_eq;

    fn remove_whitespace(s: &mut String) {
        s.retain(|c| !c.is_whitespace());
    }

    use crate::single_desugar_test;
    use crate::verify_test;

    #[test]
    fn test_k_induction_transform() {
        let mut test_string = String::from(
            r#"
            proc main() -> () 
                pre ∞
                post ∞
            {
                var x: UInt
                {
                    assert cast(EUReal, x)
                    havoc x
                    validate
                    assume cast(EUReal, x)
                    if (1 <= x) {
                        x = (x - 1)
                        assert cast(EUReal, x)
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
    fn test_bmc_transform() {
        let mut test_string = String::from(
            r#"
            proc main() -> () 
                pre ∞
                post ∞
            {
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
                @bmc(1, x)
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
    fn test_omega_transform() {
        let mut test_string = String::from(
            r#"
            proc main() -> () 
                pre ∞
                post ∞
            {
                var x: UInt
                {
                    cohavoc n
                    assert [(n > x)]
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
                @omega_inv(n,[n > x])
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
    fn test_ost_transform() {
        let mut test_string = String::from(
            r#"
            proc lt_infinity(a: Bool) -> () {
                assert ?(((cast(EUReal, 2) * [a]) < ∞))
            }
            proc past(init_prob_choice: Bool, init_a: Bool, init_b: UInt, init_k: UInt) -> (
                prob_choice: Bool, a: Bool, b: UInt, k: UInt
            )
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
                    assert (cast(EUReal, 2) * [a])
                    assume cast(EUReal, 0)
                } else {
            
                }
            }
            proc conditional_difference_bounded(
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
            proc harmonize_I_f(a: Bool, b: UInt) -> () {
                assert ?((! (a) → ((cast(EUReal, b) + [a]) == cast(EUReal, b))))
            }
            proc loopiter_lt_infty(
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
                    assert (cast(EUReal, b) + [a])
                    assume cast(EUReal, 0)
                } else {
            
                }
            }
            proc lower_bound(
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
            proc optional_stopping(init_b: UInt, init_a: Bool) -> (b: UInt, a: Bool)
                pre (cast(EUReal, init_b) + [init_a])
                post cast(EUReal, b)
            {
                var prob_choice: Bool
                var k: UInt
                b = init_b
                a = init_a
                { prob_choice, a, b, k = lower_bound(prob_choice, a, b, k) }
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
            proc condition_1(x: UInt) -> () {
                assert ?((([! ((1 <= x))] * cast(EUReal, (x + 1))) <= 10/10))
            }
            proc condition_2(x: UInt) -> () {
                assert (
                    ([(1 <= x)] * 10/10) <= (
                        ([(1 <= x)] * cast(EUReal, (x + 1))) + [! ((1 <= x))]
                    )
                )
            }
            proc past(init_x: UInt) -> (x: UInt)
                pre ([(1 <= x)] * ((cast(EUReal, (x + 1)))[x -> init_x] - 5/10))
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
            proc main() -> ()
                pre ∞
                post ∞
            {
                var x: UInt
                {  }
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
    fn test_ast_transform() {
        let mut test_string = String::from(
            r#"
        proc prob_antitone(a: UReal, b: UReal) -> ()
            pre ?((a <= b))
            post ?(((5/10)[v -> a] >= (5/10)[v -> b]))
        {
            
        }
        proc decrease_antitone(a: UReal, b: UReal) -> ()
            pre ?((a <= b))
            post ?(((cast(UReal, v))[v -> a] >= (cast(UReal, v))[v -> b]))
        {
            
        }
        proc I_wp_subinvariant(init_x: UInt) -> (x: UInt)
            pre ([true])[x -> init_x]
            post [true]
        {
            x = init_x
            if (1 <= x) { x = (x - 1) } else {  }
        }
        proc termination_condition(x: UInt) -> () {
            assert ?((! ((1 <= x)) == (cast(EUReal, x) == cast(EUReal, 0))))
        }
        proc V_wp_superinvariant(init_x: UInt) -> (x: UInt)
            pre (cast(EUReal, x))[x -> init_x]
            post cast(EUReal, x)
        {
            x = init_x
            if (1 <= x) { x = (x - 1) } else {  }
        }
        proc progress_condition(init_x: UInt) -> (x: UInt)
            pre (([true] * ([(1 <= x)] * (5/10)[v -> cast(EUReal, x)])))[x -> init_x]
            post [(
                cast(EUReal, x) <= (
                    (cast(EUReal, x))[x -> init_x] - (cast(UReal, v))[v -> (
                        cast(EUReal, x)
                    )[x -> init_x]]
                )
            )]
        {
            x = init_x
            x = (x - 1)
        }
        proc main() -> ()
            pre ∞
            post ∞
        {
            var x: UInt
            {  }
        }
        "#,
        );
        let source = r#"
            proc main() -> () {
                var x: UInt
                @ast(true, x, v, 0.5, v)
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
    fn test_past_not_on_while() {
        let source = r#"
    proc main() -> () {
        var x: UInt
        @past(x+1, 0.5, 1.0)
        x= x+1;
    }
"#;

        let err = verify_test(&source).0.unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error: The annotation `past` is not on a while statement"
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
        let err = verify_test(&source).0.unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error: The annotation `invariant` is not on a while statement"
        );
    }
}

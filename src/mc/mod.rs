//! Support for exporting HeyVL programs to JANI to run a model checker on them.

// TODO: handle name conflicts

mod opsem;
mod specs;

use std::{convert::TryInto, mem};

use ariadne::ReportKind;
use jani::{
    exprs::{BinaryExpression, BinaryOp, Expression, IteExpression},
    models::{
        Composition, CompositionElement, ConstantDeclaration, Metadata, Model, ModelFeature,
        VariableDeclaration,
    },
    types::{BasicType, BoundedType, BoundedTypeBase, Type},
    Identifier,
};

use crate::{
    ast::{
        util::{is_bot_lit, is_top_lit},
        visit::VisitorMut,
        BinOpKind, DeclRef, Diagnostic, Expr, ExprBuilder, ExprData, ExprKind, Ident, Label,
        LitKind, ProcDecl, Shared, Span, Spanned, Stmt, TyKind, UnOpKind, VarDecl,
    },
    procs::proc_verify::verify_proc,
    tyctx::TyCtx,
    version::caesar_version_info,
    JaniOptions,
};

use self::{
    opsem::{translate_block, OpAutomaton},
    specs::{extract_properties, SpecAutomaton},
};

#[derive(Debug)]
pub enum JaniConversionError {
    UnsupportedType(TyKind, Span),
    UnsupportedExpr(Expr),
    UnsupportedStmt(Box<Stmt>),
    UnsupportedPre(Expr),
    UnsupportedAssume(Expr),
    UnsupportedAssert(Expr),
    UnsupportedInftyPost(Expr),
    NondetSelection(Span),
    MismatchedDirection(Span),
    UnsupportedCall(Span, Ident),
}

impl JaniConversionError {
    pub fn diagnostic(&self) -> Diagnostic {
        match &self {
            JaniConversionError::UnsupportedType(ty, span) => {
                Diagnostic::new(ReportKind::Error, *span)
                    .with_message(format!("JANI: Type {} is not supported", ty))
                    .with_label(Label::new(*span).with_message("here"))
            }
            JaniConversionError::UnsupportedExpr(expr) => {
                Diagnostic::new(ReportKind::Error, expr.span)
                    .with_message("JANI: Expression is not supported")
                    .with_label(Label::new(expr.span).with_message("here"))
            }
            JaniConversionError::UnsupportedStmt(stmt) => {
                Diagnostic::new(ReportKind::Error, stmt.span)
                    .with_message("JANI: Statement is not supported")
                    .with_label(Label::new(stmt.span).with_message("here"))
            }
            JaniConversionError::UnsupportedPre(expr) => {
                Diagnostic::new(ReportKind::Error, expr.span)
                    .with_message("JANI: Pre must be a Boolean expression")
                    .with_label(Label::new(expr.span).with_message("expected ?(b) here"))
                    .with_note("You can ignore quantitative pre for JANI generation with the option --jani-skip-quant-pre.")
            }
            JaniConversionError::UnsupportedAssume(expr) => {
                Diagnostic::new(ReportKind::Error, expr.span)
                    .with_message("JANI: Assumption must be a Boolean expression")
                    .with_label(Label::new(expr.span).with_message("expected ?(b) here"))
            }
            JaniConversionError::UnsupportedAssert(expr) => {
                Diagnostic::new(ReportKind::Error, expr.span)
                    .with_message("JANI: Assertion must be a Boolean expression")
                    .with_label(Label::new(expr.span).with_message("expected ?(b) here"))
            }
            JaniConversionError::UnsupportedInftyPost(expr) => {
                Diagnostic::new(ReportKind::Error, expr.span)
                    .with_message("JANI: Post that evaluates to ∞ is not supported")
                    .with_label(Label::new(expr.span).with_message("post can evaluate to ∞"))
            }
            JaniConversionError::NondetSelection(span) => Diagnostic::new(ReportKind::Error, *span)
                .with_message("JANI: All variables must be initialized")
                .with_label(Label::new(*span).with_message("missing initializer")),
            JaniConversionError::MismatchedDirection(span) => {
                Diagnostic::new(ReportKind::Error, *span)
                    .with_message("JANI: Statement of other direction expected")
                    .with_label(Label::new(*span).with_message("here"))
            }
            JaniConversionError::UnsupportedCall(span, ident) => {
                Diagnostic::new(ReportKind::Error, *span)
                    .with_message(format!("JANI: Cannot call '{}'", ident.name))
                    .with_label(Label::new(*span).with_message("here"))
            }
        }
    }
}

pub fn proc_to_model(
    options: &JaniOptions,
    tcx: &TyCtx,
    proc: &ProcDecl,
) -> Result<Model, JaniConversionError> {
    // initialize the spec automaton
    let spec_part = SpecAutomaton::new(proc.direction);
    let mut verify_unit = verify_proc(proc).unwrap();
    let property = extract_properties(
        proc.span,
        &spec_part,
        &mut verify_unit.block.node,
        options.jani_skip_quant_pre,
    )?;

    // initialize the rest of the automaton
    let mut op_automaton = OpAutomaton::new(tcx, spec_part);

    // translate the variables
    let (constants, variables) = translate_var_decls(options, proc)?;
    op_automaton.variables.extend(variables);

    // translate the statements
    let next = op_automaton.spec_part.end_location();
    let start = translate_block(&mut op_automaton, &verify_unit.block, next)?;

    // now finish building the automaton
    let automaton_name = Identifier(proc.name.to_string());
    let (model_type, mut automaton) =
        op_automaton.finish(automaton_name, start, property.sink_reward);

    let mut model = Model::new(model_type);

    // Metadata
    model.metadata = Some(Metadata {
        description: Some(
            format!(
                "Created by the Caesar deductive verifier ({}).",
                caesar_version_info()
            )
            .into_boxed_str(),
        ),
        ..Default::default()
    });

    // Features
    model.features.push(ModelFeature::DerivedOperators);
    model.features.push(ModelFeature::StateExitRewards);

    // Declare the proc inputs as model parameters
    // TODO: add an option to instead declare the proc parameters as
    // (indeterminate) inputs to the automaton
    model.constants.extend(constants);

    // Make all of the automaton's variables public so they can be accessed by
    // properties (in particular our reward property).
    model.variables = mem::take(&mut automaton.variables);

    // Restriction on initial states from the pre
    model.restrict_initial = Some(property.restrict_initial.into());

    // Add the properties
    model.properties.extend(property.properties);

    // The system consists just of the one automaton
    model.system = Composition {
        elements: vec![CompositionElement {
            automaton: automaton.name.clone(),
            input_enable: None,
            comment: None,
        }],
        syncs: None,
        comment: None,
    };

    // Add the automaton
    model.automata.push(automaton);

    Ok(model)
}

/// Translate variable declarations, including local variable declarations, as
/// well as input and output parameters.
fn translate_var_decls(
    options: &JaniOptions,
    proc: &ProcDecl,
) -> Result<(Vec<ConstantDeclaration>, Vec<VariableDeclaration>), JaniConversionError> {
    let mut vars = translate_local_decls(proc)?;

    // we declare proc inputs as constants, not variables
    let mut constants = vec![];
    for param in proc.inputs.node.iter() {
        constants.push(ConstantDeclaration {
            name: Identifier(param.name.to_string()),
            typ: translate_type(&param.ty, param.span)?,
            value: None,
            comment: None,
        });
    }

    // proc outputs are normal variables
    for param in proc.outputs.node.iter() {
        let (comment, initial_value) = if !options.jani_uninit_outputs {
            arbitrarily_choose_initial(&param.ty)?
        } else {
            (None, None)
        };
        vars.push(VariableDeclaration {
            name: Identifier(param.name.to_string()),
            typ: translate_type(&param.ty, param.span)?,
            transient: false,
            initial_value: initial_value.map(Box::new),
            comment,
        });
    }

    Ok((constants, vars))
}

/// Create variable declarations for the local variables of a procedure.
fn translate_local_decls(proc: &ProcDecl) -> Result<Vec<VariableDeclaration>, JaniConversionError> {
    #[derive(Default)]
    struct VarDeclCollector(Vec<VariableDeclaration>);
    impl VisitorMut for VarDeclCollector {
        type Err = JaniConversionError;

        fn visit_var_decl(&mut self, var_ref: &mut DeclRef<VarDecl>) -> Result<(), Self::Err> {
            let decl = var_ref.borrow();
            let mut comment = None;
            let initial_value = if let Some(initial_expr) = &decl.init {
                if is_constant(initial_expr) {
                    Some(translate_expr(initial_expr)?)
                } else {
                    // only if the variable is immediately initialized, we can
                    // now choose an arbitrary initial value because that will
                    // be unobservable in the program.
                    let (comment_res, initial_value) = arbitrarily_choose_initial(&decl.ty)?;
                    comment = comment_res;
                    initial_value
                }
            } else {
                None
            };
            self.0.push(VariableDeclaration {
                name: Identifier(decl.name.to_string()),
                typ: translate_type(&decl.ty, decl.span)?,
                transient: false,
                initial_value: initial_value.map(Box::new),
                comment,
            });
            Ok(())
        }
    }
    let mut collector = VarDeclCollector::default();
    collector.visit_proc(&mut DeclRef::new(proc.clone()))?;
    Ok(collector.0)
}

fn arbitrarily_choose_initial(
    ty: &TyKind,
) -> Result<(Option<Box<str>>, Option<Expression>), JaniConversionError> {
    if let TyKind::Bool | TyKind::UInt | TyKind::UReal | TyKind::EUReal = ty {
        let comment = Some(
            "(initial value arbitrarily chosen by Caesar translation to reduce state space)"
                .to_string()
                .into_boxed_str(),
        );
        let builder = ExprBuilder::new(Span::dummy_span());
        let initial_value = Some(translate_expr(&builder.bot_lit(ty))?);
        Ok((comment, initial_value))
    } else {
        Ok((None, None))
    }
}

fn translate_type(ty: &TyKind, span: Span) -> Result<Type, JaniConversionError> {
    match ty {
        TyKind::Bool => Ok(Type::BasicType(BasicType::Bool)),
        TyKind::Int => Ok(Type::BasicType(BasicType::Int)),
        TyKind::UInt => Ok(Type::BoundedType(BoundedType {
            base: BoundedTypeBase::Int,
            lower_bound: Some(Box::new(0.into())),
            upper_bound: None,
        })),
        TyKind::Real => Ok(Type::BasicType(BasicType::Real)),
        TyKind::UReal => Ok(Type::BoundedType(BoundedType {
            base: BoundedTypeBase::Real,
            lower_bound: Some(Box::new(0.into())),
            upper_bound: None,
        })),
        TyKind::EUReal
        | TyKind::Tuple(_)
        | TyKind::List(_)
        | TyKind::Domain(_)
        | TyKind::String
        | TyKind::SpecTy
        | TyKind::Unresolved(_)
        | TyKind::None => Err(JaniConversionError::UnsupportedType(ty.clone(), span)),
    }
}

fn translate_ident(ident: Ident) -> Identifier {
    Identifier(ident.to_string())
}

fn translate_expr(expr: &Expr) -> Result<Expression, JaniConversionError> {
    let unsupported_expr_err = || JaniConversionError::UnsupportedExpr(expr.clone());

    match &expr.kind {
        ExprKind::Var(ident) => Ok(Expression::Identifier(translate_ident(*ident))),
        ExprKind::Call(_, _) => Err(unsupported_expr_err()),
        ExprKind::Ite(cond, left, right) => Ok(Expression::from(IteExpression {
            cond: translate_expr(cond)?,
            left: translate_expr(left)?,
            right: translate_expr(right)?,
        })),
        ExprKind::Binary(bin_op, left, right) => Ok(Expression::from(BinaryExpression {
            op: match bin_op.node {
                BinOpKind::Add => BinaryOp::Plus,
                BinOpKind::Sub => BinaryOp::Minus,
                BinOpKind::Mul => BinaryOp::Times,
                BinOpKind::Div => BinaryOp::Divide,
                BinOpKind::Mod => BinaryOp::Modulo,
                BinOpKind::And => BinaryOp::And,
                BinOpKind::Or => BinaryOp::Or,
                BinOpKind::Eq => BinaryOp::Equals,
                BinOpKind::Lt => BinaryOp::Less,
                BinOpKind::Le => BinaryOp::LessOrEqual,
                BinOpKind::Ne => BinaryOp::NotEquals,
                BinOpKind::Ge => BinaryOp::GreaterOrEqual,
                BinOpKind::Gt => BinaryOp::Greater,
                BinOpKind::Inf => BinaryOp::Min,
                BinOpKind::Sup => BinaryOp::Max,
                BinOpKind::Impl | BinOpKind::CoImpl | BinOpKind::Compare | BinOpKind::CoCompare => {
                    Err(unsupported_expr_err())?
                }
            },
            left: translate_expr(left)?,
            right: translate_expr(right)?,
        })),
        ExprKind::Unary(un_op, operand) => match un_op.node {
            // TODO: support other types as well
            UnOpKind::Not => {
                if expr.ty == Some(TyKind::Bool) {
                    Ok(!translate_expr(operand)?)
                } else {
                    Err(unsupported_expr_err())
                }
            }
            UnOpKind::Non => Err(unsupported_expr_err()),
            UnOpKind::Embed => Err(unsupported_expr_err()),
            UnOpKind::Iverson => Ok(Expression::from(IteExpression {
                cond: translate_expr(operand)?,
                left: 1.into(),
                right: 0.into(),
            })),
            UnOpKind::Parens => translate_expr(operand),
        },
        // TODO: for the cast we just hope for the best
        ExprKind::Cast(operand) => translate_expr(operand),
        ExprKind::Quant(_, _, _, _) => Err(unsupported_expr_err()),
        ExprKind::Subst(_, _, _) => todo!(),
        ExprKind::Lit(lit) => match &lit.node {
            LitKind::UInt(val) => Ok(Expression::from(
                TryInto::<u64>::try_into(*val).map_err(|_| unsupported_expr_err())?,
            )),
            LitKind::Bool(val) => Ok(Expression::from(*val)),
            LitKind::Frac(frac) => Ok(Expression::from(BinaryExpression {
                op: BinaryOp::Divide,
                left: TryInto::<u64>::try_into(frac.numer()).unwrap().into(),
                right: TryInto::<u64>::try_into(frac.denom()).unwrap().into(),
            })),
            LitKind::Str(_) | LitKind::Infinity => Err(unsupported_expr_err()),
        },
    }
}

/// Extract the Boolean expression out from an embed expression. This also
/// handles the `!?(expr)` idiom, returning `?(!expr)`, as well as top and
/// bottom literals.
fn extract_embed(expr: &Expr) -> Option<Expr> {
    if let ExprKind::Unary(op, operand) = &expr.kind {
        match op.node {
            UnOpKind::Embed => return Some(operand.clone()),
            UnOpKind::Not => {
                if let ExprKind::Unary(op, inner_operand) = &expr.kind {
                    if op.node == UnOpKind::Embed {
                        let builder = ExprBuilder::new(operand.span);
                        return Some(builder.unary(
                            UnOpKind::Not,
                            Some(TyKind::Bool),
                            inner_operand.clone(),
                        ));
                    }
                }
            }
            _ => {}
        }
    }
    if is_bot_lit(expr) {
        return Some(Shared::new(ExprData {
            kind: ExprKind::Lit(Spanned::new(expr.span, LitKind::Bool(false))),
            ty: Some(TyKind::Bool),
            span: expr.span,
        }));
    }
    if is_top_lit(expr) {
        return Some(Shared::new(ExprData {
            kind: ExprKind::Lit(Spanned::new(expr.span, LitKind::Bool(true))),
            ty: Some(TyKind::Bool),
            span: expr.span,
        }));
    }
    None
}

/// Whether an expression is a constant value and can be evaluated without any
/// other variables.
///
/// Right now, we just check directly that it is a literal. In the future, one
/// could allow more complex (constant) expressions as well.
fn is_constant(expr: &Expr) -> bool {
    matches!(expr.kind, ExprKind::Lit(_))
}

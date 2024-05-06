//! Support for exporting HeyVL programs to JANI to run a model checker on them.

// TODO: handle name conflicts

mod opsem;
mod specs;

use std::{convert::TryInto, mem};

use ariadne::ReportKind;
use jani::{
    exprs::{
        BinaryExpression, BinaryOp, ConstantValue, Expression, IteExpression, UnaryExpression,
        UnaryOp,
    },
    models::{
        Composition, CompositionElement, ConstantDeclaration, Metadata, Model, ModelFeature,
        ModelType, VariableDeclaration,
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
    version::self_version_info,
};

use self::{
    opsem::{translate_stmts, OpAutomaton},
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

#[derive(Debug)]
pub struct JaniOptions {
    pub skip_quant_pre: bool,
}

#[allow(clippy::field_reassign_with_default)]
pub fn proc_to_model(options: &JaniOptions, proc: &ProcDecl) -> Result<Model, JaniConversionError> {
    // initialize the spec automaton
    let spec_part = SpecAutomaton::new(proc.direction);
    let mut verify_unit = verify_proc(proc).unwrap();
    let property = extract_properties(&spec_part, &mut verify_unit.block, options.skip_quant_pre)?;

    // initialize the rest of the automaton
    let mut op_automaton = OpAutomaton::new(spec_part);

    // translate the variables
    let (constants, variables) = translate_variables(proc)?;
    op_automaton.variables.extend(variables);

    // translate the statements
    let next = op_automaton.spec_part.end_location();
    let start = translate_stmts(&mut op_automaton, &verify_unit.block, next)?;

    // now finish building the automaton
    let automaton_name = Identifier(proc.name.to_string());
    let mut automaton = op_automaton.finish(automaton_name, start, property.sink_reward);

    // TODO: change to MDP if there's nondeterminism
    let mut model = Model::new(ModelType::Dtmc);

    // Metadata
    let mut metadata = Metadata::default();
    metadata.description = Some(
        format!(
            "Created by the Caesar deductive verifier ({}).",
            self_version_info()
        )
        .into_boxed_str(),
    );
    model.metadata = Some(metadata);

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

fn translate_variables(
    proc: &ProcDecl,
) -> Result<(Vec<ConstantDeclaration>, Vec<VariableDeclaration>), JaniConversionError> {
    #[derive(Default)]
    struct VarDeclCollector(Vec<VariableDeclaration>);

    impl VisitorMut for VarDeclCollector {
        type Err = JaniConversionError;

        fn visit_var_decl(&mut self, var_ref: &mut DeclRef<VarDecl>) -> Result<(), Self::Err> {
            let decl = var_ref.borrow();
            let mut comment = None;
            let initial_value = if let Some(initial_expr) = &decl.init {
                if matches!(initial_expr.kind, ExprKind::Lit(_)) {
                    Some(Box::new(translate_expr(initial_expr)?))
                } else {
                    let builder = ExprBuilder::new(Span::dummy_span());
                    if let TyKind::Bool | TyKind::UInt | TyKind::UReal | TyKind::EUReal = decl.ty {
                        comment = Some(
                            "(initial value arbitrarily chosen by Caesar translation to reduce state space)"
                                .to_string()
                                .into_boxed_str(),
                        );
                        Some(Box::new(translate_expr(&builder.bot_lit(&decl.ty))?))
                    } else {
                        None
                    }
                }
            } else {
                None
            };
            self.0.push(VariableDeclaration {
                name: Identifier(decl.name.to_string()),
                typ: translate_type(&decl.ty, decl.span)?,
                transient: false,
                initial_value,
                comment,
            });
            Ok(())
        }
    }

    let mut collector = VarDeclCollector::default();
    collector.visit_proc(&mut DeclRef::new(proc.clone()))?; // TODO: this clone should not be necessary
    let mut vars = collector.0;

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
    let builder = ExprBuilder::new(Span::dummy_span());
    for param in proc.outputs.node.iter() {
        let initial_value = translate_expr(&builder.bot_lit(&param.ty))?;
        vars.push(VariableDeclaration {
            name: Identifier(param.name.to_string()),
            typ: translate_type(&param.ty, param.span)?,
            transient: false,
            initial_value: Some(Box::new(initial_value)),
            comment: None,
        });
    }

    Ok((constants, vars))
}

fn translate_type(ty: &TyKind, span: Span) -> Result<Type, JaniConversionError> {
    match ty {
        TyKind::Bool => Ok(Type::BasicType(BasicType::Bool)),
        TyKind::Int => Ok(Type::BasicType(BasicType::Int)),
        TyKind::UInt => Ok(Type::BoundedType(BoundedType {
            base: BoundedTypeBase::Int,
            lower_bound: Some(Box::new(Expression::Constant(ConstantValue::Number(
                0.into(),
            )))),
            upper_bound: None,
        })),
        TyKind::Real => Ok(Type::BasicType(BasicType::Real)),
        TyKind::UReal => Ok(Type::BoundedType(BoundedType {
            base: BoundedTypeBase::Real,
            lower_bound: Some(Box::new(Expression::Constant(ConstantValue::Number(
                0.into(),
            )))),
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
    match &expr.kind {
        ExprKind::Var(ident) => Ok(Expression::Identifier(translate_ident(*ident))),
        ExprKind::Call(_, _) => Err(JaniConversionError::UnsupportedExpr(expr.clone())),
        ExprKind::Ite(cond, left, right) => Ok(Expression::IfThenElse(Box::new(IteExpression {
            cond: translate_expr(cond)?,
            left: translate_expr(left)?,
            right: translate_expr(right)?,
        }))),
        ExprKind::Binary(bin_op, left, right) => {
            Ok(Expression::Binary(Box::new(BinaryExpression {
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
                    BinOpKind::Impl
                    | BinOpKind::CoImpl
                    | BinOpKind::Compare
                    | BinOpKind::CoCompare => {
                        Err(JaniConversionError::UnsupportedExpr(expr.clone()))?
                    }
                },
                left: translate_expr(left)?,
                right: translate_expr(right)?,
            })))
        }
        ExprKind::Unary(un_op, operand) => match un_op.node {
            // TODO: support other types as well
            UnOpKind::Not => Ok(Expression::Unary(Box::new(UnaryExpression {
                op: UnaryOp::Not,
                exp: translate_expr(operand)?,
            }))),
            UnOpKind::Non => todo!(),
            UnOpKind::Embed => todo!(),
            UnOpKind::Iverson => Ok(Expression::IfThenElse(Box::new(IteExpression {
                cond: translate_expr(operand)?,
                left: Expression::Constant(ConstantValue::Number(1.into())),
                right: Expression::Constant(ConstantValue::Number(0.into())),
            }))),
            UnOpKind::Parens => translate_expr(operand),
        },
        // TODO: for the cast we just hope for the best
        ExprKind::Cast(operand) => translate_expr(operand),
        ExprKind::Quant(_, _, _, _) => todo!(),
        ExprKind::Subst(_, _, _) => todo!(),
        ExprKind::Lit(lit) => match &lit.node {
            LitKind::UInt(val) => Ok(Expression::Constant(ConstantValue::Number(
                TryInto::<u64>::try_into(*val)
                    .map_err(|_| JaniConversionError::UnsupportedExpr(expr.clone()))?
                    .into(),
            ))),
            LitKind::Bool(val) => Ok(Expression::Constant(ConstantValue::Boolean(*val))),
            LitKind::Frac(frac) => Ok(Expression::Binary(Box::new(BinaryExpression {
                op: BinaryOp::Divide,
                left: Expression::Constant(ConstantValue::Number(
                    TryInto::<u64>::try_into(frac.numer()).unwrap().into(),
                )),
                right: Expression::Constant(ConstantValue::Number(
                    TryInto::<u64>::try_into(frac.denom()).unwrap().into(),
                )),
            }))),
            LitKind::Str(_) | LitKind::Infinity => {
                Err(JaniConversionError::UnsupportedExpr(expr.clone()))
            }
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

//! Support for exporting HeyVL programs to JANI to run a model checker on them.

// TODO: handle name conflicts

mod opsem;
pub mod run_storm;
mod specs;

use std::{cell::RefCell, collections::HashSet, convert::TryInto, mem};

use ariadne::ReportKind;
use jani::{
    exprs::{BinaryExpression, BinaryOp, CallExpression, Expression, IteExpression},
    models::{
        Composition, CompositionElement, ConstantDeclaration, FunctionDefinition, Metadata, Model,
        ModelFeature, ParameterDefinition, VariableDeclaration,
    },
    types::{BasicType, BoundedType, BoundedTypeBase, Type},
    Identifier,
};
use lsp_types::NumberOrString;

use crate::{
    ast::{
        util::{is_bot_lit, is_top_lit},
        visit::VisitorMut,
        BinOpKind, DeclKind, DeclRef, Diagnostic, Expr, ExprBuilder, ExprData, ExprKind, Ident,
        Label, LitKind, ProcDecl, Shared, Span, Spanned, Stmt, TyKind, UnOpKind, VarDecl,
    },
    procs::proc_verify::verify_proc,
    tyctx::TyCtx,
    version::caesar_version_info,
    ModelCheckingOptions,
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
    UnsupportedHavoc { stmt: Stmt, can_eliminate: bool },
    UnsupportedInftyPost(Expr),
    NondetSelection(Span),
    MismatchedDirection(Span),
    UnsupportedCall(Span, Ident),
    UnsupportedCalculus { proc: Ident, calculus: Ident },
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
            JaniConversionError::UnsupportedHavoc {stmt, can_eliminate} => {
                let diagnostic = Diagnostic::new(ReportKind::Error, stmt.span)
                    .with_message("JANI: Havoc is not supported")
                    .with_label(Label::new(stmt.span).with_message("here"));
                if *can_eliminate {
                    diagnostic.with_note("You can replace the havoc with a re-declaration of its variables.")
                } else {
                    diagnostic
                }
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
                    .with_label(Label::new(*span).with_message("must be a func with a body"))
            }
            JaniConversionError::UnsupportedCalculus { proc, calculus }=> Diagnostic::new(ReportKind::Error, proc.span)
                .with_message(format!("JANI: Calculus '{}' is not supported", calculus))
                .with_label(Label::new(proc.span).with_message("here")),
        }
        .with_code(NumberOrString::String("model checking".to_owned()))
    }
}

pub fn proc_to_model(
    options: &ModelCheckingOptions,
    tcx: &TyCtx,
    proc: &ProcDecl,
) -> Result<Model, JaniConversionError> {
    check_calculus_annotation(proc)?;

    let expr_translator = ExprTranslator::new(tcx);

    // initialize the spec automaton
    let spec_part = SpecAutomaton::new(proc.direction);
    let mut verify_unit = verify_proc(proc).unwrap();
    let property = extract_properties(
        proc.span,
        &spec_part,
        &expr_translator,
        &mut verify_unit.block.node,
        options.jani_skip_quant_pre,
    )?;

    // initialize the rest of the automaton
    let mut op_automaton = OpAutomaton::new(&expr_translator, spec_part);

    // translate the variables
    let (constants, variables) = translate_var_decls(options, &expr_translator, proc)?;
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

    // Translate functions
    model.functions.extend(translate_fns(&expr_translator)?);
    if !model.functions.is_empty() {
        model.features.push(ModelFeature::Functions);
    }

    // Declare the proc inputs as model parameters
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

fn check_calculus_annotation(proc: &ProcDecl) -> Result<(), JaniConversionError> {
    if let Some(calculus) = proc.calculus {
        if &calculus.name != "wp" && &calculus.name != "ert"
        // yeah that's ugly
        {
            return Err(JaniConversionError::UnsupportedCalculus {
                proc: proc.name,
                calculus,
            });
        }
    }
    Ok(())
}

/// Translate variable declarations, including local variable declarations, as
/// well as input and output parameters.
fn translate_var_decls(
    options: &ModelCheckingOptions,
    expr_translator: &ExprTranslator<'_>,
    proc: &ProcDecl,
) -> Result<(Vec<ConstantDeclaration>, Vec<VariableDeclaration>), JaniConversionError> {
    let mut vars = translate_local_decls(expr_translator, proc)?;

    // by default, proc inputs are translated as constants
    let mut constants = vec![];
    for param in proc.inputs.node.iter() {
        if !options.jani_no_constants {
            constants.push(ConstantDeclaration {
                name: Identifier(param.name.to_string()),
                typ: translate_type(&param.ty, param.span)?,
                value: None,
                comment: None,
            });
        } else {
            vars.push(VariableDeclaration {
                name: Identifier(param.name.to_string()),
                typ: translate_type(&param.ty, param.span)?,
                transient: false,
                initial_value: None,
                comment: None,
            });
        }
    }

    // proc outputs are normal variables
    for param in proc.outputs.node.iter() {
        let (comment, initial_value) = if !options.jani_uninit_outputs {
            arbitrarily_choose_initial(expr_translator, &param.ty)?
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
fn translate_local_decls(
    expr_translator: &ExprTranslator<'_>,
    proc: &ProcDecl,
) -> Result<Vec<VariableDeclaration>, JaniConversionError> {
    struct VarDeclCollector<'a> {
        expr_translator: &'a ExprTranslator<'a>,
        decls: Vec<VariableDeclaration>,
    }
    impl<'a> VisitorMut for VarDeclCollector<'a> {
        type Err = JaniConversionError;

        fn visit_var_decl(&mut self, var_ref: &mut DeclRef<VarDecl>) -> Result<(), Self::Err> {
            let decl = var_ref.borrow();
            let mut comment = None;
            let initial_value = if let Some(initial_expr) = &decl.init {
                if is_constant(initial_expr) {
                    Some(self.expr_translator.translate(initial_expr)?)
                } else {
                    // only if the variable is immediately initialized, we can
                    // now choose an arbitrary initial value because that will
                    // be unobservable in the program.
                    let (comment_res, initial_value) =
                        arbitrarily_choose_initial(self.expr_translator, &decl.ty)?;
                    comment = comment_res;
                    initial_value
                }
            } else {
                None
            };
            self.decls.push(VariableDeclaration {
                name: Identifier(decl.name.to_string()),
                typ: translate_type(&decl.ty, decl.span)?,
                transient: false,
                initial_value: initial_value.map(Box::new),
                comment,
            });
            Ok(())
        }
    }
    let mut collector = VarDeclCollector {
        expr_translator,
        decls: Vec::new(),
    };
    collector.visit_proc(&mut DeclRef::new(proc.clone()))?;
    Ok(collector.decls)
}

fn arbitrarily_choose_initial(
    expr_translator: &ExprTranslator<'_>,
    ty: &TyKind,
) -> Result<(Option<Box<str>>, Option<Expression>), JaniConversionError> {
    if let TyKind::Bool | TyKind::UInt | TyKind::UReal | TyKind::EUReal = ty {
        let comment = Some(
            "(initial value arbitrarily chosen by Caesar translation to reduce state space)"
                .to_string()
                .into_boxed_str(),
        );
        let builder = ExprBuilder::new(Span::dummy_span());
        let initial_value = Some(expr_translator.translate(&builder.bot_lit(ty))?);
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

struct ExprTranslator<'a> {
    tcx: &'a TyCtx,
    mentioned_funcs: RefCell<HashSet<Ident>>,
}

impl<'a> ExprTranslator<'a> {
    fn new(tcx: &'a TyCtx) -> Self {
        Self {
            tcx,
            mentioned_funcs: Default::default(),
        }
    }

    fn translate(&self, expr: &Expr) -> Result<Expression, JaniConversionError> {
        let unsupported_expr_err = || JaniConversionError::UnsupportedExpr(expr.clone());

        match &expr.kind {
            ExprKind::Var(ident) => Ok(Expression::Identifier(translate_ident(*ident))),
            ExprKind::Call(ident, args) => self.translate_call(expr, ident, args),
            ExprKind::Ite(cond, left, right) => Ok(Expression::from(IteExpression {
                cond: self.translate(cond)?,
                left: self.translate(left)?,
                right: self.translate(right)?,
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
                    BinOpKind::Impl
                    | BinOpKind::CoImpl
                    | BinOpKind::Compare
                    | BinOpKind::CoCompare => Err(unsupported_expr_err())?,
                },
                left: self.translate(left)?,
                right: self.translate(right)?,
            })),
            ExprKind::Unary(un_op, operand) => match un_op.node {
                // TODO: support other types as well
                UnOpKind::Not => {
                    if expr.ty == Some(TyKind::Bool) {
                        Ok(!self.translate(operand)?)
                    } else {
                        Err(unsupported_expr_err())
                    }
                }
                UnOpKind::Non => Err(unsupported_expr_err()),
                UnOpKind::Embed => Err(unsupported_expr_err()),
                UnOpKind::Iverson => Ok(Expression::from(IteExpression {
                    cond: self.translate(operand)?,
                    left: 1.into(),
                    right: 0.into(),
                })),
                UnOpKind::Parens => self.translate(operand),
            },
            // TODO: for the cast we just hope for the best
            ExprKind::Cast(operand) => self.translate(operand),
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

    /// We can translate calls to pure funcs.
    fn translate_call(
        &self,
        expr: &Expr,
        ident: &Ident,
        args: &[Expr],
    ) -> Result<Expression, JaniConversionError> {
        if let Some(decl) = self.tcx.get(*ident) {
            match &*decl {
                DeclKind::FuncDecl(func) => {
                    let func = func.borrow();
                    if func.body.borrow().is_none() {
                        Err(JaniConversionError::UnsupportedCall(expr.span, *ident))
                    } else {
                        self.mentioned_funcs.borrow_mut().insert(*ident);

                        Ok(Expression::from(CallExpression {
                            function: translate_ident(*ident),
                            args: args
                                .iter()
                                .map(|arg| self.translate(arg))
                                .collect::<Result<Vec<_>, _>>()?,
                        }))
                    }
                }
                _ => Err(JaniConversionError::UnsupportedCall(expr.span, *ident)),
            }
        } else {
            Err(JaniConversionError::UnsupportedCall(expr.span, *ident))
        }
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

/// Translate functions with bodies to JANI function definitions.
///
/// This uses a worklist algorithm to find all functions that are mentioned in
/// the given `expr_translator`, as well as in the functions' bodies that we
/// translate. For those, we also translate their dependencies.
fn translate_fns(
    expr_translator: &ExprTranslator<'_>,
) -> Result<Vec<FunctionDefinition>, JaniConversionError> {
    let mut worklist = expr_translator.mentioned_funcs.borrow().clone();
    let mut done_list = HashSet::new();

    let mut functions = vec![];

    while let Some(ident) = worklist.iter().next().cloned() {
        worklist.remove(&ident);

        if done_list.contains(&ident) {
            continue;
        }
        done_list.insert(ident);

        let decl = expr_translator.tcx.get(ident).unwrap();
        if let DeclKind::FuncDecl(func_ref) = &*decl {
            let func = func_ref.borrow();
            let body = func.body.borrow();
            if let Some(body) = &*body {
                let definition = FunctionDefinition {
                    name: Identifier(func.name.to_string()),
                    typ: translate_type(&func.output, func.span)?,
                    parameters: func
                        .inputs
                        .node
                        .iter()
                        .map(|param| {
                            Ok(ParameterDefinition {
                                name: Identifier(param.name.to_string()),
                                typ: translate_type(&param.ty, param.span)?,
                            })
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                    body: expr_translator.translate(body)?,
                };
                functions.push(definition);
            } else {
                unreachable!();
            }
        } else {
            unreachable!()
        }

        worklist.extend(expr_translator.mentioned_funcs.borrow().iter());
    }

    Ok(functions)
}

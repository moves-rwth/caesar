use super::ast;

pub fn print_file(file: &ast::File) -> String {
    file.decls
        .iter()
        .map(print_decl)
        .collect::<Vec<_>>()
        .join("\n\n")
}

fn print_decl(decl: &ast::Decl) -> String {
    match decl {
        ast::Decl::Type(type_decl) => format!("type {}(0,==)", type_decl.name),
        ast::Decl::Function(function) => print_function(function),
        ast::Decl::Method(method) => print_method(method),
    }
}

fn print_function(function: &ast::FunctionDecl) -> String {
    let mut lines = vec![format!(
        "function {}({}): {}",
        function.name,
        join_params(&function.params),
        print_type(&function.return_ty)
    )];
    if let Some(body) = &function.body {
        lines.push("{".to_owned());
        lines.push(format!("    {}", print_expr(body)));
        lines.push("}".to_owned());
    }
    lines.join("\n")
}

fn print_method(method: &ast::MethodDecl) -> String {
    let mut header = format!(
        "method{} {}({})",
        if method.axiom { " {:axiom}" } else { "" },
        method.name,
        join_params(&method.params)
    );
    if !method.returns.is_empty() {
        header.push_str(&format!(" returns ({})", join_params(&method.returns)));
    }

    let mut lines = vec![header];
    for requires in &method.requires {
        lines.push(format!("    requires {}", print_expr(requires)));
    }
    for ensures in &method.ensures {
        lines.push(format!("    ensures {}", print_expr(ensures)));
    }
    if method.decreases_star {
        lines.push("    decreases *".to_owned());
    }
    if let Some(body) = &method.body {
        lines.push("{".to_owned());
        lines.extend(print_block(body, 4));
        lines.push("}".to_owned());
    }
    lines.join("\n")
}

fn print_block(block: &ast::Block, indent: usize) -> Vec<String> {
    let mut lines = Vec::new();
    for stmt in &block.stmts {
        lines.extend(print_stmt(stmt, indent));
    }
    lines
}

fn print_stmt(stmt: &ast::Stmt, indent: usize) -> Vec<String> {
    let pad = " ".repeat(indent);
    match stmt {
        ast::Stmt::Block(block) => {
            let mut lines = vec![format!("{pad}{{")];
            lines.extend(print_block(block, indent + 4));
            lines.push(format!("{pad}}}"));
            lines
        }
        ast::Stmt::Var(var) => vec![match &var.init {
            ast::VarInit::Expr(expr) => format!(
                "{pad}var {}: {} := {};",
                var.name,
                print_type(&var.ty),
                print_expr(expr)
            ),
            ast::VarInit::MethodCall { method, args } => format!(
                "{pad}var {}: {} := {}({});",
                var.name,
                print_type(&var.ty),
                method,
                join_exprs(args)
            ),
            ast::VarInit::SuchThat(expr) => format!(
                "{pad}var {}: {} :| {};",
                var.name,
                print_type(&var.ty),
                print_expr(expr)
            ),
        }],
        ast::Stmt::Assign(assign) => {
            vec![format!(
                "{pad}{} := {};",
                assign.lhs,
                print_expr(&assign.rhs)
            )]
        }
        ast::Stmt::Call(call) => vec![format!("{pad}{}({});", call.method, join_exprs(&call.args))],
        ast::Stmt::AssignCall(call) => {
            let prefix = if call.lhs.is_empty() {
                String::new()
            } else {
                format!("{} := ", call.lhs.join(", "))
            };
            vec![format!(
                "{pad}{prefix}{}({});",
                call.method,
                join_exprs(&call.args)
            )]
        }
        ast::Stmt::SuchThatAssign(assign) => vec![format!(
            "{pad}{} :| {};",
            assign.lhs.join(", "),
            print_expr(&assign.predicate)
        )],
        ast::Stmt::Assert(assert) => vec![format!("{pad}assert {};", print_expr(&assert.expr))],
        ast::Stmt::Assume(assume) => vec![format!(
            "{pad}assume{} {};",
            if assume.axiom { " {:axiom}" } else { "" },
            print_expr(&assume.expr)
        )],
        ast::Stmt::If(if_stmt) => {
            let mut lines = vec![format!("{pad}if {} {{", print_expr(&if_stmt.cond))];
            lines.extend(print_block(&if_stmt.then_branch, indent + 4));
            lines.push(format!("{pad}}} else {{"));
            lines.extend(print_block(&if_stmt.else_branch, indent + 4));
            lines.push(format!("{pad}}}"));
            lines
        }
        ast::Stmt::While(while_stmt) => {
            let mut lines = vec![format!("{pad}while {}", print_expr(&while_stmt.cond))];
            for invariant in &while_stmt.invariants {
                lines.push(format!("{pad}    invariant {}", print_expr(invariant)));
            }
            if while_stmt.decreases_star {
                lines.push(format!("{pad}    decreases *"));
            }
            lines.push(format!("{pad}{{"));
            lines.extend(print_block(&while_stmt.body, indent + 4));
            lines.push(format!("{pad}}}"));
            lines
        }
    }
}

fn print_expr(expr: &ast::Expr) -> String {
    match expr {
        ast::Expr::Var(name) => name.clone(),
        ast::Expr::BoolLit(value) => value.to_string(),
        ast::Expr::NumberLit(value) => value.clone(),
        ast::Expr::StringLit(value) => format!("\"{}\"", value.escape_default()),
        ast::Expr::Call { function, args } => format!("{function}({})", join_exprs(args)),
        ast::Expr::Ite {
            cond,
            then_expr,
            else_expr,
        } => format!(
            "(if {} then {} else {})",
            print_expr(cond),
            print_expr(then_expr),
            print_expr(else_expr)
        ),
        ast::Expr::Binary { op, lhs, rhs } => format!(
            "({} {} {})",
            print_expr(lhs),
            print_binary_op(op),
            print_expr(rhs)
        ),
        ast::Expr::Unary { op, expr } => match op {
            ast::UnaryOp::Not => format!("!({})", print_expr(expr)),
            ast::UnaryOp::Parens => format!("({})", print_expr(expr)),
        },
        ast::Expr::Quantified {
            quantifier,
            vars,
            triggers,
            body,
        } => {
            let triggers = triggers
                .iter()
                .map(|trigger| format!(" {{:trigger {}}}", join_exprs(trigger)))
                .collect::<Vec<_>>()
                .join("");
            format!(
                "({} {}{} :: {})",
                print_quantifier(quantifier),
                join_quant_vars(vars),
                triggers,
                print_expr(body)
            )
        }
        ast::Expr::SeqLen(expr) => format!("|{}|", print_expr(expr)),
        ast::Expr::Index { collection, index } => {
            format!("{}[{}]", print_expr(collection), print_expr(index))
        }
        ast::Expr::Update {
            collection,
            index,
            value,
        } => format!(
            "{}[{} := {}]",
            print_expr(collection),
            print_expr(index),
            print_expr(value)
        ),
    }
}

fn print_binary_op(op: &ast::BinaryOp) -> &'static str {
    match op {
        ast::BinaryOp::Add => "+",
        ast::BinaryOp::Sub => "-",
        ast::BinaryOp::Mul => "*",
        ast::BinaryOp::Div => "/",
        ast::BinaryOp::Mod => "%",
        ast::BinaryOp::And => "&&",
        ast::BinaryOp::Or => "||",
        ast::BinaryOp::Eq => "==",
        ast::BinaryOp::Lt => "<",
        ast::BinaryOp::Le => "<=",
        ast::BinaryOp::Ne => "!=",
        ast::BinaryOp::Ge => ">=",
        ast::BinaryOp::Gt => ">",
        ast::BinaryOp::Impl => "==>",
    }
}

fn print_quantifier(quantifier: &ast::Quantifier) -> &'static str {
    match quantifier {
        ast::Quantifier::Forall => "forall",
        ast::Quantifier::Exists => "exists",
    }
}

fn print_type(ty: &ast::Type) -> String {
    match ty {
        ast::Type::Bool => "bool".to_owned(),
        ast::Type::Int => "int".to_owned(),
        ast::Type::Nat => "nat".to_owned(),
        ast::Type::Seq(element_ty) => format!("seq<{}>", print_type(element_ty)),
        ast::Type::Named(name) => name.clone(),
    }
}

fn join_params(params: &[ast::Param]) -> String {
    params
        .iter()
        .map(|param| format!("{}: {}", param.name, print_type(&param.ty)))
        .collect::<Vec<_>>()
        .join(", ")
}

fn join_quant_vars(vars: &[ast::QuantVar]) -> String {
    vars.iter()
        .map(|var| format!("{}: {}", var.name, print_type(&var.ty)))
        .collect::<Vec<_>>()
        .join(", ")
}

fn join_exprs(exprs: &[ast::Expr]) -> String {
    exprs.iter().map(print_expr).collect::<Vec<_>>().join(", ")
}

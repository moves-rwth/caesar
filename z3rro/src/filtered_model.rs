use z3::ast::Ast;

use crate::model::InstrumentedModel;

// Adds a filter to InstrumentedModel, which works by skipping evaluations of filtered out variables
pub struct FilteredModel<'ctx> {
    pub model: InstrumentedModel<'ctx>,
    filter: Box<dyn Fn(&str) -> bool + 'ctx>,
}

impl<'ctx> FilteredModel<'ctx> {
    pub fn new<F>(model: InstrumentedModel<'ctx>, filter: F) -> Self
    where
        F: Fn(&str) -> bool + 'ctx,
    {
        Self {
            model,
            filter: Box::new(filter),
        }
    }

    pub fn eval_ast<T: Ast<'ctx>>(&self, ast: &T, model_completion: bool) -> Option<T> {
        let decl = ast.decl();
        let name = decl.name().to_string();
        let passes_filter = (self.filter)(&name);
        if passes_filter {
            let result = self.model.model.eval(ast, model_completion);
            result
        } else {
            None
        }
    }
}

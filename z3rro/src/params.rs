//! Tracking of config options for Z3.

use std::{
    fmt::{self, Display, Formatter},
    sync::Mutex,
};

use indexmap::IndexMap;
use once_cell::sync::Lazy;

/// SMT parameters that we set, preserving insertion order of keys.
#[derive(Debug, Default, Clone)]
pub struct SmtParams {
    /// The parameter settings, from key to value.
    params: IndexMap<String, String>,
    /// Whether to set the options globally using [`z3::set_global_param`].
    global: bool,
}

static GLOBAL_SMT_PARAMS: Lazy<Mutex<SmtParams>> = Lazy::new(|| {
    Mutex::new(SmtParams {
        params: IndexMap::new(),
        global: true,
    })
});

impl SmtParams {
    /// Get access to the global SMT parameters. Using `set_param` on this
    /// object will also call [`z3::set_global_param`].
    pub fn global() -> &'static Mutex<SmtParams> {
        &GLOBAL_SMT_PARAMS
    }

    /// Set a parameter for the SMT solver.
    ///
    /// If this is the global parameters object, the parameter will be set
    /// globally using [`z3::set_global_param`].
    pub fn set_param(&mut self, key: &str, value: &str) {
        self.params.insert(key.to_string(), value.to_string());
        if self.global {
            z3::set_global_param(key, value);
        }
    }

    /// Add global parameters to this instance. Global parameters will be overwritten by parameters in this instance.
    pub fn add_global_params(&mut self) {
        let globals = SmtParams::global().lock().unwrap();
        // replace self.params with the globals...
        let self_params = std::mem::replace(&mut self.params, globals.params.clone());
        // and then re-add the (previous) self.params, so that we properly
        // overwrite global params by local ones.
        self.params.extend(self_params);
    }
}

/// Prints the params as SMT-LIB `set-option` commands, including global ones.
/// Note that this Display impl will not do any escaping.
impl Display for SmtParams {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut params = self.clone();
        params.add_global_params();
        for (key, value) in &params.params {
            writeln!(f, "(set-option :{} {})", key, value)?;
        }
        Ok(())
    }
}

//! Data structures to represent JANI models according to the [jani-model specification](https://docs.google.com/document/d/1BDQIzPBtscxJFFlDUEPIo8ivKHgXT8_X6hz5quq7jK0/edit).
//!
//! We include support for some extensions directly in the data structures.
//!
//! The main type is [`models::Model`], which can be read using [`from_str`] and
//! [`from_reader`] and serialized with [`to_string`].

pub mod exprs;
pub mod models;
pub mod properties;
pub mod types;

use std::io::Read;

use models::Model;
use serde::{Deserialize, Serialize};

/// An identifier.
///
/// Must not contain line breaks.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Identifier(pub String);

/// Parse a JANI model from a `&str`.
pub fn from_str(s: &str) -> serde_json::Result<Model> {
    serde_json::from_str(s)
}

/// Parse a JANI model from a reader.
pub fn from_reader<R>(rdr: R) -> serde_json::Result<Model>
where
    R: Read,
{
    serde_json::from_reader(rdr)
}

/// Convert a model into a (pretty-printed) JANI model, i.e. JSON according to
/// the JANI spec.
pub fn to_string(model: &Model) -> String {
    serde_json::to_string_pretty(model).unwrap()
}

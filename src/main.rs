// clippy (correctly) tells us that we can sometimes elide lifetimes, but many
// of these cases make the declarations way more clear than with implicit
// lifetimes.
#![allow(clippy::needless_lifetimes)]

use std::process::ExitCode;

use crate::driver::commands::CaesarCli;

mod ast;
mod depgraph;
mod driver;
mod front;
mod intrinsic;
mod mc;
mod opt;
mod pretty;
mod procs;
mod proof_rules;
mod resource_limits;
mod scope_map;
mod servers;
mod slicing;
mod smt;
mod timing;
mod tyctx;
mod vc;
mod version;

/// Caesar's main entry point redirects to [`CaesarCli::main`].
#[tokio::main]
async fn main() -> ExitCode {
    CaesarCli::main().await
}

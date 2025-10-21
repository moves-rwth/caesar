//! (CLI) command and option declarations to run Caesar with.

pub mod get_pre_models;
pub mod model_check;
pub mod options;
pub mod refinement;
pub mod run_lsp;
pub mod verify;

use std::{
    collections::HashMap,
    ffi::OsString,
    io,
    process::ExitCode,
    sync::{Arc, Mutex},
};

use clap::{crate_description, Args, CommandFactory, Parser, Subcommand};

use crate::{
    ast::FileId,
    driver::commands::{
        get_pre_models::run_nontrivial_model_command,
        model_check::{run_model_checking_command, ModelCheckCommand},
        options::{DebugOptions, InputOptions},
        refinement::run_verify_entailment_command,
        run_lsp::run_lsp_command,
        verify::{run_verify_command, VerifyCommand},
    },
    servers::{CliServer, SharedServer},
    timing::{self, DispatchBuilder, TimingLayer},
    version,
};

#[derive(Debug, Parser)]
#[command(
    name = "caesar",
    about = crate_description!(),
    long_about = "Caesar is a deductive verifier for probabilistic programs. Run the caesar binary with a subcommand to use it. Usually, you'll want to use the `verify` command.",
    version = version::clap_detailed_version_info()
)]
pub struct CaesarCli {
    #[command(subcommand)]
    pub command: CaesarCommand,
}

impl CaesarCli {
    pub async fn main() -> ExitCode {
        let options = CaesarCli::parse_and_normalize();

        if let Some(debug_options) = options.command.debug_options() {
            if debug_options.debug {
                let mut stderr = io::stderr().lock();
                version::write_detailed_command_info(&mut stderr).unwrap();
            }
            // install global collector configured based on RUST_LOG env var.
            timing::init_tracing(
                DispatchBuilder::default()
                    .json(debug_options.json)
                    .timing(debug_options.timing),
            );
        }

        match options.command {
            CaesarCommand::Verify(options) => run_verify_command(options).await,
            CaesarCommand::Entailment(options) => run_verify_entailment_command(options).await,
            CaesarCommand::Mc(options) => run_model_checking_command(options),
            CaesarCommand::Lsp(options) => run_lsp_command(options).await,
            CaesarCommand::ShellCompletions(options) => run_shell_completions_command(options),
            CaesarCommand::GetPreModels(options) => run_nontrivial_model_command(options).await,
            CaesarCommand::Other(_) => unreachable!(),
        }
    }

    fn parse_and_normalize() -> Self {
        let cli = Self::parse();
        match cli.command {
            CaesarCommand::Other(vec) => {
                // if it's an unrecognized command, parse as "verify" command
                Self::parse_from(
                    std::iter::once(std::env::args().next().unwrap().into())
                        .chain(std::iter::once("verify".into()))
                        .chain(vec),
                )
            }
            command => CaesarCli { command },
        }
    }
}

#[derive(Debug, Subcommand)]
pub enum CaesarCommand {
    /// Verify HeyVL files with Caesar.
    Verify(VerifyCommand),
    /// Check an entailment with Caesar.
    Entailment(VerifyCommand),
    /// Model checking via JANI, can run Storm directly.
    #[clap(visible_alias = "to-jani")]
    Mc(ModelCheckCommand),
    /// Run Caesar's LSP server.
    Lsp(VerifyCommand),
    /// Generate shell completions for the Caesar binary.
    ShellCompletions(ShellCompletionsCommand),
    /// Get non-trivial models for preexpectation.
    #[clap(visible_alias = "get-models")]
    GetPreModels(VerifyCommand),
    /// This is to support the default `verify` command.
    #[command(external_subcommand)]
    #[command(hide(true))]
    Other(Vec<OsString>),
}

impl CaesarCommand {
    pub fn debug_options(&self) -> Option<&DebugOptions> {
        match &self {
            CaesarCommand::Verify(verify_options) => Some(&verify_options.debug_options),
            CaesarCommand::Entailment(verify_options) => Some(&verify_options.debug_options),
            CaesarCommand::Lsp(verify_options) => Some(&verify_options.debug_options),
            CaesarCommand::Mc(mc_options) => Some(&mc_options.debug_options),
            CaesarCommand::ShellCompletions(_) => None,
            CaesarCommand::GetPreModels(verify_options) => Some(&verify_options.debug_options),
            CaesarCommand::Other(_vec) => unreachable!(),
        }
    }
}

fn mk_cli_server(input_options: &InputOptions) -> Result<(Vec<FileId>, SharedServer), ExitCode> {
    if input_options.files.is_empty() {
        eprintln!("Error: list of files must not be empty.\n");
        return Err(ExitCode::from(1));
    }
    let mut client = CliServer::new(input_options);
    let user_files: Vec<FileId> = input_options
        .files
        .iter()
        .map(|path| client.load_file(path))
        .collect();
    let server: SharedServer = Arc::new(Mutex::new(client));
    Ok((user_files, server))
}

fn print_timings() {
    let timings = TimingLayer::read_active().unwrap();
    let timings: HashMap<&'static str, String> = timings
        .iter()
        .map(|(key, value)| (*key, format!("{}", value.as_nanos())))
        .collect();
    eprintln!("Timings: {timings:?}");
}

#[derive(Debug, Default, Args)]
pub struct ShellCompletionsCommand {
    /// The shell for which to generate completions.
    #[arg(required(true), value_enum)]
    pub shell: Option<clap_complete::Shell>,
}

fn run_shell_completions_command(options: ShellCompletionsCommand) -> ExitCode {
    let binary_name = std::env::args().next().unwrap();
    clap_complete::aot::generate(
        options.shell.unwrap(),
        &mut CaesarCli::command(),
        binary_name,
        &mut std::io::stdout(),
    );
    ExitCode::SUCCESS
}

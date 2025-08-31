//! Module for running Storm directly from Caesar on generated JANI files.

use std::{
    io,
    path::Path,
    process::{Command, ExitStatus},
    time::Duration,
};

use ariadne::ReportKind;
use indexmap::IndexMap;
use lsp_types::NumberOrString;
use num::BigRational;
use regex::Regex;
use thiserror::Error;
use z3rro::util::PrettyRational;

use crate::{
    ast::{Diagnostic, Label, Span},
    driver::commands::options::{ModelCheckingOptions, RunWhichStorm},
    resource_limits::LimitsRef,
};

pub type StormResult = Result<StormOutput, StormError>;

pub fn storm_result_to_diagnostic(result: &StormResult, span: Span) -> Diagnostic {
    match result {
        Ok(output) => match output.results.get("reward").unwrap() {
            StormValue::Value(reward) => Diagnostic::new(ReportKind::Advice, span)
                .with_message(format!("Expected reward from Storm: {reward}"))
                .with_label(Label::new(span))
                .with_code(NumberOrString::String("model checking".to_owned())),
            StormValue::NotFound => Diagnostic::new(ReportKind::Error, span)
                .with_message("Could not find result from Storm")
                .with_label(Label::new(span))
                .with_code(NumberOrString::String("model checking".to_owned())),
            StormValue::NoInitialState => Diagnostic::new(ReportKind::Advice, span)
                .with_message("Model does not have an initial state")
                .with_label(Label::new(span))
                .with_code(NumberOrString::String("model checking".to_owned())),
        },
        Err(err) => Diagnostic::new(ReportKind::Error, span)
            .with_message(err)
            .with_label(Label::new(span))
            .with_code(NumberOrString::String("storm".to_owned())),
    }
}

#[derive(Debug)]
pub struct StormOutput {
    #[allow(unused)] // used in logging
    pub version: String,
    pub results: IndexMap<String, StormValue>,
}

#[derive(Debug)]
pub enum StormValue {
    NotFound,
    Value(String),
    NoInitialState,
}

#[derive(Debug, Error)]
pub enum StormError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),
    #[error("{0}: {1}")]
    StormFailed(ExitStatus, String),
    #[error("State exploration aborted after {} seconds, explored {} states", .0.as_secs(), .1)]
    StateExplorationAborted(Duration, usize),
    #[error("Docker is not running")]
    DockerNotRunning,
}

/// Run Storm on the given JANI file and look for output for the given properties.
///
/// Panics if `options.run_storm` is `None`.
pub fn run_storm(
    options: &ModelCheckingOptions,
    mut jani_file: &Path,
    properties: Vec<String>,
    limits_ref: &LimitsRef,
) -> Result<StormOutput, StormError> {
    let which_storm = options.run_storm.unwrap();
    let mut command = match which_storm {
        RunWhichStorm::Path => {
            if limits_ref.memory_limit().is_some() {
                tracing::debug!("Memory limit is ignored when running Storm from path");
            }

            Command::new("storm")
        }
        RunWhichStorm::DockerStable | RunWhichStorm::DockerCI => {
            let mut command = Command::new("docker");
            let jani_file_dir = jani_file.parent().unwrap().canonicalize().unwrap();
            jani_file = jani_file.file_name().unwrap().as_ref();
            let image_name = match which_storm {
                RunWhichStorm::DockerStable => "movesrwth/storm:stable",
                RunWhichStorm::DockerCI => "movesrwth/storm:ci",
                _ => unreachable!(),
            };
            command
                .arg("run")
                .arg("--rm")
                .arg("-v")
                .arg(format!("{}:/mnt", jani_file_dir.display()))
                .arg("-w")
                .arg("/mnt");

            if let Some(mem_limit) = limits_ref.memory_limit() {
                command
                    .arg("--memory")
                    .arg(format!("{}m", mem_limit.as_megabytes()));
            }

            command.arg(image_name).arg("storm");
            command
        }
    };

    let caesar_timeout = limits_ref.time_left();
    let storm_specific_timeout = options.storm_timeout();
    let timeout = caesar_timeout
        .and_then(|ct| storm_specific_timeout.map(|st| ct.min(st)))
        .or(caesar_timeout)
        .or(storm_specific_timeout);
    if let Some(timeout) = timeout {
        command.arg("--timeout").arg(timeout.as_secs().to_string());
    }

    if options.storm_exact {
        command.arg("--exact");
    }

    if let Some(storm_state_limit) = options.storm_state_limit {
        command
            .arg("--state-limit")
            .arg(storm_state_limit.to_string());
    }

    if let Some(storm_constants) = &options.storm_constants {
        command.arg("--constants").arg(storm_constants);
    }

    command
        .arg("--sound")
        .arg("--jani")
        .arg(jani_file)
        .arg("-jprop")
        .arg(properties.join(","));

    tracing::debug!("Running command: {:?}", &command);
    let output = command.output()?;

    let output_str = String::from_utf8(output.stdout).unwrap();
    if !output.status.success() {
        if output.status.code() == Some(125)
            && matches!(
                which_storm,
                RunWhichStorm::DockerStable | RunWhichStorm::DockerCI
            )
        {
            return Err(StormError::DockerNotRunning);
        }

        if output_str.contains("The model does not have a single initial state") {
            let version = output_str.lines().next().unwrap().to_string();
            return Ok(StormOutput {
                version,
                results: properties
                    .iter()
                    .map(|p| (p.clone(), StormValue::NoInitialState))
                    .collect(),
            });
        }

        let re = Regex::new(r"Explored (\d+) states in (\d+) seconds before abort").unwrap();
        if let Some(captures) = re.captures(&output_str) {
            let states_explored: usize = captures[1].parse().unwrap();
            let time_taken: u64 = captures[2].parse().unwrap();
            return Err(StormError::StateExplorationAborted(
                Duration::from_secs(time_taken),
                states_explored,
            ));
        }

        Err(StormError::StormFailed(output.status, output_str))
    } else {
        let results = parse_property_results(options, properties, &output_str);
        Ok(StormOutput {
            version: output_str.lines().next().unwrap().to_string(),
            results,
        })
    }
}

fn parse_property_results(
    options: &ModelCheckingOptions,
    properties: Vec<String>,
    output: &str,
) -> IndexMap<String, StormValue> {
    properties
        .into_iter()
        .map(|property| {
            let res = find_property_result(options, output, &property);
            (property, res)
        })
        .collect()
}

fn find_property_result(
    options: &ModelCheckingOptions,
    output: &str,
    property: &str,
) -> StormValue {
    const RESULT_TEXT: &str = "Result (for initial states):";

    let search_string = format!("Model checking property \"{property}\"");
    if let Some(start) = output.find(&search_string) {
        if let Some(result_start) = output[start..].find(RESULT_TEXT) {
            let result_start = start + result_start + RESULT_TEXT.len();
            if let Some(result_end) = output[result_start..].find('\n') {
                let mut result = &output[result_start..result_start + result_end];
                if result.contains("(approx. ") {
                    result = result.split("(approx. ").next().unwrap();
                };
                let mut result = result.trim().to_string();
                if options.storm_exact {
                    if let Ok(value) = result.parse::<BigRational>() {
                        let pretty = PrettyRational::from(value);
                        result = pretty.to_string()
                    }
                }
                let operator = match (options.storm_exact, options.storm_state_limit) {
                    (true, None) => "",
                    (true, Some(_)) => "≥ ",
                    (false, Some(_)) => "⪆ ",
                    (false, None) => "≈ ",
                };
                let result = format!("{operator}{result}");
                return StormValue::Value(result);
            }
        }
    }
    StormValue::NotFound
}

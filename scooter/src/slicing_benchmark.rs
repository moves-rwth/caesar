//! Running and evaluating slicing benchmarks.

#![allow(dead_code)]

use std::{
    fmt::Display,
    io::{self, Write},
    time::Duration,
};

use indicatif::ProgressBar;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::{
    runner::{run_benchmark, BenchmarkResult, BenchmarkTask},
    traces::TracingEventFields,
};

#[derive(Debug, Serialize)]
pub enum SliceResult {
    Success {
        info: SliceSuccessfulFields,
        time: Duration,
    },
    Failure {
        original_size: usize,
        time: Option<Duration>,
    },
    NotFound,
    AmbiguousProcs,
}

impl SliceResult {
    pub fn is_success(&self) -> bool {
        matches!(self, SliceResult::Success { .. })
    }

    pub fn as_success(&self) -> Option<(&SliceSuccessfulFields, Duration)> {
        match self {
            SliceResult::Success { info, time } => Some((info, *time)),
            _ => None,
        }
    }

    pub fn num_sliceable_statements(&self) -> Option<usize> {
        match self {
            SliceResult::Success { info, .. } => Some(info.slice_size + info.removed_statements),
            SliceResult::Failure { original_size, .. } => Some(*original_size),
            _ => None,
        }
    }
}

impl Display for SliceResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SliceResult::Success { info, time } => {
                write!(f, "✓ {} {:?}", info.slice_size, time)
            }
            SliceResult::Failure {
                original_size: _,
                time,
            } => {
                write!(f, "✗ {time:?}")
            }
            SliceResult::NotFound => write!(f, "BUG"),
            SliceResult::AmbiguousProcs => write!(f, "BUG"),
        }
    }
}

#[derive(Debug, Deserialize)]
#[serde(tag = "message")]
enum SliceTraceFields {
    #[serde(rename = "translated slice selection")]
    TranslatedSliceSelection(TranslatedSliceSelectionFields),
    #[serde(rename = "slicing successful")]
    SlicingSuccessful(SliceSuccessfulFields),
    #[serde(rename = "no slice accepted")]
    SlicingFailed,
}

#[derive(Debug, Deserialize)]
struct TranslatedSliceSelectionFields {
    active: usize,
    inactive: usize,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct SliceSuccessfulFields {
    pub slice_size: usize,
    pub removed_statements: usize,
    pub from_first_model: usize,
    pub found_slices: usize,
}

fn parse_slice_result(result: &BenchmarkResult, tracing_name: &str) -> SliceResult {
    let relevant_events = result.events.iter().filter(|event| {
        event
            .span
            .as_ref()
            .is_some_and(|span| span.name == tracing_name)
    });
    let mut total_time = None;
    let mut active = None;

    for event in relevant_events.clone().rev() {
        if let Ok(TracingEventFields::Close {
            time_busy,
            time_idle: _,
        }) = serde_json::from_value(Value::Object(event.fields.clone()))
        {
            if total_time.is_some() {
                return SliceResult::AmbiguousProcs;
            }
            total_time = Some(time_busy.0);
        }
    }

    for event in relevant_events {
        match serde_json::from_value(Value::Object(event.fields.clone())) {
            Ok(SliceTraceFields::TranslatedSliceSelection(fields)) => {
                active = Some(fields.active);
            }
            Ok(SliceTraceFields::SlicingSuccessful(fields)) => {
                return SliceResult::Success {
                    info: fields,
                    time: total_time.unwrap(),
                };
            }
            Ok(SliceTraceFields::SlicingFailed) => {
                return SliceResult::Failure {
                    original_size: active.unwrap(),
                    time: total_time,
                };
            }
            _ => {}
        }
    }
    SliceResult::NotFound
}

/// Results for slicing a benchmark file with different slicing strategies.
#[derive(Debug)]
pub struct SliceFileResults {
    task: BenchmarkTask,
    heyvl_loc: usize,
    kind: SliceFileResultsKind,
}

#[derive(Debug)]
pub enum SliceFileResultsKind {
    Error(ErroringSliceFileResults),
    Verifying(VerifyingSliceFileResults),
}

impl SliceFileResultsKind {
    pub fn iter(&self) -> Box<dyn Iterator<Item = &SliceResult> + '_> {
        match self {
            SliceFileResultsKind::Error(results) => Box::new(results.iter()),
            SliceFileResultsKind::Verifying(results) => Box::new(results.iter()),
        }
    }
}

#[derive(Debug)]
pub struct ErroringSliceFileResults {
    first_cex_slice: SliceResult,
    optimal_cex_slice: SliceResult,
}

impl ErroringSliceFileResults {
    pub fn iter(&self) -> impl Iterator<Item = &SliceResult> {
        vec![&self.first_cex_slice, &self.optimal_cex_slice].into_iter()
    }
}

#[derive(Debug)]
pub struct VerifyingSliceFileResults {
    core_slice: SliceResult,
    mus_slice: SliceResult,
    sus_slice: SliceResult,
    exists_forall_slice: SliceResult,
}

impl VerifyingSliceFileResults {
    pub fn iter(&self) -> impl Iterator<Item = &SliceResult> {
        vec![
            &self.core_slice,
            &self.mus_slice,
            &self.sus_slice,
            &self.exists_forall_slice,
        ]
        .into_iter()
    }
}

impl SliceFileResults {
    pub fn num_sliceable_statements(&self) -> usize {
        match &self.kind {
            SliceFileResultsKind::Error(results) => {
                results.first_cex_slice.num_sliceable_statements().unwrap()
            }
            SliceFileResultsKind::Verifying(results) => {
                results.core_slice.num_sliceable_statements().unwrap()
            }
        }
    }

    fn to_latex_line(&self) -> String {
        let mut result = format!(
            "{} & {} & {}",
            self.task.name,
            self.heyvl_loc,
            self.num_sliceable_statements()
        );
        for result_item in self.kind.iter() {
            if let Some((info, time)) = result_item.as_success() {
                let mut millis = time.as_millis();
                if time - Duration::from_millis(millis as u64) >= Duration::from_millis(500) {
                    millis += 1;
                }
                result.push_str(&format!(" && {} & {}", info.slice_size, millis));
            } else {
                result.push_str(" && - & -");
            }
        }
        result.push_str(" \\\\");
        result
    }

    fn write_csv_record<W: Write>(&self, writer: &mut csv::Writer<W>) -> csv::Result<()> {
        let mut record = vec![
            self.task.name.clone(),
            self.heyvl_loc.to_string(),
            self.num_sliceable_statements().to_string(),
        ];
        for result_item in self.kind.iter() {
            if let Some((info, time)) = result_item.as_success() {
                let millis = time.as_millis();
                record.extend(vec![info.slice_size.to_string(), millis.to_string()]);
            } else {
                record.extend(vec!["-".to_string(), "-".to_string()]);
            }
        }
        writer.write_record(record)?;
        Ok(())
    }
}

/// Write these results into a CSV file.
///
/// All results must be of the same kind or this will panic.
pub fn write_csv_results<W: Write>(
    results: &[SliceFileResults],
    writer: &mut W,
) -> csv::Result<()> {
    let mut writer = csv::Writer::from_writer(writer);
    match &results.first().unwrap().kind {
        SliceFileResultsKind::Error(_) => {
            writer.write_record(vec![
                "name",
                "loc",
                "original_size",
                "first_cex_slice_size",
                "first_cex_slice_time",
                "optimal_cex_slice_size",
                "optimal_cex_slice_time",
            ])?;
            assert!(results
                .iter()
                .all(|res| matches!(res.kind, SliceFileResultsKind::Error(_))));
        }
        SliceFileResultsKind::Verifying(_) => {
            writer.write_record(vec![
                "name",
                "loc",
                "original_size",
                "core_slice_size",
                "core_slice_time",
                "mus_slice_size",
                "mus_slice_time",
                "sus_slice_size",
                "sus_slice_time",
                "exists_forall_slice_size",
                "exists_forall_slice_time",
            ])?;
            assert!(results
                .iter()
                .all(|res| matches!(res.kind, SliceFileResultsKind::Verifying(_))));
        }
    }
    for result in results {
        result.write_csv_record(&mut writer)?;
    }
    Ok(())
}

/// Run a single slicing benchmark with the given extra arguments.
fn run_slicing_benchmark(
    task: &BenchmarkTask,
    extra_args: &[&str],
    trace_field_name: &str,
    progress: &ProgressBar,
) -> io::Result<SliceResult> {
    progress.set_message(extra_args.join(" "));
    let mut task = task.clone();
    task.args.extend(extra_args.iter().map(|s| s.to_string()));
    let res = run_benchmark(task)?;
    let result = parse_slice_result(&res, trace_field_name);
    progress.inc(1);
    Ok(result)
}

/// Run all slicing benchmarks for a single task.
pub fn run_benchmark_task_all_slices(
    task: &BenchmarkTask,
    progress: &ProgressBar,
) -> io::Result<SliceFileResults> {
    progress.reset();
    progress.set_length(5); // max is four plus initial

    let heyvl_loc = task.get_loc()?;

    let first_cex_slice = run_slicing_benchmark(
        task,
        &["--slice-error-first"],
        "slice_failing_binary_search",
        progress,
    )?;

    // first, do the "normal" verifying check that does slicing for errors.
    // based on the result, continue with slicing for errors benchmarks or
    // switch to verifying slices.
    if first_cex_slice.is_success() {
        progress.set_length(2);
        let optimal_cex_slice =
            run_slicing_benchmark(task, &[], "slice_failing_binary_search", progress)?;
        Ok(SliceFileResults {
            task: task.clone(),
            heyvl_loc,
            kind: SliceFileResultsKind::Error(ErroringSliceFileResults {
                first_cex_slice,
                optimal_cex_slice,
            }),
        })
    } else {
        let core_slice = run_slicing_benchmark(
            task,
            &["--slice-verify", "--slice-verify-via", "core"],
            "slice_verifying_unsat_core",
            progress,
        )?;
        let mus_slice = run_slicing_benchmark(
            task,
            &["--slice-verify", "--slice-verify-via", "mus"],
            "slice_verifying_enumerate",
            progress,
        )?;
        let sus_slice = run_slicing_benchmark(
            task,
            &["--slice-verify", "--slice-verify-via", "sus"],
            "slice_verifying_enumerate",
            progress,
        )?;
        let exists_forall_slice = run_slicing_benchmark(
            task,
            &["--slice-verify", "--slice-verify-via", "exists-forall"],
            "slice_verifying_exists_forall",
            progress,
        )?;
        Ok(SliceFileResults {
            task: task.clone(),
            heyvl_loc,
            kind: SliceFileResultsKind::Verifying(VerifyingSliceFileResults {
                core_slice,
                mus_slice,
                sus_slice,
                exists_forall_slice,
            }),
        })
    }
}

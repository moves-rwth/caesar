//! Running and evaluating slicing benchmarks.

#![allow(dead_code)]

use std::{fmt::Display, io, time::Duration};

use indicatif::ProgressBar;
use serde::Deserialize;
use serde_json::Value;
use std::thread;

use crate::{
    runner::{run_benchmark, BenchmarkResult, BenchmarkTask},
    traces::TracingEventFields,
};

#[derive(Debug)]
pub enum SlicingResult {
    Success {
        info: SlicingSuccessfulFields,
        time: Duration,
    },
    Failure {
        original_size: usize,
        time: Duration,
    },
    NotFound,
    AmbiguousProcs,
}

impl SlicingResult {
    pub fn is_success(&self) -> bool {
        matches!(self, SlicingResult::Success { .. })
    }

    pub fn as_success(&self) -> Option<(&SlicingSuccessfulFields, Duration)> {
        match self {
            SlicingResult::Success { info, time } => Some((info, *time)),
            _ => None,
        }
    }
}

impl Display for SlicingResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SlicingResult::Success { info, time } => {
                write!(f, "✓ {} {:?}", info.slice_size, time)
            }
            SlicingResult::Failure {
                original_size: _,
                time,
            } => {
                write!(f, "✗ {:?}", time)
            }
            SlicingResult::NotFound => write!(f, "BUG"),
            SlicingResult::AmbiguousProcs => write!(f, "BUG"),
        }
    }
}

#[derive(Debug, Deserialize)]
#[serde(tag = "message")]
enum SlicingTraceFields {
    #[serde(rename = "translated slice selection")]
    TranslatedSliceSelection(TranslatedSliceSelectionFields),
    #[serde(rename = "slicing successful")]
    SlicingSuccessful(SlicingSuccessfulFields),
    #[serde(rename = "no slice accepted")]
    SlicingFailed,
}

#[derive(Debug, Deserialize)]
struct TranslatedSliceSelectionFields {
    active: usize,
    inactive: usize,
}

#[derive(Debug, Deserialize)]
pub struct SlicingSuccessfulFields {
    pub slice_size: usize,
    pub removed_statements: usize,
    pub from_first_model: usize,
    pub found_slices: usize,
}

fn parse_slicing_result(result: &BenchmarkResult, tracing_name: &str) -> SlicingResult {
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
                return SlicingResult::AmbiguousProcs;
            }
            total_time = Some(time_busy.0);
        }
    }

    for event in relevant_events {
        match serde_json::from_value(Value::Object(event.fields.clone())) {
            Ok(SlicingTraceFields::TranslatedSliceSelection(fields)) => {
                active = Some(fields.active);
            }
            Ok(SlicingTraceFields::SlicingSuccessful(fields)) => {
                return SlicingResult::Success {
                    info: fields,
                    time: total_time.unwrap(),
                };
            }
            Ok(SlicingTraceFields::SlicingFailed) => {
                return SlicingResult::Failure {
                    original_size: active.unwrap(),
                    time: total_time.unwrap(),
                };
            }
            _ => {}
        }
    }
    SlicingResult::NotFound
}

#[derive(Debug)]
pub struct SlicingBenchmarkResult {
    task: BenchmarkTask,
    heyvl_loc: usize,
    first_cex_slice: SlicingResult,
    optimal_cex_slice: SlicingResult,
    core_slice: SlicingResult,
    mus_slice: SlicingResult,
    sus_slice: SlicingResult,
    exists_forall_slice: SlicingResult,
}

impl SlicingBenchmarkResult {
    fn all_results(&self) -> Vec<&SlicingResult> {
        vec![
            &self.first_cex_slice,
            &self.optimal_cex_slice,
            &self.core_slice,
            &self.mus_slice,
            &self.sus_slice,
            &self.exists_forall_slice,
        ]
    }

    fn all_error_results(&self) -> Vec<&SlicingResult> {
        vec![&self.first_cex_slice, &self.optimal_cex_slice]
    }

    fn all_verifying_results(&self) -> Vec<&SlicingResult> {
        vec![
            &self.core_slice,
            &self.mus_slice,
            &self.sus_slice,
            &self.exists_forall_slice,
        ]
    }

    pub fn num_sliceable_statements(&self) -> usize {
        self.first_cex_slice
            .as_success()
            .or(self.core_slice.as_success())
            .map(|(info, _time)| info.slice_size + info.removed_statements)
            .unwrap()
    }
}

impl Display for SlicingBenchmarkResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} & {} & {}",
            self.task.name,
            self.heyvl_loc,
            self.num_sliceable_statements()
        )?;
        let has_error = self.first_cex_slice.is_success();
        let iter = if has_error {
            self.all_error_results()
        } else {
            self.all_verifying_results()
        };
        for result in iter {
            if let Some((info, time)) = result.as_success() {
                write!(f, " & {} & {}", info.slice_size, time.as_millis())?;
            } else {
                write!(f, " & - & -")?;
            }
        }
        write!(f, " \\\\")?;
        Ok(())
    }
}

pub fn run_benchmark_slicing(
    task: &BenchmarkTask,
    progress: &ProgressBar,
) -> io::Result<SlicingBenchmarkResult> {
    let heyvl_loc = task.get_loc()?;

    let first_cex_slice = thread::spawn({
        let task = task.clone();
        let progress = progress.clone();
        move || {
            let mut task_first_cex = task.clone();
            task_first_cex.args.push("--slice-error-first".to_string());
            let res = run_benchmark(task_first_cex).unwrap();
            let result = parse_slicing_result(&res, "slice_failing_binary_search");
            progress.inc(1);
            result
        }
    });

    let optimal_cex_slice = thread::spawn({
        let task = task.clone();
        let progress = progress.clone();
        move || {
            let task_optimal_cex = task.clone();
            let res = run_benchmark(task_optimal_cex).unwrap();
            let result = parse_slicing_result(&res, "slice_failing_binary_search");
            progress.inc(1);
            result
        }
    });

    let core_slice = thread::spawn({
        let task = task.clone();
        let progress = progress.clone();
        move || {
            let mut task_core = task.clone();
            task_core.args.extend([
                "--slice-verify".to_string(),
                "--slice-verify-via".to_string(),
                "core".to_string(),
            ]);
            let res = run_benchmark(task_core).unwrap();
            let result = parse_slicing_result(&res, "slice_verifying_unsat_core");
            progress.inc(1);
            result
        }
    });

    let mus_slice = thread::spawn({
        let task = task.clone();
        let progress = progress.clone();
        move || {
            let mut task_mus = task.clone();
            task_mus.args.extend([
                "--slice-verify".to_string(),
                "--slice-verify-via".to_string(),
                "mus".to_string(),
            ]);
            let res = run_benchmark(task_mus).unwrap();
            let result = parse_slicing_result(&res, "slice_verifying_enumerate");
            progress.inc(1);
            result
        }
    });

    let sus_slice = thread::spawn({
        let task = task.clone();
        let progress = progress.clone();
        move || {
            let mut task_sus = task.clone();
            task_sus.args.extend([
                "--slice-verify".to_string(),
                "--slice-verify-via".to_string(),
                "sus".to_string(),
            ]);
            let res = run_benchmark(task_sus).unwrap();
            let result = parse_slicing_result(&res, "slice_verifying_enumerate");
            progress.inc(1);
            result
        }
    });

    let exists_forall_slice = thread::spawn({
        let task = task.clone();
        let progress = progress.clone();
        move || {
            let mut task_exists_forall = task.clone();
            task_exists_forall.args.extend([
                "--slice-verify".to_string(),
                "--slice-verify-via".to_string(),
                "exists-forall".to_string(),
            ]);
            let res = run_benchmark(task_exists_forall).unwrap();
            let result = parse_slicing_result(&res, "slice_verifying_ef_binary_search");
            progress.inc(1);
            result
        }
    });

    let first_cex_slice = first_cex_slice.join().unwrap();
    let optimal_cex_slice = optimal_cex_slice.join().unwrap();
    let core_slice = core_slice.join().unwrap();
    let mus_slice = mus_slice.join().unwrap();
    let sus_slice = sus_slice.join().unwrap();
    let exists_forall_slice = exists_forall_slice.join().unwrap();

    Ok(SlicingBenchmarkResult {
        task: task.clone(),
        heyvl_loc,
        first_cex_slice,
        optimal_cex_slice,
        core_slice,
        mus_slice,
        sus_slice,
        exists_forall_slice,
    })
}

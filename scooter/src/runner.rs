//! Run Caesar and parse its output from stdout and stderr.

use std::{
    collections::HashMap,
    fmt::Display,
    fs::File,
    io::{self, BufRead, BufReader, ErrorKind},
    process::{Command, ExitStatus},
    time::Duration,
};

use crate::traces::TracingEvent;

/// Try to build caesar. If `cargo` is not installed, do nothing.
pub fn build_caesar() -> io::Result<()> {
    let mut cmd = Command::new("cargo");
    cmd.arg("build").arg("--release");
    let mut spawn_res = match cmd.spawn() {
        Err(e) if e.kind() == ErrorKind::NotFound => {
            eprintln!("info: cargo not found, not rebuilding caesar.");
            return Ok(());
        }
        spawn_res => spawn_res?,
    };
    spawn_res.wait().map(|_| ())
}

/// Caesar's exit status.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CaesarExitStatus {
    Verified,
    OutOfMemory,
    Timeout,
    Error,
}

impl CaesarExitStatus {
    fn from_exit_status(exit_status: ExitStatus) -> Self {
        match exit_status.code() {
            Some(0) => CaesarExitStatus::Verified,
            Some(1) => CaesarExitStatus::Error,
            Some(2) | Some(130) => CaesarExitStatus::Timeout,
            Some(3) => CaesarExitStatus::OutOfMemory,
            _ => panic!("unexpected exit status of process: {exit_status}"),
        }
    }
}

impl Display for CaesarExitStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let res = match self {
            CaesarExitStatus::Verified => "OK",
            CaesarExitStatus::OutOfMemory => "OOM",
            CaesarExitStatus::Timeout => "TO",
            CaesarExitStatus::Error => "ERR",
        };
        write!(f, "{res}")
    }
}

/// Timing information from a benchmark result from Caesar's `--timing` flag.
#[derive(Debug)]
#[allow(unused)]
pub struct CaesarTimingSummary(pub HashMap<String, Duration>);

impl CaesarTimingSummary {
    fn from_caesar_stderr(stderr: &[u8]) -> Option<Self> {
        const TIMINGS: &[u8] = b"Timings: ";

        let timings_json = stderr
            .split(|c| *c == b'\n')
            .filter(|line| line.starts_with(TIMINGS))
            .map(|line| &line[TIMINGS.len()..])
            .next()
            .unwrap();
        let timings_map: HashMap<String, String> = serde_json::from_slice(timings_json).unwrap();
        let timings_map = timings_map
            .into_iter()
            .map(|(key, value)| (key, Duration::from_nanos(value.parse().unwrap())))
            .collect();
        Some(CaesarTimingSummary(timings_map))
    }
}

#[derive(Debug, Clone)]
pub struct BenchmarkTask {
    pub name: String,
    pub args: Vec<String>,
}

impl BenchmarkTask {
    /// Counts the number of lines in the file specified by the first argument in the
    /// list, ignoring lines that start with `//`.
    pub fn get_loc(&self) -> io::Result<usize> {
        let file_name = self.args.first().unwrap();
        let file = File::open(file_name)?;
        let lines = BufReader::new(file).lines();
        let mut count = 0;
        for line in lines {
            let line = line?;
            let line = line.trim();
            if line.is_empty() || line.starts_with("//") {
                continue;
            }
            count += 1;
        }
        Ok(count)
    }
}

#[derive(Debug)]
#[allow(unused)]
pub struct BenchmarkResult {
    pub task: BenchmarkTask,
    pub exit_status: CaesarExitStatus,
    pub events: Vec<TracingEvent>,
    pub timings: Option<CaesarTimingSummary>,
}

pub fn run_benchmark(task: BenchmarkTask) -> io::Result<BenchmarkResult> {
    let mut args = task.args.clone();
    args.push("--timing".to_owned());
    args.push("--json".to_owned());

    let mut command = Command::new("../target/release/caesar");
    command.args(&args);
    command.env("RUST_LOG", "caesar=info,caesar::slicing=debug");

    let output = command.output().expect("failed to execute process");
    let exit_status = CaesarExitStatus::from_exit_status(output.status);
    let timings = CaesarTimingSummary::from_caesar_stderr(&output.stderr);

    let events = output
        .stderr
        .split(|c| *c == b'\n')
        .filter(|line| (*line).starts_with(b"{"))
        .flat_map(|line| match serde_json::from_slice::<TracingEvent>(line) {
            Ok(event) => Some(event),
            Err(e) => {
                eprintln!(
                    "Failed to parse line: {}\nError: {:?}",
                    String::from_utf8_lossy(line),
                    e
                );
                None
            }
        })
        .collect::<Vec<_>>();

    Ok(BenchmarkResult {
        task,
        exit_status,
        events,
        timings,
    })
}

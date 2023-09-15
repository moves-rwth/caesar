use cli_table::{format::Justify, print_stdout, Cell, Style, Table};
use indicatif::{ProgressBar, ProgressIterator, ProgressStyle};
use std::{
    collections::HashMap,
    fmt::Display,
    fs::File,
    io::{self, BufRead, BufReader, ErrorKind, Write},
    process::{Command, ExitStatus},
    time::Duration,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BenchmarkStatus {
    Verified,
    OutOfMemory,
    Timeout,
    Error,
}

impl BenchmarkStatus {
    fn from_exit_status(exit_status: ExitStatus) -> Self {
        match exit_status.code() {
            Some(0) => BenchmarkStatus::Verified,
            Some(1) => BenchmarkStatus::Error,
            Some(2) => BenchmarkStatus::Timeout,
            Some(3) => BenchmarkStatus::OutOfMemory,
            _ => panic!("unexpected exit status of process: {}", exit_status),
        }
    }
}

impl Display for BenchmarkStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let res = match self {
            BenchmarkStatus::Verified => "OK",
            BenchmarkStatus::OutOfMemory => "OOM",
            BenchmarkStatus::Timeout => "TO",
            BenchmarkStatus::Error => "ERR",
        };
        write!(f, "{}", res)
    }
}

#[derive(Debug)]
struct BenchmarkResult {
    prefix: String,
    heyvl_loc: usize,
    status: BenchmarkStatus,
    timings: Option<BenchmarkTimings>,
}

impl BenchmarkResult {
    /// Get the table headers.
    fn table_headers() -> Vec<String> {
        ["Name", "HeyVL LOC", "Total", "Unfolding", "SAT"]
            .into_iter()
            .map(ToOwned::to_owned)
            .collect()
    }

    /// Format this benchmark result as a table row.
    fn to_table_row(&self) -> Vec<String> {
        let timings = self.timings.as_ref();
        let total = match self.status {
            BenchmarkStatus::Verified => {
                format!("{:.2}", timings.unwrap().total_time.as_secs_f64())
            }
            status => status.to_string(),
        };
        let format_percent =
            |value: Option<f64>| value.map(|v: f64| format!("{:.0}%", v)).unwrap_or_default();
        vec![
            self.prefix.clone(),
            self.heyvl_loc.to_string(),
            total,
            format_percent(timings.map(|timings| timings.unfolding_percent)),
            format_percent(timings.map(|timings| timings.sat_percent)),
        ]
    }
}

fn run_benchmark(prefix: &str, mut args: Vec<String>) -> io::Result<BenchmarkResult> {
    args.push("--timing".to_owned());

    let mut command = Command::new("./target/release/caesar");
    command.args(&args);
    command.env("RUST_LOG", "caesar=info");

    let output = command.output().expect("failed to execute process");
    let status = BenchmarkStatus::from_exit_status(output.status);
    let timings = if status == BenchmarkStatus::Verified {
        BenchmarkTimings::from_caesar_stderr(&output.stderr)
    } else {
        None
    };
    Ok(BenchmarkResult {
        prefix: prefix.to_owned(),
        heyvl_loc: get_loc(&args)?,
        status,
        timings,
    })
}

/// Counts the number of lines in the file specified by the first argument in the
/// list, ignoring lines that start with `//`.
fn get_loc(args: &[String]) -> io::Result<usize> {
    let file_name = args.first().unwrap();
    let file = File::open(file_name)?;
    let lines = BufReader::new(file).lines();
    let mut count = 0;
    for line in lines {
        let line = line?;
        if !line.starts_with("//") {
            count += 1;
        }
    }
    Ok(count)
}

/// Pretty-printed timing information from a benchmark result.
#[derive(Debug)]
struct BenchmarkTimings {
    /// The total duration.
    total_time: Duration,
    /// Unfolding duration as a percentage of the total duration.
    unfolding_percent: f64,
    /// SAT time as a percentage of the total duration.
    sat_percent: f64,
}

impl BenchmarkTimings {
    /// Extract timing information from caesar's stderr output.
    ///
    /// The timing information is provided as a JSON in a unique line starting with
    /// `Timings: ` if `--timing` is passed.
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
        Self::from_json(timings_map)
    }

    fn from_json(timings: HashMap<String, Duration>) -> Option<BenchmarkTimings> {
        let total_time = timings.get("item").copied()?;
        let total_secs = total_time.as_secs_f64();
        let get_duration_percent = |name: &str| {
            timings
                .get(name)
                .map(|duration| duration.as_secs_f64() / total_secs * 100.0)
                .unwrap_or_default()
        };

        let unfolding_time = get_duration_percent("unfolding");
        let sat_time = get_duration_percent("SAT check");
        Some(BenchmarkTimings {
            total_time,
            unfolding_percent: unfolding_time,
            sat_percent: sat_time,
        })
    }
}

/// Try to build caesar. If `cargo` is not installed, do nothing.
fn build_caesar() -> io::Result<()> {
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

#[derive(Default)]
struct BenchmarkResultList(Vec<BenchmarkResult>);

impl BenchmarkResultList {
    fn push(&mut self, result: BenchmarkResult) {
        self.0.push(result);
    }

    fn loc_min(&self) -> usize {
        self.0
            .iter()
            .map(|res| res.heyvl_loc)
            .min()
            .unwrap_or_default()
    }

    fn loc_max(&self) -> usize {
        self.0
            .iter()
            .map(|res| res.heyvl_loc)
            .max()
            .unwrap_or_default()
    }

    fn time_avg(&self) -> Duration {
        self.iter_verified()
            .flat_map(|res| res.timings.as_ref())
            .map(|timings| timings.total_time)
            .sum::<Duration>()
            / (self.iter_verified().count() as u32)
    }

    fn time_max(&self) -> Duration {
        self.iter_verified()
            .flat_map(|res| res.timings.as_ref())
            .map(|timings| timings.total_time)
            .max()
            .unwrap_or_default()
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn iter_verified(&self) -> impl Iterator<Item = &BenchmarkResult> {
        self.0
            .iter()
            .filter(|res| res.status == BenchmarkStatus::Verified)
    }

    fn print_cli_table(&self) {
        let table_title = BenchmarkResult::table_headers()
            .iter()
            .map(|header| header.cell().bold(true))
            .collect::<Vec<_>>();
        let table_rows = self.0.iter().map(|res| {
            res.to_table_row()
                .iter()
                .enumerate()
                .map(|(i, cell)| {
                    cell.cell().justify(if i == 0 {
                        Justify::Left
                    } else {
                        Justify::Right
                    })
                })
                .collect::<Vec<_>>()
        });
        let table = table_rows.table().title(table_title);
        print_stdout(table).unwrap();
    }
}

fn main() {
    build_caesar().expect("Could not build caesar.");

    let mut args = std::env::args();
    args.next().unwrap();
    let more_args: Vec<String> = args.collect();

    let stdin = std::io::stdin();
    let stdin_reader = std::io::BufReader::new(stdin);
    let lines: Vec<Result<String, _>> = stdin_reader.lines().collect();

    const CSV_FILE_NAME: &str = "benchmark-results.csv";
    let mut csv_output = std::fs::File::create(CSV_FILE_NAME).unwrap();
    writeln!(
        &mut csv_output,
        "{}",
        BenchmarkResult::table_headers().join(",")
    )
    .unwrap();

    println!("Running benchmarks...");

    let style = ProgressStyle::with_template("[{pos}/{len}] {bar:40.cyan/blue} {msg}").unwrap();
    let pb = ProgressBar::new(lines.len() as u64);
    pb.set_style(style);

    let mut results = BenchmarkResultList::default();
    for item in lines.into_iter().progress_with(pb.clone()) {
        let line = item.unwrap();
        let (prefix, args) = line.split_once(':').unwrap();
        pb.set_message(prefix.to_owned());
        let mut args = shell_words::split(args).unwrap();
        args.append(&mut more_args.clone());
        let res = run_benchmark(prefix, args).unwrap();
        writeln!(&mut csv_output, "{}", res.to_table_row().join(",")).unwrap();
        results.push(res);
    }

    println!("Benchmarks completed.");
    println!(
        "Out of {} benchmarks, {} verified.",
        results.len(),
        results.iter_verified().count()
    );
    println!();
    results.print_cli_table();
    println!();
    println!(
        "HeyVL LOC min: {}, HeyVL LOC max: {}.",
        results.loc_min(),
        results.loc_max(),
    );
    println!(
        "For the verifying benchmarks: average time was {:.2}s, maximum time was {:.2}s.",
        results.time_avg().as_secs_f64(),
        results.time_max().as_secs_f64()
    );
    println!(
        "Results have been written to a CSV file: {}.",
        CSV_FILE_NAME
    );
}

mod runner;
mod slicing_benchmark;
pub mod traces;

use std::io::BufRead;

use indicatif::{ProgressBar, ProgressIterator, ProgressStyle};
use runner::{build_caesar, BenchmarkTask};
use slicing_benchmark::run_benchmark_slicing;

fn main() {
    build_caesar().expect("Could not build caesar.");

    let mut args = std::env::args();
    args.next().unwrap();
    let more_args: Vec<String> = args.collect();

    let stdin = std::io::stdin();
    let stdin_reader = std::io::BufReader::new(stdin);
    let lines: Vec<Result<String, _>> = stdin_reader.lines().collect();

    println!("Running benchmarks...");

    let mpb = indicatif::MultiProgress::new();
    let outer_pb = mpb.add(ProgressBar::new(lines.len() as u64));
    let style = ProgressStyle::with_template("[{pos}/{len}] {bar:40.cyan/blue} {msg}").unwrap();
    outer_pb.set_style(style);
    let inner_pb = mpb.add(ProgressBar::new(8));
    let style = ProgressStyle::with_template("[{pos}/{len}] {bar:40.green/red} {msg}").unwrap();
    inner_pb.set_style(style);

    for item in lines.into_iter().progress_with(outer_pb.clone()) {
        let line = item.unwrap();
        let (prefix, args) = line.split_once(':').unwrap();
        outer_pb.set_message(prefix.to_owned());
        let mut args = shlex::split(args).unwrap();
        args.append(&mut more_args.clone());
        let slicing_result = run_benchmark_slicing(
            &BenchmarkTask {
                name: prefix.to_string(),
                args: args.clone(),
            },
            &inner_pb,
        );

        match slicing_result {
            Ok(result) => println!("{}", result),
            Err(e) => {
                if e.kind() == std::io::ErrorKind::NotFound {
                    panic!("Error: Benchmark task {:?} not found.", &args);
                } else {
                    panic!("Error: {}", e);
                }
            }
        }
        inner_pb.reset();
    }
}

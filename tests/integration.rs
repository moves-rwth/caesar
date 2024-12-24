//! Integration tests for Caesar.
//!
//! This module runs tests with Caesar. Commands are written as comments in test
//! files. The following commands are supported: RUN, XFAIL, and IGNORE. The RUN
//! command runs a given command (substituting `@caesar` with the path to the
//! Caesar binary and `@file` with the path to the test file) and checks that it
//! exits with a success status code. If the XFAIL command is present, the test
//! is expected to fail instead with a non-zero status code. The IGNORE command
//! allows the file to be ignored (we throw an error if the file has no commands
//! otherwise).

use std::{
    fs, io,
    path::PathBuf,
    process::{Command, Output},
};

use glob::glob;
use libtest_mimic::{Arguments, Failed, Trial};
use pathdiff::diff_paths;
use regex::Regex;

const CRATE_PATH: &str = env!("CARGO_MANIFEST_DIR");
const CAESAR_PATH: &str = env!("CARGO_BIN_EXE_caesar");

fn main() {
    let args = Arguments::from_args();

    let tests = glob(&format!("{}/tests/**/*.heyvl", CRATE_PATH))
        .unwrap()
        .map(|res| res.unwrap())
        .map(|path| {
            Trial::test(get_test_name(&path), move || {
                let test_file = TestFile::parse(path)?;
                test_file.run()
            })
        })
        .collect();

    libtest_mimic::run(&args, tests).exit();
}

fn get_test_name(path: &PathBuf) -> String {
    diff_paths(path, CRATE_PATH)
        .unwrap()
        .to_string_lossy()
        .to_string()
}

/// A command written as a comment in a test file.
#[derive(Debug)]
enum TestCommand {
    Run(String),
    Xfail(String),
    Ignore(String),
}

#[derive(Debug)]
struct TestFile {
    commands: Vec<TestCommand>,
}

impl TestFile {
    fn parse(path: PathBuf) -> io::Result<Self> {
        let test_file = fs::read_to_string(&path).unwrap();
        let regex = Regex::new(r"//\s*(RUN|XFAIL|IGNORE): (.*)").unwrap();
        let commands = regex
            .captures_iter(&test_file)
            .map(|capture| {
                let arg = capture[2].to_string();
                let arg = arg.replace("@caesar", CAESAR_PATH);
                let arg = arg.replace("@file", path.to_str().unwrap());
                match &capture[1] {
                    "RUN" => TestCommand::Run(arg),
                    "XFAIL" => TestCommand::Xfail(arg),
                    "IGNORE" => TestCommand::Ignore(arg),
                    _ => unreachable!(),
                }
            })
            .collect();
        Ok(TestFile { commands })
    }

    fn run(&self) -> Result<(), Failed> {
        let mut output: Option<(&str, Output)> = None;
        let mut xfail = false;
        let mut ignore = false;
        for command in &self.commands {
            match command {
                TestCommand::Run(arg) => {
                    if output.is_some() {
                        return Err("Test contains multiple RUN commands".into());
                    }
                    let args = shlex::split(arg).unwrap();
                    let mut command = Command::new(&args[0]);
                    command.args(&args[1..]);
                    output = Some((arg, command.output().unwrap()));
                }
                TestCommand::Xfail(_args) => {
                    xfail = true;
                    if let Some((_, output)) = &output {
                        if output.status.success() {
                            return Err("XFAIL command succeeded".into());
                        }
                    } else {
                        return Err("XFAIL command without preceding RUN command".into());
                    }
                }
                TestCommand::Ignore(_args) => {
                    ignore = true;
                }
            }
        }
        if !xfail {
            if let Some((command, output)) = output {
                if !output.status.success() {
                    return Err(format!(
                        "Failed RUN: {}.\n\nStdout:\n{}\n\nStderr:\n{}",
                        command,
                        String::from_utf8(output.stdout).unwrap(),
                        String::from_utf8(output.stderr).unwrap()
                    )
                    .into());
                }
            } else if !ignore {
                return Err("Test file contains no commands".into());
            }
        }
        Ok(())
    }
}

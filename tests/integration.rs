// Notes on the `lit` library that we're using, because there are some issues.
//
// The library is too complex for my taste and does too much that I don't want.
// It shouldn't handle test discovery, just run a single file's commands. At the
// moment, we're working around this feature by adding each file manually that
// we want (applying our own filters). But then there's a bug in lit where we
// have to add a random directory to the search path so the file name lit
// outputs are not empty strings.
//
// Then, XFAIL is not working as I would expect. For one, if a file is marked as
// XFAIL and a command in it exits with a status code other than 0, the file is
// erroneously marked as FAIL (not XFAIL). Additionally, if the command exits
// with status code 0 and is marked as XFAIL, the file will be marked as PASS. I
// would expected a XFAIL or FAIL there.
//
// Finally, lit is not actively maintained anymore. We should move away from lit
// and develop our own simple version of lit without all the unnecessary features.

use std::{env, process};

use clap::{App, Arg};
use glob::glob;

const CRATE_PATH: &str = env!("CARGO_MANIFEST_DIR");
const CAESAR_PATH: &str = env!("CARGO_BIN_EXE_caesar");

fn main() {
    let app = App::new("Integration test runner")
        .usage("cargo test --test integration --")
        .arg(
            Arg::with_name("test-filters")
                .help("Run only tests that contain any of the given strings")
                .multiple(true),
        );
    let app = lit::config::clap::mount_inside_app(app, false);
    let matches = app.get_matches();

    let test_filters = matches
        .values_of("test-filters")
        .map(|values| values.collect::<Vec<_>>());

    let test_files: Vec<String> = glob(&format!("{}/tests/**/*.heyvl", CRATE_PATH))
        .unwrap()
        .map(|res| res.unwrap())
        .filter(|test_file| {
            // if there are any filters, skip this file if no filters match
            if let Some(test_filters) = &test_filters {
                let test_name = test_file.file_name().unwrap().to_str().unwrap();
                if !test_filters.iter().any(|filter| test_name.contains(filter)) {
                    return false;
                }
            }
            true
        })
        .map(|test_file| test_file.to_str().unwrap().to_owned())
        .collect();

    if test_filters.is_some() && test_files.is_empty() {
        // if all tests were intentionally filtered out, don't invoke lit.
        // lit will throw an error if run without tests
        return;
    }

    let res = lit::run::tests(lit::event_handler::Default::default(), |config| {
        // we add this directory as a search path, but no file extensions to search so that it actually is not used.
        // but we need to add _some_ directory, otherwise lit will give all tests empty "relative" names and the output will be useless.
        // so this is just a workaround for a lit bug.
        config.add_search_path(&format!("{}/tests/", CRATE_PATH));

        for test_file in &test_files {
            config.add_search_path(test_file);
        }

        // The default shell is bash, which is not available on Windows.
        if cfg!(target_os = "windows") {
            // does not actually execute the tests under windows as cmd requires the
            // /C flag to execute a command. But there seems no way to specify that.
            config.shell = "cmd.exe".to_string();
        }

        config
            .constants
            .insert("caesar".to_owned(), CAESAR_PATH.to_owned());

        lit::config::clap::parse_arguments(&matches, config);
    });

    process::exit(if res.is_ok() { 0 } else { 1 });
}

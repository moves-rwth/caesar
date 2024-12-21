//! Utilities to print the version of Caesar and some dependencies.
//! This is printed to the command-line when Caesar is used without the `quiet` option.

use std::{
    env,
    ffi::CStr,
    io::{self, Write},
};

mod built_info {
    // The file has been placed there by the build script.
    include!(concat!(env!("OUT_DIR"), "/built.rs"));
}

/// Return a String that describes the currently built version of Caesar.
pub fn caesar_version_info() -> String {
    let cargo_version = env!("CARGO_PKG_VERSION");
    if let Some(git_commit) = built_info::GIT_COMMIT_HASH {
        let dirty_suffix = if built_info::GIT_DIRTY.unwrap_or(false) {
            ", dirty"
        } else {
            ""
        };
        format!("{} ({}{})", cargo_version, git_commit, dirty_suffix)
    } else {
        format!("{} (no git info)", cargo_version)
    }
}

/// This is the Cargo.toml's package version. It's used to check if a VSCode
/// client is compatible.
pub fn caesar_semver_version() -> String {
    env!("CARGO_PKG_VERSION").to_owned()
}

/// Return Z3's version.
fn z3_version_info() -> String {
    let z3_str = unsafe { CStr::from_ptr(z3_sys::Z3_get_full_version()) };
    z3_str.to_string_lossy().to_string()
}

/// Write detailed version info about Caesar and its dependencies.
pub fn write_detailed_version_info<W>(w: &mut W) -> io::Result<()>
where
    W: Write,
{
    let command: String = {
        let args_strings: Vec<String> = env::args().collect();
        let args_strs = args_strings.iter().map(|s| s.as_str());
        shlex::try_join(args_strs).unwrap()
    };
    writeln!(w, "Command: {}", command)?;
    writeln!(w, "Caesar version: {}", caesar_version_info())?;

    write!(w, "Build: {}", built_info::BUILT_TIME_UTC)?;
    if let Some(ci_platform) = built_info::CI_PLATFORM {
        write!(w, " ({})", ci_platform)?;
    }
    writeln!(w)?;

    writeln!(
        w,
        "Profile: {}. Features: {}. Target: {}, Host: {}",
        built_info::PROFILE,
        built_info::FEATURES_STR,
        built_info::TARGET,
        built_info::HOST
    )?;
    writeln!(w, "Z3 version: {}", z3_version_info())?;
    writeln!(w)
}

/// Get a detailed version info string about Caesar and its dependencies.
pub fn detailed_version_info_string() -> String {
    let mut buffer = Vec::new();
    write_detailed_version_info(&mut buffer).unwrap();
    String::from_utf8(buffer).unwrap()
}

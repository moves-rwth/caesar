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

/// Return a String that describes this crate's version, including a Git commit hash.
pub fn self_version_info() -> String {
    if let Some(git_version) = built_info::GIT_VERSION {
        let mut git_version = git_version.to_string();
        if built_info::GIT_DIRTY.unwrap_or(false) {
            git_version.push_str("-dirty");
        }
        format!("{} ({})", env!("CARGO_PKG_VERSION"), git_version)
    } else {
        // if git is not installed or we're in a shallow checkout (e.g. in CI),
        // then GIT_VERSION is None. So use a fallback then.
        env!("CARGO_PKG_VERSION").to_string()
    }
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
        let args_strs: Vec<&str> = args_strings.iter().map(|s| s.as_str()).collect();
        shellwords::join(&args_strs)
    };
    writeln!(w, "Command: {}", command)?;
    writeln!(w, "Caesar version: {}", self_version_info())?;
    writeln!(
        w,
        "Profile: {}. Features: {}. Target: {}",
        built_info::PROFILE,
        built_info::FEATURES_STR,
        built_info::TARGET
    )?;
    writeln!(w, "Z3 version: {}", z3_version_info())?;
    writeln!(w)
}

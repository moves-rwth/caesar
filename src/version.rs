//! Utilities to print the version of Caesar and some dependencies.
//! This is printed to the command-line when Caesar is used without the `quiet` option.

use std::{
    env,
    io::{self, Write},
};

mod built_info {
    // The file has been placed there by the build script.
    include!(concat!(env!("OUT_DIR"), "/built.rs"));
}

/// This is the Cargo.toml's package version as a SemVer string.
pub fn caesar_semver_version() -> String {
    env!("CARGO_PKG_VERSION").to_owned()
}

/// Return a String that describes the currently built version of Caesar.
pub fn caesar_detailed_version() -> String {
    let cargo_version = env!("CARGO_PKG_VERSION");
    if let Some(git_commit) = built_info::GIT_COMMIT_HASH {
        let dirty_suffix = if built_info::GIT_DIRTY.unwrap_or(false) {
            ", dirty"
        } else {
            ""
        };
        format!("{cargo_version} ({git_commit}{dirty_suffix})")
    } else {
        format!("{cargo_version} (no git info)")
    }
}

/// Write detailed version info about the caesar command and its dependencies.
pub fn write_detailed_command_info<W>(w: &mut W) -> io::Result<()>
where
    W: Write,
{
    let command: String = {
        let args_strings: Vec<String> = env::args().collect();
        let args_strs = args_strings.iter().map(|s| s.as_str());
        shlex::try_join(args_strs).unwrap()
    };
    writeln!(w, "Command: {command}")?;
    writeln!(w, "Caesar version: {}", caesar_detailed_version())?;
    writeln!(w, "Features: {}", built_info::FEATURES_LOWERCASE_STR)?;
    writeln!(w)?;

    writeln!(w, "Profile: {}", built_info::PROFILE)?;
    writeln!(w, "Target: {}", built_info::TARGET)?;
    writeln!(w, "Build date: {}", built_info::BUILT_TIME_UTC)?;
    write!(w, "Build host: {}", built_info::HOST)?;
    if let Some(ci_platform) = built_info::CI_PLATFORM {
        write!(w, " ({ci_platform})")?;
    }
    writeln!(w)?;
    writeln!(w)?;

    writeln!(w, "Z3 version: {}", z3::full_version())?;
    writeln!(w, "Operating system: {}", os_info::get())?;
    writeln!(w)
}

/// Get a detailed version info string about Caesar and its dependencies.
pub(crate) fn clap_detailed_version_info() -> String {
    let mut buffer = Vec::new();
    writeln!(&mut buffer, "{}", caesar_semver_version()).unwrap();
    write_detailed_command_info(&mut buffer).unwrap();
    String::from_utf8(buffer).unwrap()
}

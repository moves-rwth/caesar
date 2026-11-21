use std::{
    collections::HashSet,
    fs::create_dir_all,
    path::{Path, PathBuf},
    process::Command,
};

use ariadne::ReportKind;
use regex::Regex;

use super::{
    index::DeclIndex,
    lower::{ensure_required_decl_supported, DafnyLowerer},
    pretty,
};
use crate::{
    ast::{FileId, Ident, SourceFilePath},
    depgraph::DepGraph,
    driver::{
        commands::options::{DafnyOptions, DafnyScope, InputOptions},
        error::CaesarError,
        front::Module,
    },
    resource_limits::LimitsRef,
    servers::Server,
    smt::funcs::axiomatic::AxiomInstantiation,
    tyctx::TyCtx,
};

/// Per-file translation state after scope selection has been resolved.
pub(crate) struct FilePlan {
    pub(crate) file_id: FileId,
    pub(crate) output_path: PathBuf,
    pub(crate) roots: Vec<Ident>,
    pub(crate) included: HashSet<Ident>,
}

/// Translate the selected HeyVL files into Dafny files and optionally run `dafny verify`.
pub fn translate_to_dafny(
    options: &DafnyOptions,
    input_options: &InputOptions,
    module: &mut Module,
    server: &mut dyn Server,
    limits_ref: &LimitsRef,
    tcx: &TyCtx,
    user_files: &[FileId],
) -> Result<(), CaesarError> {
    if options.dafny_dir.is_none() && !options.run_dafny {
        return Err(CaesarError::UserError(
            "Either --dafny-dir or --run-dafny must be provided.".into(),
        ));
    }

    let filter = match &input_options.filter {
        Some(filter) => Some(Regex::new(filter).map_err(|err| {
            CaesarError::UserError(format!("Invalid filter regex: {err}").into())
        })?),
        None => None,
    };

    let mut depgraph = DepGraph::new(AxiomInstantiation::Decreasing);
    for source_unit in &mut module.items {
        source_unit.enter_mut().populate_depgraph(&mut depgraph)?;
    }

    let index = DeclIndex::new(module);

    let mut temp_dir = None;
    let output_dir = if let Some(dafny_dir) = &options.dafny_dir {
        dafny_dir.clone()
    } else {
        let dir = tempfile::tempdir().map_err(|err| {
            CaesarError::UserError(format!("Could not create temporary directory: {err}").into())
        })?;
        let path = dir.path().to_owned();
        temp_dir = Some(dir);
        path
    };

    let lowerer = DafnyLowerer {
        tcx,
        depgraph: &depgraph,
        index: &index,
    };

    let mut wrote_anything = false;
    for file_id in user_files {
        limits_ref.check_limits()?;
        let roots = index.selected_roots_for_file(*file_id, filter.as_ref());
        if roots.is_empty() {
            continue;
        }

        let stored_file = server.get_file(*file_id).ok_or_else(|| {
            CaesarError::UserError("Could not retrieve loaded source file.".into())
        })?;
        let output_path = output_file_path(&stored_file.path, &output_dir)?;
        let included = select_included_decls(options, server, &lowerer, *file_id, &roots, tcx)?;
        let plan = FilePlan {
            file_id: *file_id,
            output_path,
            roots,
            included,
        };
        let dafny_file = lowerer.lower_file(plan.file_id, &plan.roots, &plan.included)?;
        let rendered = pretty::print_file(&dafny_file);
        create_dir_all(plan.output_path.parent().unwrap())?;
        std::fs::write(&plan.output_path, rendered)?;
        wrote_anything = true;

        if options.run_dafny {
            run_dafny_verify(&plan.output_path)?;
        }
    }

    drop(temp_dir.take());

    if !wrote_anything {
        return Err(CaesarError::UserError(
            "No matching top-level procs were selected for Dafny translation.".into(),
        ));
    }

    Ok(())
}

fn output_file_path(
    source_path: &SourceFilePath,
    output_dir: &Path,
) -> Result<PathBuf, CaesarError> {
    let relative = source_path
        .relative_to_cwd()
        .map_err(CaesarError::IoError)?;
    match relative {
        SourceFilePath::Path(path) => {
            let mut output_path = output_dir.join(path);
            output_path.set_extension("dfy");
            Ok(output_path)
        }
        _ => Err(CaesarError::UserError(
            "The Dafny backend only supports filesystem-backed input files.".into(),
        )),
    }
}

fn run_dafny_verify(path: &Path) -> Result<(), CaesarError> {
    let output = Command::new("dafny").arg("verify").arg(path).output()?;
    if output.status.success() {
        return Ok(());
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    Err(CaesarError::UserError(
        format!(
            "`dafny verify {}` failed with status {}.\nstdout:\n{}\nstderr:\n{}",
            path.display(),
            output.status,
            stdout,
            stderr
        )
        .into(),
    ))
}

/// Choose the declarations that must be present in one emitted `.dfy` file.
pub(crate) fn select_included_decls(
    options: &DafnyOptions,
    server: &mut dyn Server,
    lowerer: &DafnyLowerer<'_>,
    file_id: FileId,
    roots: &[Ident],
    tcx: &TyCtx,
) -> Result<HashSet<Ident>, CaesarError> {
    let mut seeds = HashSet::new();
    let root_set: HashSet<_> = roots.iter().copied().collect();

    match options.dafny_scope {
        DafnyScope::Reachable => {
            for root in roots {
                ensure_required_decl_supported(*root, lowerer, tcx)?;
                seeds.insert(*root);
            }
        }
        DafnyScope::All => {
            for record in &lowerer.index.ordered {
                if record.file_id != file_id {
                    continue;
                }
                let local_support = lowerer.local_support(record);
                if root_set.contains(&record.ident) {
                    local_support.map_err(|err| {
                        CaesarError::Diagnostic(err.diagnostic(ReportKind::Error))
                    })?;
                    seeds.insert(record.ident);
                    continue;
                }

                match local_support {
                    Ok(()) => {
                        seeds.insert(record.ident);
                    }
                    Err(err) => {
                        server.add_diagnostic(err.diagnostic(ReportKind::Warning).with_note(
                            "Skipping this declaration while translating with `--dafny-scope all`.",
                        ))?;
                    }
                }
            }
        }
    }

    let included: HashSet<_> = lowerer
        .depgraph
        .get_reachable(seeds.iter().copied())
        .into_hash_set();

    for ident in &included {
        ensure_required_decl_supported(*ident, lowerer, tcx)?;
    }

    Ok(included)
}

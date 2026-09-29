use std::path::PathBuf;

use ariadne::ReportKind;
use regex::Regex;

use super::{
    index::DeclIndex,
    lower::DafnyLowerer,
    pretty,
    translate::{select_included_decls, FilePlan},
};
use crate::{
    ast::SourceFilePath,
    depgraph::DepGraph,
    driver::{
        commands::{
            options::{DafnyOptions, DafnyScope, InputOptions},
            verify::VerifyCommand,
        },
        front::parse_and_tycheck,
    },
    front::parser::ParserMode,
    servers::{Server, TestServer},
    smt::funcs::axiomatic::AxiomInstantiation,
};

fn translate_test_source(
    source: &str,
    scope: DafnyScope,
    filter: Option<&str>,
    werr: bool,
) -> (
    Result<String, crate::driver::error::CaesarError>,
    TestServer,
) {
    let mut verify_options = VerifyCommand::default();
    verify_options.input_options.werr = werr;

    let mut server = TestServer::new(&verify_options);
    let file_id = server
        .get_files_internal()
        .lock()
        .unwrap()
        .add(SourceFilePath::Builtin, source.to_owned())
        .id;

    let input_options = InputOptions {
        files: vec![],
        raw: false,
        parser_mode: ParserMode::Both,
        werr,
        filter: None,
    };

    let res = (|| {
        let (mut module, tcx) = parse_and_tycheck(
            &input_options,
            &verify_options.debug_options,
            &mut server,
            &[file_id],
        )?;

        let mut depgraph = DepGraph::new(AxiomInstantiation::Decreasing);
        for source_unit in &mut module.items {
            source_unit.enter_mut().populate_depgraph(&mut depgraph)?;
        }

        let index = DeclIndex::new(&module);
        let lowerer = DafnyLowerer {
            tcx: &tcx,
            depgraph: &depgraph,
            index: &index,
        };
        let filter = filter.map(|regex| Regex::new(regex).unwrap());
        let roots = index.selected_roots_for_file(file_id, filter.as_ref());
        let dafny_options = DafnyOptions {
            dafny_dir: None,
            run_dafny: false,
            dafny_scope: scope,
        };
        let included =
            select_included_decls(&dafny_options, &mut server, &lowerer, file_id, &roots, &tcx)?;
        let plan = FilePlan {
            file_id,
            output_path: PathBuf::from("test.dfy"),
            roots,
            included,
        };
        let file = lowerer.lower_file(plan.file_id, &plan.roots, &plan.included)?;
        Ok(pretty::print_file(&file))
    })();

    (res, server)
}

#[test]
fn reachable_scope_includes_selected_root_and_helper() {
    let source = r#"
            proc helper(x: UInt) -> (y: UInt)
                pre ?(true)
                post ?(y == x)
            {
                y = x
            }

            proc root(x: UInt) -> (y: UInt)
                pre ?(true)
                post ?(y == x)
            {
                y = helper(x)
            }

            proc unused(x: UInt) -> (y: UInt)
                pre ?(true)
                post ?(y == x)
            {
                y = x
            }
        "#;
    let rendered = translate_test_source(source, DafnyScope::Reachable, Some("root$"), true)
        .0
        .unwrap();
    assert!(rendered.contains("method helper"));
    assert!(rendered.contains("method root"));
    assert!(!rendered.contains("method unused"));
}

#[test]
fn all_scope_includes_unreachable_translateable_proc() {
    let source = r#"
            proc helper(x: UInt) -> (y: UInt)
                pre ?(true)
                post ?(y == x)
            {
                y = x
            }

            proc root(x: UInt) -> (y: UInt)
                pre ?(true)
                post ?(y == x)
            {
                y = helper(x)
            }

            proc unused(x: UInt) -> (y: UInt)
                pre ?(true)
                post ?(y == x)
            {
                y = x
            }
        "#;
    let rendered = translate_test_source(source, DafnyScope::All, Some("root$"), true)
        .0
        .unwrap();
    assert!(rendered.contains("method helper"));
    assert!(rendered.contains("method root"));
    assert!(rendered.contains("method unused"));
}

#[test]
fn all_scope_warns_and_skips_unreachable_unsupported_decl() {
    let source = r#"
            proc root(x: UInt) -> (y: UInt)
                pre ?(true)
                post ?(y == x)
            {
                y = x
            }

            coproc ghost() -> ()
                pre ?(false)
                post ?(false)
            {}
        "#;
    let (res, server) = translate_test_source(source, DafnyScope::All, Some("root$"), false);
    let rendered = res.unwrap();
    assert!(rendered.contains("method root"));
    assert!(!rendered.contains("ghost"));
    assert_eq!(server.diagnostics.len(), 1);
    assert_eq!(server.diagnostics[0].kind(), ReportKind::Warning);
}

#[test]
fn required_unsupported_dependency_fails_translation() {
    let source = r#"
            proc root() -> (b: Bool)
                pre ?(true)
                post ?(b == true || b == false)
            {
                b = flip(0.5)
            }
        "#;
    let res = translate_test_source(source, DafnyScope::Reachable, Some("root$"), true).0;
    assert!(res.is_err());
}

#[test]
fn user_defined_select_stays_a_function_call() {
    let source = r#"
            domain List {
                func nil(): List
                func select(ls: List, i: UInt): Int
            }

            proc root(ls: List) -> (x: Int)
                post ?(x == select(ls, 0))
            {
                x = select(ls, 0)
            }
        "#;
    let rendered = translate_test_source(source, DafnyScope::Reachable, Some("root$"), true)
        .0
        .unwrap();
    assert!(rendered.contains("function select(ls: List, i: nat): int"));
    assert!(rendered.contains("ensures ((x == select(ls, 0)))"));
    assert!(rendered.contains("x := select(ls, 0);"));
    assert!(!rendered.contains("ls[0]"));
}

#[test]
fn builtin_select_and_len_stay_sequence_operations() {
    let source = r#"
            proc root(ls: []Int) -> (x: Int)
                pre ?(0 < len(ls))
                post ?(x == select(ls, 0))
            {
                x = select(ls, 0)
            }
        "#;
    let rendered = translate_test_source(source, DafnyScope::Reachable, Some("root$"), true)
        .0
        .unwrap();
    assert!(rendered.contains("requires ((0 < |ls|))"));
    assert!(rendered.contains("ensures ((x == ls[0]))"));
    assert!(rendered.contains("x := ls[0];"));
}

#[test]
fn builtin_store_stays_a_sequence_update() {
    let source = r#"
            proc root(ls: []Int) -> (res: []Int)
                pre ?(0 < len(ls))
                post ?(select(res, 0) == 7)
            {
                res = store(ls, 0, 7)
            }
        "#;
    let rendered = translate_test_source(source, DafnyScope::Reachable, Some("root$"), true)
        .0
        .unwrap();
    assert!(rendered.contains("requires ((0 < |ls|))"));
    assert!(rendered.contains("ensures ((res[0] == 7))"));
    assert!(rendered.contains("res := ls[0 := 7];"));
}

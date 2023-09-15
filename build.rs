extern crate lalrpop;

fn main() {
    // LALRPOP
    lalrpop::Configuration::new()
        .emit_rerun_directives(true)
        .process_dir("src/front/parser/")
        .unwrap();

    // Version info
    built::write_built_file().expect("Failed to acquire build-time information");
}

# Caesar's Integration Tests

Here are Caesar's integration tests.
They are automatically run by `cargo test`.
For options on how to run these tests, execute `cargo test --test integration -- --help`.
E.g. you can do `cargo test --test integration -- --verbose`.

The `integration.rs` runner will collect all files ending in `.heyvl` in this directory.
The runner will search for directives like `RUN: ` and `XFAIL: ` in the file.
See the documentation of `integration.rs` for more information.

---
sidebar_position: 8
---

# Development Guide

This guide explains how Caesar and related tools work internally and how to contribute to the code.

The project is maintained in a GitHub repository: [`github.com/moves-rwth/caesar`](https://github.com/moves-rwth/caesar).
We use GitHub's issue tracker.
Feel free to [open an issue](https://github.com/moves-rwth/caesar/issues) or [start a discussion](https://github.com/moves-rwth/caesar/discussions).
You can also reach the main developer, [Philipp Schröer](https://moves.rwth-aachen.de/people/philipp-schroer/), by email: [`phisch@cs.rwth-aachen.de`](mailto:phisch@cs.rwth-aachen.de).
We are very happy to work and research with you on Caesar!

## Caesar

Follow the [*"Build From Source"* section in the installation instructions](./getting-started/installation.mdx#build-source) to learn how to compile Caesar.
This gives you an environment to modify the code and run it locally.

The source code of the main [caesar tool](./caesar) begins at the root level of the Git repository.
It is a [cargo workspace](https://doc.rust-lang.org/book/ch14-03-cargo-workspaces.html) containing the main `caesar` crate and the `z3rro` crate.

We try to use [rustdoc](https://doc.rust-lang.org/rustdoc/what-is-rustdoc.html) as much as possible to document how `caesar` works.
Just run `cargo doc --open` to build and open the Rust API documentation of the project.

To run all tests, execute `cargo test --all`.

The source code for the `caesar` crate lives in [`src/`](https://github.com/moves-rwth/caesar/tree/master/src).

Integration tests live in the [`tests/`](https://github.com/moves-rwth/caesar/tree/master/tests) directory.
Read the associated [`tests/README.md`](https://github.com/moves-rwth/caesar/blob/master/tests/README.md) for more information about these tests.

`z3rro` is our dedicated crate for basic SMT functionality.
It lives in [`z3rro/`](https://github.com/moves-rwth/caesar/tree/master/z3rro).
The idea is that this code is independent of Caesar itself and may be useful to other projects.

## Website

The documentation you are reading right now is built using [Docosaurus](https://docusaurus.io/) and lives in the [`website`](https://github.com/moves-rwth/caesar/tree/main/website) directory.

You can install it using `yarn` or `npm`: Run `yarn` or `npm install`.

Then either run `yarn start` or `npm run start` to start a local development server and open the site in a browser window.

## VSCode Extension

[Caesar's VSCode extension](./caesar/vscode-and-lsp.md) lives in the [`vscode-ext/` directory](https://github.com/moves-rwth/caesar/tree/main/vscode-ext).
The [`vscode-ext/vsc-extension-quickstart.md`](https://github.com/moves-rwth/caesar/blob/main/vscode-ext/vsc-extension-quickstart.md) document explains the basics of how to develop and debug the binary.

Here, we still use `npm` for package management.
 * `npm install` to install the necessary dependencies.
 * `npm run compile` to compile the extension and run the linter.
 * `npm run watch` to start a TypeScript compiler server that recompiles when changes are made.
 * `npm run lint` to run the linter.
 * `npm run vscode:prepublish` compiles as well.

## pgcl2heyvl

`pgcl2heyvl` is our old [pGCL frontend](./pgcl.md).
It lives in [`pgcl/pgcl2heyvl`](https://github.com/moves-rwth/caesar/tree/main/pgcl/pgcl2heyvl).
The tool is written in Python and we use [poetry](https://python-poetry.org/) for its dependency management.
The most important dependency is [`probably`](https://github.com/Philipp15b/probably) which defines the accepted pGCL syntax.

The tool has a terrible user interface (need to specify invariants as command-line arguments!) and `pgcl2heyvl` is being phased out (see [its documentation](./pgcl.md)) in favor of integration of the encodings directly in Caesar.

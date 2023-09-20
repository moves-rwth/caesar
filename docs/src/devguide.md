# Development Guide

This guide explains how Caesar and related tools work internally and how to contribute to the code.

The whole project currently lives in a GitHub repository: [`github.com/moves-rwth/caesar`](https://github.com/moves-rwth/caesar).
We use GitHub's issue tracker.

This project is being built at the [Chair for Software Modeling and Verification (MOVES)](https://moves.rwth-aachen.de/) at RWTH Aachen University.

## Caesar

[Caesar's](./caesar.md)'s source code is begins at the root level of the Git repository.
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

## pgcl2heyvl

`pgcl2heyvl` is our [pGCL frontend](./frontends/pgcl.md).
It lives in [`pgcl/pgcl2heyvl`](https://github.com/moves-rwth/caesar/tree/master/pgcl/pgcl2heyvl).
The tool is written in Python and we use [poetry](https://python-poetry.org/) for its dependency management.
The most important dependency is [`probably`](https://github.com/Philipp15b/probably) which defines the accepted pGCL syntax.

The tool has a terrible user interface (need to specify invariants as command-line arguments!).
Someone should improve that.

## mdbook Documentation

The documentation you are reading right now is built using [mdbook](https://rust-lang.github.io/mdBook/).
We also require [graphviz](https://graphviz.org/) to be installed as well as [`mdbook-graphviz`](https://github.com/dylanowen/mdbook-graphviz).

After installing graphviz and running `cargo install mdbook mdbook-graphviz`, you can host a local server with the documentation and open it in a web browser:
```
cd docs
mdbook serve --open
```

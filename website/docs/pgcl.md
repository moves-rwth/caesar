---
sidebar_position: 11
---

# pgcl2heyvl Frontend

The now deprecated `pgcl2heyvl` tool is a frontend for pGCL programs written in the syntax of the [*probably* library](https://github.com/Philipp15b/probably)
Given an annotated pGCL program, it automatically generates HeyVL code for Caesar.

:::caution
The `pgcl2heyvl` tool is deprecated and its functionality is now fully integrated into Caesar itself.
Simply use HeyVL [statements](heyvl/statements.md) and use the built-in [proof rules](proof-rules/README.md) on `while` loops.

Using HeyVL directly enables the use of the proof rule encodings with features of Caesar that pgcl2heyvl does not support, such as [domain declarations](heyvl/domains.md) or a more powerful set of [expressions](heyvl/expressions.md).
Furthermore, Caesar's proof rules have support for [slicing](caesar/slicing.md), which enables detailed error messages such as "the invariant is not inductive".
:::

## Installing pgcl2heyvl

To run `pgcl2heyvl`, first install dependencies using [poetry](https://python-poetry.org/).
Poetry is a build system and dependency manager for Python.
[Here are installation instructions for Poetry](https://python-poetry.org/docs/).

In the [`pgcl/pgcl2heyvl` directory](https://github.com/moves-rwth/caesar/tree/main/pgcl/pgcl2heyvl), install dependencies:
```bash
cd pgcl/pgcl2heyvl
poetry install
```

## Using pgcl2heyvl

After installation, use `poetry run` to run `pgcl2heyvl`.
```bash
cd pgcl/pgcl2heyvl
poetry run pgcl2heyvl FILE > OUTFILE
```

where `FILE` is a file name with the pGCL program and `OUTFILE` is the name of the output file with the HeyVL code.

The first line in `FILE` must include `// ARGS: --post POST --pre PRE --k K`.
`POST` is a post-expectation, and `PRE` is a pre-expectation (in [pGCL syntax](#pgcl-syntax)).
The `K` argument is an integer that specifies which `k`-induction to use for the encoding.

If the pGCL program includes a single loop, then `PRE` will be used as the loop invariant.
When the program includes multiple loops, additional invariants must be specified using `--invariant`.

The command-line interface documentation is available by invoking `poetry run pgcl2heyvl --help`.

## pGCL Examples

You can find pGCL examples in the [`pgcl/examples`](https://github.com/moves-rwth/caesar/tree/main/pgcl/examples) directory.
They include all necessary parameters to generate verifying HeyVL files.

For these examples, the generated HeyVL files are located under [`pgcl/examples-heyvl`](https://github.com/moves-rwth/caesar/tree/main/pgcl/examples-heyvl).
Verification with `caesar` requires the `--raw` command-line flag since these files are just sequences of HeyVL statements.

Instructions on how to (re-)generate these examples are located in [`pgcl/examples-heyvl/README.md`](https://github.com/moves-rwth/caesar/blob/main/pgcl/examples-heyvl/README.md).

To execute `caesar` with the generated HeyVL files, refer to the [benchmarks section of Caesar's documentation](./caesar/benchmarks.md).

## pGCL Syntax

`pgcl2heyvl` uses the [`probably`](https://github.com/Philipp15b/probably) Python library to parse and type-check pGCL programs.
That means the pGCL syntax of `probably` is used for the pGCL programs and the `--pre`, `--post`, and `--invariant` command-line parameters.

There is no formal specification for the exact pGCL syntax that `probably` accepts, but here are some pointers:

 * pGCL examples in [`pgcl/examples`](https://github.com/moves-rwth/caesar/tree/master/pgcl/examples).
 * The [`probably` documentation](https://philipp15b.github.io/probably/pgcl.html). There are many doctests with examples.
 * The [grammar specification](https://philipp15b.github.io/probably/pgcl_grammar.html#pgcl-grammar) used by `probably` built on top of the [Lark parsing toolkit](https://github.com/lark-parser/lark).
 * [`probably`'s tests](https://github.com/Philipp15b/probably/tree/master/tests).

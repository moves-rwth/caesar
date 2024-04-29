---
sidebar_position: 7
---

# pGCL Frontend

At the moment, _pGCL_, the probabilistic guarded command langage, is the only supported frontend.
We have a tool, `pgcl2heyvl`, that automatically generates HeyVL code from pGCL programs.

Most of pGCL's syntax can be encoded in fairly straightforward manner, but loops are a bit more complicated and require additional user annotations (loop invariants).
The tool supports both Park induction and the more general k-induction.

:::info
The `pgcl2heyvl` tool is being phased out and its functionality is being integrated directly into Caesar itself.
This will enable the use of the proof rule encodings with features of Caesar that pgcl2heyvl does not support, such as [domain declarations](heyvl/domains.md) or a more powerful set of [expressions](heyvl/expressions.md).
:::

## Using pgcl2heyvl

[`pgcl2heyvl`](https://github.com/moves-rwth/caesar/tree/master/pgcl/pgcl2heyvl) is a Python program that reads a pGCL program from a file and uses additional user-provided annotations to encode loops.
The output is a HeyVL file.

To run `pgcl2heyl`, enter its source code directory and execute it using [poetry](https://python-poetry.org/).
Poetry is a build system and dependency manager for Python.
[Here are installation instructions for Poetry](https://python-poetry.org/docs/).

For example:
```bash
cd pgcl/pgcl2heyvl
poetry run pgcl2heyvl FILE --post POST --pre PRE --k K > OUTFILE
```
where `FILE` is a file name with the pGCL program, `POST` is a post-expectation, and `PRE` is a pre-expectation (in [pGCL syntax](#pgcl-syntax)).
The `K` argument is an integer that specifies which `k`-induction to use for the encoding.
`OUTFILE` is the name of the output file with the HeyVL code.

If the pGCL program includes a single loop, then `PRE` will be used as the loop invariant.
When the program includes multiple loops, additional invariants must be specified using `--invariant`.

If the input file starts with a comment `// ARGS: ` followed by command-line arguments, it will use these as defaults.

The command-line interface documentation is available by invoking `poetry run pgcl2heyvl --help`.

And yes, we're aware the user experience of this tool is particularly horrible.
We're working on it!

## pGCL Examples

You can find pGCL examples in the [`pgcl/examples`](https://github.com/moves-rwth/caesar/tree/master/pgcl/examples) directory.
They include all necessary parameters to generate verifying HeyVL files.

For these examples, the generated HeyVL files are located under [`pgcl/examples-heyvl`](https://github.com/moves-rwth/caesar/tree/master/pgcl/examples-heyvl).
Verification with `caesar` requires the `--raw` command-line flag since these files are just sequences of HeyVL statements.

Instructions on how to (re-)generate these examples are located in [`pgcl/examples-heyvl/README.md`](https://github.com/moves-rwth/caesar/blob/master/pgcl/examples-heyvl/README.md).

To execute `caesar` with the generated HeyVL files, refer to the [benchmarks section of Caesar's documentation](./caesar/benchmarks.md).

## pGCL Syntax

`pgcl2heyvl` uses the [`probably`](https://github.com/Philipp15b/probably) Python library to parse and type-check pGCL programs.
That means the pGCL syntax of `probably` is used for the pGCL programs and the `--pre`, `--post`, and `--invariant` command-line parameters.

There is no formal specification for the exact pGCL syntax that `probably` accepts, but here are some pointers:

 * pGCL examples in [`pgcl/examples`](https://github.com/moves-rwth/caesar/tree/master/pgcl/examples).
 * The [`probably` documentation](https://philipp15b.github.io/probably/pgcl.html). There are many doctests with examples.
 * The [grammar specification](https://philipp15b.github.io/probably/pgcl_grammar.html#pgcl-grammar) used by `probably` built on top of the [Lark parsing toolkit](https://github.com/lark-parser/lark).
 * [`probably`'s tests](https://github.com/Philipp15b/probably/tree/master/tests).

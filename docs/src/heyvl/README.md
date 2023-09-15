# HeyVL

HeyVL is a verification language similar to Viper and Boogie (see [related work](../related-work.md)).
The main innovation is that it supports _quantitative_ reasoning via its constructs inspired by Gödel logic.

A HeyVL file consists of a sequence of declarations: [procedure](./procs.md) and [domain declarations](./domains.md).
<small>If `--raw` is passed to the command line, then HeyVL files are parsed as sequences of statements without declarations. See [Caesar documentation](../caesar.md) for more information.</small>

## Use the source, Luke

We do not formally describe the syntax of HeyVL in this documentation.
You can find a more formal definition in the [`src/front/parser/grammar.lalrpop`](https://github.com/Philipp15b/caesar/blob/master/src/front/parser/grammar.lalrpop) file that specifies the syntax used to generate Caesar's parser.
It is written in the [LALRPOP language](https://lalrpop.github.io/lalrpop/tutorial/index.html).

## Examples

The [`pgcl/examples-heyvl`](https://github.com/Philipp15b/caesar/tree/master/pgcl/examples-heyvl) directory contains the machine-translated HeyVL code for our pGCL examples.
Note that they are just sequences of HeyVL statements without wrapping procedure declarations.
Refer to the page on the [pGCL frontend](../frontends/pgcl.md) for more information.

Caesar's integration tests in [`tests/`](https://github.com/Philipp15b/caesar/tree/master/tests) can also serve as a reference.
Refer to the [development guide](../devguide.md#caesar) for more information about these tests.

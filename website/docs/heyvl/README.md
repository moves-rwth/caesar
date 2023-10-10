---
sidebar_position: 3
---

# HeyVL

HeyVL is a verification language similar to Viper and Boogie.
The main innovation is that it supports _quantitative_ reasoning via its constructs inspired by Gödel logic.
Refer to our [publications](../publications.md) for details on the theory.

A HeyVL file consists of a sequence of declarations: [procedure](./procs.md) and [domain declarations](./domains.md).

```mdx-code-block
import DocCardList from '@theme/DocCardList';

<DocCardList />
```

## Use the source, Luke

We do not formally describe the syntax of HeyVL in this documentation.
You can find a more formal definition in the [`src/front/parser/grammar.lalrpop`](https://github.com/moves-rwth/caesar/blob/main/src/front/parser/grammar.lalrpop) file that specifies the syntax used to generate Caesar's parser.
It is written in the [LALRPOP language](https://lalrpop.github.io/lalrpop/tutorial/index.html).

## Examples

The [`pgcl/examples-heyvl`](https://github.com/moves-rwth/caesar/tree/main/pgcl/examples-heyvl) directory contains the machine-translated HeyVL code for our pGCL examples.
Note that they are just sequences of HeyVL statements without wrapping procedure declarations.
Refer to the page on the [pGCL frontend](../pgcl.md) for more information.

Caesar's integration tests in [`tests/`](https://github.com/moves-rwth/caesar/tree/main/tests) can also serve as a reference.
Refer to the [development guide](../devguide.md#caesar) for more information about these tests.

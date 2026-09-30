---
description: Worked examples of expected runtimes, probability bounds, termination, and model checking.
sidebar_position: 3
---

# A Zoo of HeyVL Examples

## Worked Examples

- **[Expected Runtime of a Geometric Loop](./first-proof.mdx).**
  A short first example: use a supplied invariant to bound the expected number of loop iterations.
- **[Lossy List Traversal](./heyvl-guide.md#verifying-our-first-program-lossy-list-traversal).**
  Define a list type and an exponential function, then verify a probability bound that depends on the list's length.
- **[Induction and k-Induction](../proof-rules/induction.md#usage).**
  Compare invariants that are preserved by one loop iteration with those that require several iterations.
- **[Almost-Sure Termination](../proof-rules/ast.md#usage).**
  Prove termination with probability one for a loop whose chance of exiting decreases as its counter grows.
- **[Model Checking](../model-checking.md#usage).**
  Analyze a bounded geometric loop using Caesar's Storm backend, without supplying an invariant.

## Example Collections

The repository contains further [HeyVL examples and tests](https://github.com/moves-rwth/caesar/tree/main/tests), including examples for individual language features and proof rules.
It also contains [pGCL programs](https://github.com/moves-rwth/caesar/tree/main/pgcl/examples) and their [translations to HeyVL](https://github.com/moves-rwth/caesar/tree/main/pgcl/examples-heyvl).

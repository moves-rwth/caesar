---
sidebar_position: 5
---

# Proof Rules

Caesar supports a number of proof rule encodings out of the box.
The proof rules are used via annotations on while loops.
All while loops used in HeyVL must have a proof rule annotation so that they can be verified with loop-free verification pre-expectation reasoning.

To help you use proof rules correctly, Caesar supports [calculus annotations](./calculi.md) on procedures.
These annotations specify a desired reasoning calculus and limit the proof rules for loops to ensure that only sound proof rules for the respective calculi are used.

If you have read our [OOPSLA '23 publication](../publications.md#oopsla-23): these proof rules were implemented in our [`pgcl2heyvl`](../pgcl.md) tool to reason about pGCL programs, but are now implemented directly in Caesar.
This allows verifiers for languages other than pGCL to re-use the proof rule encodings.

:::caution

Proof rules are only sound in specific contexts.
Using proof rules in a wrong way may lead to _unsoundness_, i.e. a program may falsely verify.
To be certain that a proof rule may be applied, correctness of the proof rule needs to be proven with respect to the language semantics that are to be encoded.
See our [OOPSLA '23 publication](../publications.md#oopsla-23) for details on the theory.

:::

```mdx-code-block
import DocCardList from '@theme/DocCardList';

<DocCardList />
```

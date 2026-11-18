---
description: Learn what Caesar can verify, run a first proof in HeyVL, and find the language and tool references.
sidebar_position: 1
slug: /
---

# Introduction

Caesar is a deductive verifier for probabilistic programs.
It can prove bounds on the probability that a protocol abandons a message or on the expected number of steps in a randomized algorithm.
It also checks whether a program terminates with probability one and whether it satisfies Boolean specifications, such as returning a sorted list whenever it terminates.

## Getting Started {#overview}

[Install Caesar](./getting-started/installation.mdx) to verify programs in VS Code or from the command line.
In the [first example](./getting-started/first-proof.mdx), you verify that a loop that flips a fair coin until heads takes at most two iterations in expectation.

The [Guide to HeyVL](./getting-started/heyvl-guide.md) shows how to write your own programs and specifications.
Browse [HeyVL Examples](./getting-started/zoo.md) for worked proofs and downloadable programs, from sorting and sampling algorithms to random walks and communication protocols.

## How Verification Works

You write the program and its specification in HeyVL, Caesar's verification language.
For each loop, you select a proof rule and supply the information it needs, such as a loop invariant.
Caesar generates verification conditions and checks them with the Z3 SMT solver.
This lets you reason symbolically about unbounded loops and programs with infinitely many possible states.

## Reference

- [HeyVL](./heyvl/) documents the language, and the [standard library](./stdlib/) documents built-in types, functions, and distributions.
- [Proof Rules](./proof-rules/) covers loop annotations, their assumptions, and the guarantees they establish.
- [The Caesar Tool](./caesar/) covers the command line, VS Code integration, and diagnostics for debugging proofs.
- [Model Checking](./model-checking.md) explains how to export supported HeyVL programs to JANI and analyze them with Storm.

## Research and Citation {#our-theory-paper}

Read about Caesar's verification workflow and tooling in the [CAV 2026 tool paper](./publications.md#cav-26-caesar-a-deductive-verifier-for-probabilistic-programs).
For the design of HeyVL and the theory behind the verifier, see the [OOPSLA 2023 paper](./publications.md#oopsla-23).
See [Publications](./publications.md) for related work and BibTeX entries.

## Questions and Feedback {#contact-us}

Ask a question in [GitHub Discussions](https://github.com/moves-rwth/caesar/discussions) or [open an issue](https://github.com/moves-rwth/caesar/issues) to report a bug.
For research questions or collaboration, email [Philipp Schroer](mailto:phisch@cs.rwth-aachen.de).

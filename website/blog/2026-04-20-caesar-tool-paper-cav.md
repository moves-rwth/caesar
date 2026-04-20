---
title: Tool Paper on Caesar Accepted at CAV 2026
authors: phisch
tags: [publications]
---

Our tool paper _"Caesar: A Deductive Verifier for Probabilistic Programs"_ was accepted as a tool paper at [CAV 2026](https://conferences.i-cav.org/2026/), to be held in Lisbon, Portugal.
The authors are Philipp Schröer, Kevin Batz, Umut Yiğit Dural, Darion Haase, Benjamin Lucien Kaminski, Joost-Pieter Katoen, and Christoph Matheja.

The paper reports on five years of Caesar development and presents Caesar as a deductive verifier for probabilistic programs in its current form: from the HeyVL/HeyLo core and the SMT-based pipeline via Z3 to the surrounding tooling and verification features.
Compared to our earlier OOPSLA 2023 paper, which introduced the formal foundations of HeyVL and HeyLo, the new tool paper focuses on Caesar as a practical verification tool.
Among the additions highlighted in the paper are the *Caesar Verifier* VSCode extension, support for limited functions and improved quantifier handling, the model checking backend via JANI and Storm, stronger soundness checks and guardrails for proof-rule usage, and slicing-based diagnostics.

<!-- truncate -->

The paper builds on our earlier OOPSLA paper [_"A Deductive Verification Infrastructure for Probabilistic Programs"_](https://doi.org/10.1145/3622870) ([announcement post](/blog/2023/09/28/oopsla23)).
In particular, it covers:
 * the [*Caesar Verifier* VSCode extension](/docs/caesar/vscode-and-lsp), which is now the recommended way to use Caesar;
 * support for [limited functions](/docs/caesar/debugging#function-encodings-and-limited-functions) and improved [quantifier handling](/docs/caesar/debugging#selecting-quantifier-instantiation-strategies);
 * the [model checking backend](/docs/model-checking) via JANI and Storm;
 * stronger [soundness checks for proof rules](/docs/proof-rules/approximations#what-is-checked) and additional guardrails for sound verification, building on Caesar's [calculus annotations](/docs/proof-rules/approximations#calculus-annotations) and the ["More Guardrails" release](/blog/2025/01/17/caesar-2-1#more-guardrails);
 * [slicing-based diagnostics](/docs/caesar/slicing) and related user-facing tooling.

If you want to explore these features on this website, the most relevant documentation is:
 * [Getting Started](/docs/getting-started)
 * [VSCode Extension & LSP Support](/docs/caesar/vscode-and-lsp)
 * [Debugging Caesar](/docs/caesar/debugging)
 * [Model Checking Support](/docs/model-checking)
 * [Soundness of Proof Rules](/docs/proof-rules/approximations)
 * [Slicing and Diagnostics](/docs/caesar/slicing)

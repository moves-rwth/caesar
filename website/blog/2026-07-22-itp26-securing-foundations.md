---
title: Securing HeyVL's Foundations in Lean
authors: phisch
tags: [publications]
---

The paper [_"Securing the Foundations of an Intermediate Language for Probabilistic Program Verification"_](https://doi.org/10.4230/LIPIcs.ITP.2026.29) by Oliver Bøving and Christoph Matheja was published at [ITP 2026](https://itp-conference-2026.github.io/) in Lisbon, Portugal.

The paper develops mechanized foundations in the interactive theorem prover Lean for proving the correctness of probabilistic-program verification techniques and their encodings in HeyVL.
All results are built on top of [mathlib](https://leanprover-community.github.io/).

The **open-access paper is available online**: [_"Securing the Foundations of an Intermediate Language for Probabilistic Program Verification"_](https://drops.dagstuhl.de/storage/00lipics/lipics-vol382-itp2026/LIPIcs.ITP.2026.29/LIPIcs.ITP.2026.29.pdf).

<!-- truncate -->

Caesar makes it possible to rapidly prototype verification techniques by encoding programs, specifications, and proof rules in the quantitative intermediate verification language HeyVL.
However, establishing that such an encoding is correct is subtle: the argument must connect HeyVL's denotational semantics to the probabilistic behavior of the encoded program.

The paper provides a machine-checked foundation for such arguments. In particular, it:

 * formalizes Markov decision processes and constructs the probability spaces needed to give probabilistic programs an operational semantics;
 * establishes least-fixed-point characterizations of expected total costs in Markov decision processes;
 * derives sound weakest-precondition calculi for partial and total correctness, including unbounded loops, nondeterminism, and conditioning;
 * develops a deep embedding of HeyVL in Lean; and
 * uses this machinery to verify several existing HeyVL encodings.

The complete [Lean formalization is available on Zenodo](https://doi.org/10.5281/zenodo.20346876).
For more background on HeyVL and Caesar's original formal foundations, see our OOPSLA 2023 paper [_"A Deductive Verification Infrastructure for Probabilistic Programs"_](https://doi.org/10.1145/3622870) and its [announcement post](/blog/2023/09/28/oopsla23).

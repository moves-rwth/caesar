---
title: Paper on Slicing Accepted at ESOP 2026
authors: phisch
tags: [publications]
---

Our paper [_"Error Localization, Certificates, and Hints for Probabilistic Program Verification via Slicing"_](https://arxiv.org/abs/2512.20214) was accepted at the [European Symposium on Programming (ESOP) 2026](https://etaps.org/2026/conferences/esop/) to be held in Turin, Italy.
The authors are Philipp Schröer, Darion Haase, and Joost-Pieter Katoen.
[An extended version of the paper is already available on arXiv](https://arxiv.org/abs/2512.20214).

The paper presents theoretical foundations and the implementation of our slicing-based user diagnostics in Caesar, which we dub *Brutus*.
On this website, you can also find the [user guide-level documentation on slicing in Caesar](/docs/caesar/slicing).
See also the [announcement of Caesar 2.0](./2024-05-20-caesar-2-0.md), which introduced the first slicing implementation in Caesar.

<!-- truncate -->

<a href={require("/img/slicing-demo.png").default} className="float-right-responsive">
    <img src={require("/img/slicing-demo.png").default} className="item shadow--tl" />
</a>

The theory is about *slices*, i.e. smaller sub-programs, to provide
 1. error localization (*error-witnessing slices*),
 2. proof simplification (*verification-witnessing slices*), and
 3. preserving successful verification results (*verification-preserving slices*).

These notions are defined on the quantitative intermediate verification language HeyVL, and thus the theory and implementation work for all statements expressible in HeyVL, such as `assume` and `assert` statements.
Based on these notions, specialized slicing-based diagnostics are provided for various proof rules, such as the [induction proof rule](/docs/proof-rules/induction) or [procedure calls](/docs/heyvl/procs) (called *specification statements* in the paper).
The correctness of the above is formally proven in the paper.

<a href={require("/img/general-slicing-demo.png").default} className="float-right-responsive">
    <img src={require("/img/general-slicing-demo.png").default} className="item shadow--tl" />
</a>

The paper also reports on the implementation of these ideas.
We explain the algorithms to compute the different slice types efficiently.
For error reporting, we use a binary search-based algorithm to find minimal error-witnessing slices.
For the other two slice types, we compare different algorithms based on unsat core extraction, minimal unsat subset enumeration, and a direct SMT encoding of the slicing problem.
Our empirical evaluation of Brutus on existing and new benchmarks shows that we can find slices that are both small and informative.


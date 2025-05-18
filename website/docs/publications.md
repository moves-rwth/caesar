---
title: Publications
sidebar_position: 9
---

# Academic Publications

Caesar is a project from a collaboration of the [Chair for Software Modeling and Verification (MOVES)](https://moves.rwth-aachen.de/) at RWTH Aachen University, the [QUAVE group](https://quave.cs.uni-saarland.de/) at Saarland University, the [PPLV group](http://pplv.cs.ucl.ac.uk/welcome/) at University College London and the [SSE section](https://www.compute.dtu.dk/english/research/research-sections/software-systems-engineering) at Denmark Technical University.

If you are interested in collaborations or simply have some questions, please reach out to [Philipp Schroer](https://moves.rwth-aachen.de/people/philipp-schroer/) ([phisch@cs.rwth-aachen.de](mailto:phisch@cs.rwth-aachen.de)).

:::note Citing Caesar

For publications about Caesar, please cite our [OOPSLA '23 paper](#oopsla-23) ([BibTeX file](https://dblp.org/rec/journals/pacmpl/SchroerBKKM23.html?view=bibtex)):

> Philipp Schröer, Kevin Batz, Benjamin Lucien Kaminski, Joost-Pieter Katoen, Christoph Matheja. *A Deductive Verification Infrastructure for Probabilistic Programs.* Proceedings of the ACM on Programming Languages 7, OOPSLA 2023. DOI: https://doi.org/10.1145/3622870.

:::

**Overview:**

```mdx-code-block
import TOCInline from '@theme/TOCInline';

<TOCInline toc={toc} />
```

## OOPSLA '25: Foundations for Deductive Verification of Continuous Probabilistic Programs

The paper [_"Foundations for Deductive Verification of Continuous Probabilistic Programs: From Lebesgue to Riemann and Back"_](https://dl.acm.org/doi/10.1145/3720429) by Kevin Batz, Joost-Pieter Katoen, Francesca Randone, and Tobias Winkler was recently published at [OOPSLA 2025](https://2025.splashcon.org/track/OOPSLA). DOI: https://doi.org/10.1145/3720429.

This paper lays out the formal foundations for us to verify probabilistic programs that sample from continuous distributions, with support for loops, and conditioning.
One challenge is to integrate the integrals for the expected values that arise from continuous distributions into the deductive verification framework of Caesar.
The key idea is to soundly under- or over-approximate these integrals via [Riemann sums](https://en.wikipedia.org/wiki/Riemann_sum).
In addition to theoretical results such as convergence and completeness of the approach, the paper also provides case studies of continuous probabilistic programs that are encoded in HeyVL and verified with Caesar.

[See our blog post for more details and examples](/blog/2025/04/11/foundations-continuous).

## AISoLA '24: A Game-Based Semantics for the Probabilistic Intermediate Verification Language HeyVL

The publication [_"A Game-Based Semantics for the Probabilistic
Intermediate Verification Language HeyVL"_](https://doi.org/10.1007/978-3-031-75434-0_17) by Christoph Matheja was published at [AISoLA 2024](https://2024-isola.isola-conference.org/). DOI: https://doi.org/10.1007/978-3-031-75434-0_17.

Quoting from its abstract:

> [T]he original language [HeyVL] lacked a formal “ground truth” in terms of a small-step operational semantics that enables an intuitive reading of HeyVL programs.
>
> In this paper, we define an operational semantics for a cleaned-up version of HeyVL in terms of *refereed* stochastic games, a novel extension of simple stochastic games in which a referee may perform quantitative reasoning about the expected outcome of sub-games and give one player an advantage if those sub-game are outside of certain boundaries.

This new operational semantics is aimed at improved intuition and ergonomics of HeyVL, as well as a possible future work enabling other verification backends such as ones based on probabilistic model checking tools.

## OOPSLA '23: A Deductive Verification Infrastructure for Probabilistic Programs {#oopsla-23}

HeyVL and Caesar were first published at [OOPSLA '23](https://2023.splashcon.org/track/splash-2023-oopsla): [A Deductive Verification Infrastructure for Probabilistic Programs](https://doi.org/10.1145/3622870) by Schröer et al.

For publication, please cite as follows ([BibTeX file](https://dblp.org/rec/journals/pacmpl/SchroerBKKM23.html?view=bibtex)):

> Philipp Schröer, Kevin Batz, Benjamin Lucien Kaminski, Joost-Pieter Katoen, Christoph Matheja. *A Deductive Verification Infrastructure for Probabilistic Programs.* Proceedings of the ACM on Programming Languages 7, OOPSLA 2023. DOI: https://doi.org/10.1145/3622870.

An **extended version with proofs and details on encodings** is available on arXiv: [A Deductive Verification Infrastructure for Probabilistic Programs (extended version) — arXiv:2309.07781](https://arxiv.org/abs/2309.07781).

**The artifact** for our OOPSLA '23 publication is [available on Zenodo](https://zenodo.org/record/8146987).
During artifact evaluation, it received the _reusable_ badge.

## Master Thesis '22: A Deductive Verifier for Probabilistic Programs

Caesar is based on a 2022 Master thesis by Philipp Schroer entitled [_"A Deductive Verifier for Probabilistic Programs"_](https://publications.rwth-aachen.de/record/998370).

The [PDF file is available online](https://publications.rwth-aachen.de/record/998370/files/998370.pdf).

DOI: https://doi.org/10.18154/RWTH-2024-11340.

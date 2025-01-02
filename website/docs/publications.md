---
title: Publications
sidebar_position: 9
---

# Academic Publications

Caesar is a project from a collaboration of the [Chair for Software Modeling and Verification (MOVES)](https://moves.rwth-aachen.de/) at RWTH Aachen University, the [QUAVE group](https://quave.cs.uni-saarland.de/) at Saarland University, the [PPLV group](http://pplv.cs.ucl.ac.uk/welcome/) at University College London and the [SSE section](https://www.compute.dtu.dk/english/research/research-sections/software-systems-engineering) at Denmark Technical University.

If you are interested in collaborations or simply have some questions, please reach out to [Philipp Schroer](https://moves.rwth-aachen.de/people/philipp-schroer/) ([phisch@cs.rwth-aachen.de](mailto:phisch@cs.rwth-aachen.de)).

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

For publication, please cite as follows:

Philipp Schröer, Kevin Batz, Benjamin Lucien Kaminski, Joost-Pieter Katoen, Christoph Matheja. *A Deductive Verification Infrastructure for Probabilistic Programs.* Proceedings of the ACM on Programming Languages 7, OOPSLA 2023. DOI: https://doi.org/10.1145/3622870.

An **extended version with proofs and details on encodings** is available on arXiv: [A Deductive Verification Infrastructure for Probabilistic Programs (extended version) — arXiv:2309.07781](https://arxiv.org/abs/2309.07781).

**The artifact** for our OOPSLA '23 publication is [available on Zenodo](https://zenodo.org/record/8146987).
During artifact evaluation, it received the _reusable_ badge.

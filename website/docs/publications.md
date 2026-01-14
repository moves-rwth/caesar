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

## Peer-Reviewed Papers

### POPL '26: Verifying Almost-Sure Termination for Randomized Distributed Algorithms

The paper [_"Verifying Almost-Sure Termination for Randomized Distributed Algorithms"_](https://doi.org/10.1145/3776691) was presented at the [POPL 2026](https://popl26.sigplan.org/).
The authors are Constantin Enea (LIX, CNRS, Ecole Polytechnique), Rupak Majumdar (MPI-SWS), Harshit Jitendra Motwani (MPI-SWS), V.R. Sathiyanarayana (MPI-SWS).

The paper presents a verification technique for liveness properties of randomized distributed algorithms.
It introduces a proof rule for fair almost-sure termination of distributed systems, combining martingale-based arguments for probabilistic termination with reasoning about weak fairness.
The proof rules are implemented in Caesar and were used to verify termination of randomized asynchronous consensus protocols, including Ben-Or’s protocol and graded binary consensus, under both crash and Byzantine faults.

See also [our blog post for more details](/blog/2026/01/15/popl26-ast-distributed).

### ESOP '26: Error Localization, Certificates, and Hints for Probabilistic Program Verification via Slicing

The paper [_"Error Localization, Certificates, and Hints for Probabilistic Program Verification via Slicing"_](https://arxiv.org/abs/2512.20214) by Philipp Schröer, Darion Haase, and Joost-Pieter Katoen was accepted at the [ESOP 2026](https://etaps.org/2026/conferences/esop/) to be held in Turin, Italy.

An **extended version with proofs and additional material** is available on arXiv: [Error Localization, Certificates, and Hints for Probabilistic Program Verification via Slicing (Extended Version) — arXiv:2512.20214](https://arxiv.org/abs/2512.20214).

The paper presents theoretical foundations and the implementation of our slicing-based user diagnostics in Caesar, dubbed *Brutus*, and introduces different kinds of slices: error-witnessing (for error localization), verification-witnessing (for proof simplification), and verification-preserving (to maintain successful verification results).

See also:
 * [Talk about the ESOP '26 paper at Dafny 2026](/blog/2026/01/11/dafny26-slicing),
 * [Blog post about the ESOP '26 paper](/blog/2025/12/23/esop26-slicing),
 * [User guide-level documentation on slicing in Caesar](/docs/caesar/slicing),
 * [Announcement of Caesar 2.0](/blog/2024/05/20/caesar-2-0), which introduced the first slicing implementation in Caesar.

### OOPSLA '25: Foundations for Deductive Verification of Continuous Probabilistic Programs

The paper [_"Foundations for Deductive Verification of Continuous Probabilistic Programs: From Lebesgue to Riemann and Back"_](https://dl.acm.org/doi/10.1145/3720429) by Kevin Batz, Joost-Pieter Katoen, Francesca Randone, and Tobias Winkler was recently published at [OOPSLA 2025](https://2025.splashcon.org/track/OOPSLA). DOI: https://doi.org/10.1145/3720429.

This paper lays out the formal foundations for us to verify probabilistic programs that sample from continuous distributions, with support for loops, and conditioning.
One challenge is to integrate the integrals for the expected values that arise from continuous distributions into the deductive verification framework of Caesar.
The key idea is to soundly under- or over-approximate these integrals via [Riemann sums](https://en.wikipedia.org/wiki/Riemann_sum).
In addition to theoretical results such as convergence and completeness of the approach, the paper also provides case studies of continuous probabilistic programs that are encoded in HeyVL and verified with Caesar.

[See our blog post for more details and examples](/blog/2025/04/11/foundations-continuous).

### AISoLA '24: A Game-Based Semantics for the Probabilistic Intermediate Verification Language HeyVL

The publication [_"A Game-Based Semantics for the Probabilistic
Intermediate Verification Language HeyVL"_](https://doi.org/10.1007/978-3-031-75434-0_17) by Christoph Matheja was published at [AISoLA 2024](https://2024-isola.isola-conference.org/). DOI: https://doi.org/10.1007/978-3-031-75434-0_17.

Quoting from its abstract:

> [T]he original language [HeyVL] lacked a formal “ground truth” in terms of a small-step operational semantics that enables an intuitive reading of HeyVL programs.
>
> In this paper, we define an operational semantics for a cleaned-up version of HeyVL in terms of *refereed* stochastic games, a novel extension of simple stochastic games in which a referee may perform quantitative reasoning about the expected outcome of sub-games and give one player an advantage if those sub-game are outside of certain boundaries.

This new operational semantics is aimed at improved intuition and ergonomics of HeyVL, as well as a possible future work enabling other verification backends such as ones based on probabilistic model checking tools.

### OOPSLA '23: A Deductive Verification Infrastructure for Probabilistic Programs {#oopsla-23}

HeyVL and Caesar were first published at [OOPSLA '23](https://2023.splashcon.org/track/splash-2023-oopsla): [A Deductive Verification Infrastructure for Probabilistic Programs](https://doi.org/10.1145/3622870) by Schröer et al.
This paper introduces HeyLo and HeyVL with formal semantics, and explains how different proof rule encodings work.

For publication, please cite as follows ([BibTeX file](https://dblp.org/rec/journals/pacmpl/SchroerBKKM23.html?view=bibtex)):

> Philipp Schröer, Kevin Batz, Benjamin Lucien Kaminski, Joost-Pieter Katoen, Christoph Matheja. *A Deductive Verification Infrastructure for Probabilistic Programs.* Proceedings of the ACM on Programming Languages 7, OOPSLA 2023. DOI: https://doi.org/10.1145/3622870.

An **extended version with proofs, details on encodings, and typo fixes** is available on arXiv: [A Deductive Verification Infrastructure for Probabilistic Programs (Extended Version) — arXiv:2309.07781](https://arxiv.org/abs/2309.07781).

**The artifact** for our OOPSLA '23 publication is [available on Zenodo](https://zenodo.org/record/8146987).
[It has received the *Distinguished Artifact* award](/blog/2023/10/27/oopsla23-distinguished-artifact), praising exceptionally high quality of the artifact.

A video of the OOPSLA '23 presentation is available on YouTube:
<iframe width="560" height="315" src="https://www.youtube-nocookie.com/embed/2cHo4HsuYJY?si=nwJQqrsEMIVdGhSS" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share" referrerpolicy="strict-origin-when-cross-origin" allowfullscreen></iframe>

<br />
<br />

We also presented this paper at the [Dafny 2024 workshop](/blog/2024/01/14/dafny-2024-talk), see the video below:

<iframe width="560" height="315" src="https://www.youtube-nocookie.com/embed/riDqWQlAk84?si=Wh4bZT9OyFMzJdYs" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share" referrerpolicy="strict-origin-when-cross-origin" allowfullscreen></iframe>

The talk slides are [available in PDF format](pathname:///assets/talks/dafny2024.pdf).

## Bachelor and Master Theses

Below are some selected theses that contributed to the development of Caesar and HeyVL.

### Master Thesis '25: Effective Quantifier-based Reasoning for Quantitative Deductive Verification

[_"Effective quantifier-based reasoning for quantitative deductive verification"_](https://publications.rwth-aachen.de/record/1016969) is a Master thesis written by Emil Beothy-Elo at RWTH Aachen University.
This thesis investigates different encodings of user-defined recursive functions as limited functions to avoid matching loops in the context of Caesar.
It provides formal definitions and soundness proofs for several encodings used by other verifiers, and examines how one of the encodings can be modified to obtain finite and constructible counterexamples involving recursive functions.
The results of this thesis [have been implemented in Caesar](./caesar/debugging.md#function-encodings-and-limited-functions) (as of [Caesar 3.0.0](/blog/2025/07/29/caesar-3-0)).

[The PDF file is available online](https://publications.rwth-aachen.de/record/1016969/files/1016969.pdf).

<details>
<summary>Abstract</summary>

Caesar is a deductive verifier for probabilistic programs. It builds on modern SMT solvers to automatically check if probabilistic programs conform to their specification. This high degree of automation sometimes comes at the cost of brittle verification. Seemingly unrelated changes in the input program can cause the verifier to hang and verification to fail. These instabilities are often caused by quantifiers that are used in axioms to describe the relevant theories for verification. A common problem here are matching loops - an ill-behaved set of quantifiers that can cause an infinite number of quantifier instantiations by themselves. A large contributor of matching loops are user-defined recursive functions. A common approach taken by other verifiers is to encode such functions as limited functions, limiting the number of recursive instantiations and avoiding matching loops by construction. While they have been proven to be effective, there is little information available about them and they lacked a formal treatment. We present and formally define different limited function encodings used by other verifiers, and subsequently prove that these transformations are sound. Furthermore, we examine how one of the encodings can be modified to obtain finite and constructible counterexamples involving recursive functions. The presented encodings are implemented in Caesar. We provide guidance on the subtleties that are required for the encodings to work well in practice. Our evaluation shows that the implemented encodings are very effective in eliminating brittleness for problematic programs in Caesar's test suite.
</details>

### Master Thesis '25: Practical Probabilistic Program Verification using Caesar

[_"Practical Probabilistic Program Verification using Caesar"_](https://purl.utwente.nl/essays/106318) is a Master thesis by Franka van Jaarsveld written at the University of Twente.
It uses the *Bounded Retransmission Protocol* (BRP) as a case study to explore the practical verification of probabilistic programs using Caesar and gives insights into the strengths and limitations of Caesar in practice.

The PDF file is available via the [UT Student Theses website](https://purl.utwente.nl/essays/106318).

<details>
<summary>Abstract</summary>

This thesis explores the practical verification of probabilistic programs using Caesar, a weakest preexpectation-based verification tool for reasoning about the expected behaviour of discrete probabilistic programs. The Bounded Retransmission Protocol (BRP) is studied as a case study. A key contribution of this work is the abstraction and decomposition of BRP into two geometric-like programs, enabling more effective reasoning about the protocol's behaviour and facilitating the stepwise verification strategy. Theoretical verification of key properties (positive almost-sure termination, success probability, and the expectation of the number of failed and sent transmissions) was largely successful using weakest preexpectation calculus. Translating these results into verification using Caesar introduced practical challenges, particularly in invariant discovery. Additionally, even valid invariants did not always lead to successful verification due to limitations in Caesar’s current implementation, particularly in SMT solver performance and the handling of exponentials. However, through workarounds including alternative invariants and a 'fueled' exponential function, meaningful properties of BRP were verified. This thesis demonstrates how such techniques support practical verification in Caesar and concludes with a discussion of its strengths, limitations, and recommendations for effective use.
</details>

### Master Thesis '22: A Deductive Verifier for Probabilistic Programs

Caesar is based on a 2022 Master thesis by Philipp Schroer entitled [_"A Deductive Verifier for Probabilistic Programs"_](https://publications.rwth-aachen.de/record/998370).
This thesis contains the foundations for Caesar, HeyVL, and HeyLo, including encodings for Park induction, k-induction, and bounded model checking.
It also discusses the implementation of Caesar with its prenexing-based quantifier elimination and presents early experimental results.

The [PDF file is available online](https://publications.rwth-aachen.de/record/998370/files/998370.pdf).

<details>
<summary>Abstract</summary>

We design and implement a deductive verification infrastructure for probabilistic programs. It consists of a quantitative intermediate verification language (HeyVL) and a quantitative assertion language (HeyLo). HeyLo is a syntax to express expected values of probabilistic programs, with support for quantitative implications based on Gödel logic. Both HeyLo and HeyVL contain lattice-theoretic dual constructs to reason about lower and upper bounds of expected values. As a case study, we encode weakest pre-expectation and weakest liberal pre-expectation reasoning about the probabilistic programming language pGCL into HeyVL. For loops, we provide encodings of Park induction, k-induction, and bounded model checking. Park induction and k-induction are both proof rules that require on user-provided invariant candidates. Furthermore, we discuss the automation of our deductive verification infrastructure. Our implementation Caesar takes a HeyVL program as input, generates and optimizes verification conditions in the form of HeyLo formulas and uses the automated theorem prover Z3 to prove or disprove validity of the verification conditions. In this thesis, we focus on the central optimization of quantifier elimination of HeyLo formulas. We present early promising experimental results. Finally, we discuss the abstraction of our framework based on Heyting and Gödel algebras to support more domains than expectations.
</details>

Compared to the [OOPSLA '23 paper](#oopsla-23):
 * The thesis includes a large section on quantifier elimination (by prenexing) for the logic, which is omitted in the paper for brevity.
 * The thesis provides a more exploratory view on the logic, with e.g. a *"relational view"* on the semantics.
 * The thesis still uses negation statements, whereas the paper switches to `validate` statements to encode comparisons.
   * `validate` statements have monotonic semantics (in contrast to negation statements), which is easier to work with in general.

Citations:
* DOI: https://doi.org/10.18154/RWTH-2024-11340.
* BibTeX: https://publications.rwth-aachen.de/record/998370/export/hx?ln=en

## Related Work and Further Reading

For more background on the weakest pre-expectation-based approach to reasoning about probabilistic programs, we recommend the following publications:
 * [_"Advanced weakest precondition calculi for probabilistic programs"_](https://publications.rwth-aachen.de/record/755408/). PhD thesis by Benjamin Lucien Kaminski (RWTH Aachen University, 2019). [PDF file is available online](https://publications.rwth-aachen.de/record/755408/files/755408.pdf).
 * [_"Automated deductive verification of probabilistic programs"_](https://publications.rwth-aachen.de/record/1002329/). PhD thesis by Kevin Batz (RWTH Aachen University, 2024). [PDF file is available online](https://publications.rwth-aachen.de/record/1002329/files/1002329.pdf).

Caesar uses SMT solvers as backends.
For more information on SMT solving, we recommend:
 * [_"Satisfiability Modulo Theories: A Beginner’s Tutorial"_](https://doi.org/10.1007/978-3-031-71177-0_31) by Barrett et al. (2024).

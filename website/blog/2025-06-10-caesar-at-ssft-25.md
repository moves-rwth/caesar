---
authors: phisch
tags: [talks]
---

# Caesar at Summer School for Formal Techniques '25

We had the pleasure to present Caesar at the 14th [Summer School for Formal Techniques](https://ssft-sri.github.io/) at Menlo College in Menlo Park, California, organized by the [SRI Formal Methods Group](https://www.csl.sri.com/programs/formalmethods/).
It took place from May 24th to May 30th.

[Joost-Pieter Katoen](https://moves.rwth-aachen.de/people/katoen/) gave two lectures on the theoretical foundations of probabilistic programming and their verification, and together we hosted two accompanying lab sessions where students could try out Caesar and HeyVL.

Here is the lecture abstract:

> Probabilistic programs encode randomized algorithms, robot controllers, learning components, security mechanisms, and much more. They are however hard to grasp. Not only by humans, also by computers: checking elementary properties related to e.g., termination are "more undecidable" than for ordinary programs. The analysis of probabilistic programs requires manipulating irrational or even transcendental numbers.
>
> Although this all sounds like a no-go for (semi-)automated analysis, I will present a deductive verification technique to analyse probabilistic programs. In contrast to simulation (like MCMC), this analysis yields exact results. Our technique is based on weakest precondition reasoning. We will explain the foundations of this approach, present some proof rules to reason about probabilistic while-loops, and discuss how the analysis can be automated &mdash; either fully or with the help of invariants.

The [material is available online](./2025-06-10-caesar-at-ssft-25.md#materials).

<!-- truncate -->

## Materials

The slides and exercise sheets for the lectures and labs are available online:
 * [Lecture Slides: Deductive Verification of Probabilistic Programs](pathname:///assets/ssft25/SSFT25-lectures.pdf)
 * [Exercises for the two lab sessions](pathname:///assets/ssft25/SSFT25-labs.pdf)
   * Solutions are available on request (email us at phisch@cs.rwth-aachen.de).

[Video recordings are also available online](https://ssft-sri.github.io/materials/zoom.txt).

Further recommended materials were:
 * [Foundations of Probabilistic Programming Ch. 6: Expected Runtime Analysis by Program Verification](https://doi.org/10.1017/9781108770750.007)
 * Annabelle McIver, Carroll Morgan, Benjamin Lucien Kaminski, Joost-Pieter Katoen: [A new proof rule for almost-sure termination](https://doi.org/10.1145/3158121). Proc. ACM Program. Lang. 2(POPL): 33:1-33:28 (2018)
 * Joost-Pieter Katoen, Friedrich Gretz, Nils Jansen, Benjamin Lucien Kaminski, Federico Olmedo: [Understanding Probabilistic Programs](https://doi.org/10.1007/978-3-319-23506-6_4). Correct System Design 2015: 15-32
 * Joost-Pieter Katoen: [Deductive Verification of Probabilistic Programs: From Theory to Automation](https://www.youtube.com/watch?v=I3sOp_mbs8k). Tutorial at ETAPS 2023.

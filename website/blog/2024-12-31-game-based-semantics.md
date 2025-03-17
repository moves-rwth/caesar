---
authors: phisch
tags: [publications]
---

# A Game-Based Operational Semantics for HeyVL

The paper [_"A Game-Based Semantics for the Probabilistic
Intermediate Verification Language HeyVL"_](https://doi.org/10.1007/978-3-031-75434-0_17) by Christoph Matheja was published at [AISoLA 2024](https://2024-isola.isola-conference.org/) and is now available online.

<!-- truncate -->

Quoting from its abstract:

> [T]he original language [HeyVL] lacked a formal “ground truth” in terms of a small-step operational semantics that enables an intuitive reading of HeyVL programs.
>
> In this paper, we define an operational semantics for a cleaned-up version of HeyVL in terms of *refereed* stochastic games, a novel extension of simple stochastic games in which a referee may perform quantitative reasoning about the expected outcome of sub-games and give one player an advantage if those sub-game are outside of certain boundaries.

This new operational semantics is aimed at improved intuition and ergonomics of HeyVL, as well as a possible future work enabling other verification backends such as ones based on probabilistic model checking tools.

Note that the existing [model checking backend](/docs/model-checking) of Caesar does not yet support for the full extent of the HeyVL language, but merely an "executable subset".
Therefore, this publication shows an avenue for a future extension of this existing backend via refereed stochastic games.

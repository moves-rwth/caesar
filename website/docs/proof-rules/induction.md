---
description: Induction and k-Induction are proof rules for while loops.
sidebar_position: 1
---

# Induction and k-Induction

TLDR: Probabilistic induction generalizes the well-known [proof rule for loops from Hoare logic](https://en.wikipedia.org/wiki/Hoare_logic#While_rule).

_Induction_ and the more general _k-Induction_ are built-in proof rules to reason about `while` loops.
The non-probabilistic intuitions go as follows: induction requires an _invariant_ that is maintained by each loop iteration.
It must hold before the loop, and then we are guaranteed that the invariant holds after the loop.
_k_-induction allows us to reason about multiple loop iterations: the invariant is not required to be re-established after just one loop iteration, but may be re-established after `1`, `2`, ..., up to `k` loop iterations.

HeyVL supports the lattice-theoretic generalizations of these rules.
See [_Latticed k-Induction with an Application to Probabilistic Programs_](https://link.springer.com/chapter/10.1007/978-3-030-81688-9_25) (CAV 2021) for more information on the theory.
Caesar will use the formulation from that paper only for upper-bounds reasoning (`coproc`s) because it is associated with least fixed-point reasoning that the paper also deals with.
For lower-bounds reasoning (`proc`s), Caesar will use a dual encoding that is sound with respect to greatest fixed-point semantics.
Formal details are provided in Appendix C of the [extended version of our OOPSLA '23 paper](https://arxiv.org/abs/2309.07781).

## Usage

To use _induction_, simply add an `@invariant(I)` annotation to your loop with a probabilistic invariant `I`.
In this case, it is `ite(cont, c + 1, c)`.
```heyvl
coproc geo1_induction(init_c: UInt) -> (c: UInt)
    pre init_c + 1
    post c
{
    c = init_c
    var cont: Bool = true
    @invariant(ite(cont, c + 1, c))
    while (cont) {
        var prob_choice: Bool = flip(0.5)
        if prob_choice { cont = false } else { c = c + 1 }
    }
}
```

To use _k-induction_, you can use the `@k_induction(k, I)` annotation on a loop.
It takes two parameters: The number literal `k` specifies the number of unrollings are to be done and `I` is the invariant.
```heyvl
coproc geo1_2induction(init_c: UInt) -> (c: UInt)
    pre init_c + 1
    post c
{
    c = init_c
    var cont: Bool = true
    @k_induction(2, c + 1)
    while cont {
        var prob_choice: Bool = flip(0.5)
        if prob_choice { cont = false } else { c = c + 1 }
    }
}
```
This program will not verify if `k` is set to `1` because the invariant `c + 1` is not 1-inductive.

## Soundness

Using these proof rules is always *sound* in the following way: Both annotations will always *under-approximate greatest fixed-point* semantics when used in lower-bound contexts (`proc`) and *over-approximate  least fixed-point* loop semantics when used in upper-bound contexts (`coproc`).

If the invariants are not *inductive* in some initial state, i.e. are not maintained by the loop iteration(s), then the encodings will evaluate to `0` or `\infty` (`proc` and `coproc`, respectively) for that initial state.

Again, formal details are provided in Appendix C of the [extended version of our OOPSLA '23 paper](https://arxiv.org/abs/2309.07781).

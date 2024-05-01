---
title: Loop Unrolling
description: Loop unrolling, also known as bounded model checking.
sidebar_position: 3
---

# Loop Unrolling and Bounded Model Checking

*Loop unrolling* (also known as *fixpoint iteration* or *Kleene iteration*) replaces a `while` loop by a fixed number of iterations `k` and a *terminator* expectation to be used if more than `k` iterations run.
This simple proof rule does not require invariants, just a choice of how many loop iterations to be done.
The necessary terminator is usually clear from the context.

Just like all others of Caesar's proof rules, loop unrolling can be used as a proof rule for verification.
But it also often used in *bounded model checking* not to *prove*, but to *refute* specifications.
See the [*Bounded Model Checking* section](#bounded-model-checking) below for details.

## Usage

A `while` loop is annotated by the `@unroll(k, terminator)` annotation where `k` is a number literal and `terminator` is an expression of type `EUReal`.

The `terminator` should be the initial value of the fixpoint iteration.
Thus, one chooses the `terminator` to encode the loop unrolling such that it either
 * over-approximates greatest fixed-point semantics:
    * commonly `1` for the one-bounded wlp semantics,
    * or `\infty` for the unbounded expectation-based semantics.
 * under-approximates least fixed-point semantics:
    * commonly `0` for expectation-based semantics (wp, ert).

See the [section on soundness](#soundness) below.

## Verification Example

In the simple example below, we show a lower bound of `0.75` on the probability value of termination in at most 3 iterations of the loop.
We want to encode a loop with least fixed-point semantics, so we use `0` as our `terminator`.

```heyvl
@wp proc geo1_unroll() -> (c: UInt)
    pre 0.75
    post 1
{
    c = 0
    var cont: Bool = true
    @unroll(3, 0) // k = 3, terminator = 0
    while cont {
        var prob_choice: Bool = flip(0.5)
        if prob_choice { cont = false } else { c = c + 1 }
    }
}
```

The [`@wp` annotation](./calculi.md) annotation adds a sanity check from Caesar that we correctly reason about *weakest pre-expectations*.

Internally, the loop is replaced by its unfolding, with a `assert 0; assume 0` at the end of the `k = 3` loop iterations.

```heyvl
if cont {
    ... body ...
    if cont {
        ... body ...
        if cont {
            ... body ...
            assert 0; assume 0 // terminator = 0
        }
    }
}
```

There is a `0.25` chance of reaching the `assert 0`, so we can at most prove a lower bound of `0.75` with `k = 3`.

Notice that `k = 3` generates three `if cont { ... }` statements, but that the last body has essentially constant zero semantics due to the `assert 0` at the end.
So we get probability mass from the first *two* iterations only (`0.5 + 0.25`).

## Refutation (Bounded Model Checking) {#bounded-model-checking}

*Bounded model checking* (BMC) is what we usually call using loop unrolling when we *refute* a specification with it.
The idea is that if a specification does not hold e.g. for 12 loop steps, then we can guarantee that it still will not hold for more potential loop steps.

:::danger

Bounded model checking is a technique for refuting verification (if there is a counter-example, it is valid for the original program) but can make successful verification unsound (if the program verifies, we know nothing).

:::

In the following example, we use loop unrolling to *under-approximate* least fixed-point semantics in an *upper-bound context* (`coproc`).
Because we want to approximate least fixpoint semantics, we use `0` as our `terminator`.

Because loop unrolling *under-approximates* the least fixed-point, we know that if verification of an *upper bound fails*, then we have refuted the upper bound.
On the other hand, if verification succeeds, we cannot conclude that the specification holds.

```heyvl
coproc geo1_bmc(init_c: UInt) -> (c: UInt)
    pre init_c + 0.99
    post c
{
    c = init_c
    var cont: Bool = true
    @unroll(12, 0) // k = 12, terminator = 0
    while cont {
        var prob_choice: Bool = flip(0.5)
        if prob_choice { cont = false } else { c = c + 1 }
    }
}
```

Trying to verify `geo1_unroll` will yield a counter-example to verification.
Because this is loop unrolling, it is a *true counter-example* to `init_c + 0.99` being an upper bound.
On the other hand, if you change `k = 11`, then the program verifies.
But this tells you nothing about the actual program semantics.

:::caution

Remember that correctness of encoding BMC here depends on the fact that we encoded a sound under-approximation on a least fixpoint in a `coproc`.
If you over-approximate in this program, e.g. using additional `coassert` statements or `coproc` calls, then you might get spurious counterexamples again.
Then BMC would be useless!

:::

:::info

The `@unroll` annotation only provides a sound under-approximation for the `wp` and `ert` calculi and only a sound over-approximation for `wlp` (cf. [calculus annotations](./calculi.md)).
The calculus annotations check *soundness* in the limited sense that verification implies that the specification holds for the original program.
Therefore, the calculus annotations would *not allow* the above combination of `coproc` with the `@wp` annotation.

However, here it is still correct to *under-approximate* the `wp` and then conclude from a counter-example of an *upper bound* (`coproc`) that the upper bound is not valid for the original program!
But calculus annotations do not support the task of checking for sound *refutations* yet.

:::

## Soundness

See [_Latticed k-Induction with an Application to Probabilistic Programs_](https://link.springer.com/chapter/10.1007/978-3-030-81688-9_25) (CAV 2021) for more information on the theory of *bounded model checking* on probabilistic programs.

One needs to be very careful in choosing the `terminator` such that `@unroll` actually approximates the correct fixed-point corresponding to the desired semantics (see [Usage](#usage)).

Notice that you **cannot** *under-approximate a greatest fixed-point semantics* or *over-approximate a least fixed-point semantics* with loop unrolling, in contrast to the other proof rules such as [induction](./induction.md).

---
title: Loop Unrolling
description: Loop unrolling and bounded model checking.
sidebar_position: 3
---

# Loop Unrolling and Bounded Model Checking

*Loop unrolling* replaces a `while` loop by a fixed number of iterations `k` and a `terminator` expectation to be used if more than `k` iterations run.
For example, it *under-approximates* least fixed-point semantics (`wp` and `ert`, `k = 0`):
$$
    \mathrm{vc}\llbracket \texttt{@unroll(k, 0) while G \{ B \}} \rrbracket \sqsubseteq \mathrm{wp}\llbracket \texttt{while G \{ B \}} \rrbracket
$$
This simple proof rule does not require invariants, just a choice of how many loop iterations to be done.

There are three main applications of loop unrolling:
1. [**Approximating loop semantics**](#approximation): Approximating the expected value of loops to gain insight into the unbounded semantics.
2. [**Verification**](#verification): Proving specifications of loops.
3. [**Refutation**](#bounded-model-checking): Refuting specifications of loops. This is often called *bounded model checking*.

Read the [*Soundness* section](#soundness) for details on the soundness of the proof rule.

:::note Relation to Probabilistic Model Checking (Bounded)

[Caesar supports using *probabilistic model checking*](../model-checking.md) to compute and verify expected values of probabilistic programs.
For probabilistic model checking, one would bound the *number of explored states* as opposed to the *number of loop iterations* like is done here.
Both techniques are related, but [we explain the difference between applying the two techniques in more detail here](../model-checking.md#relation-to-caesars-unrolling-proof-rule).

:::

## Usage

A `while` loop is annotated by the `@unroll(k, terminator)` annotation where `k` is a number literal and `terminator` is an expression of type `EUReal`.

The `terminator` expression must correspond to the initial value of the fixed-point iteration semantics of the loop.
By [Kleene's fixed-point theorem](https://en.wikipedia.org/wiki/Kleene_fixed-point_theorem), one should use the following values for `terminator`:
 * For *greatest fixed-point semantics* (`wlp`), one chooses the *top* element of the lattice:
    * `1` for the one-bounded wlp semantics,
    * or `\infty` for the unbounded expectation-based semantics.
 * For *least fixed-point semantics* (`wp`, `ert`), one chooses the *bottom* element of the lattice:
    * `0` for expectation-based semantics (wp, ert).

## Approximating Loop Semantics {#approximation}

Loop unrolling can be used to *approximate* expected value semantics of a loop to gain insight into the actual semantics.

The idea is to have Caesar to *calculate* the expected value of the loop after a fixed number of iterations.
As the unrolling approaches the true semantics as `k` increases, we can use this to e.g. guess the expected value after an unbounded number of iterations.
This might help to find e.g. an [inductive invariant](./induction.md) for the loop.
In contrast to the applications of [verification](#verification) and [refutation](#bounded-model-checking), unrolling for approximations does not require a `pre`, but just a `post` expectation.

Consider this simple geometric loop example.
We want to encode a loop with `wp` semantics, so we use `0` as our `terminator`.

```heyvl
@wp proc geo1_unroll() -> (c: UInt)
    pre \infty
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

By using `pre \infty`, we ensure that Caesar will print a counter-example for (non-infinite) values of the pre.
Caesar will show a counter-example with an evaluation ("the pre-quantity evaluated to:") when we run it.
We can evaluate different values for `k` to see how the expected value of `c` changes after more iterations.
 * For `k = 0`, the expected value is `0`.
 * For `k = 1`, the expected value is `0`.
 * For `k = 2`, the expected value is `0.5`.
 * For `k = 3`, the expected value is `0.75`.
 * For `k = 4`, the expected value is `0.875`.

This sequence is a consequence of the definition of the fixed-point semantics and the corresponding fixed-point iteration.
We can guess (and it is true) that the expected value will eventually converge to `1` as `k` approaches infinity.

## Verification with Loop Unrolling {#verification}

Loop unrolling can be used to *prove* specifications of loops.
We modified the above example to show a *lower bound* of `0.75` on the probability value of termination in at most 3 unrollings of the loop.

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

For *verification*, the following combinations are sound.
More details can be found in the [*Soundness* section](#soundness).
  * For `wlp`, use `@unroll(k, 1)` in a `coproc` to verify upper bounds on the greatest fixed-point semantics.
  * For `wp` and `ert`, use `@unroll(k, 0)` in a `proc` to verify lower bounds on the least fixed-point semantics.

A *counter-example* from Caesar to verification will only be a counter-example for the $k$-unrolled program, but not for the original program.

:::tip

Use the [calculus annotations](./calculi.md) `@wp`, `@wlp`, `@ert` to have Caesar check you apply the `unroll` proof correctly to *verify* a specification.

:::

## Refutation (Bounded Model Checking) {#bounded-model-checking}

Loop unrolling is often used to *refute* specifications as well.
This is done because it is a simple way to *unroll* a loop and then check the specification can be refuted already after a fixed number of iterations.
This is in contrast to e.g. the [induction proof rule](./induction.md), which requires an inductive invariant to be specified to refute specifications properly.
When used for refutations, this technique is often called *bounded model checking* (BMC).

In the following example, we use loop unrolling to refute an upper bound (`coproc`) of *least fixed-point semantics* (`wp`).
Because we want to approximate least fixpoint semantics, we use `0` as our `terminator` (c.f. [*Usage*](#usage)).

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
It is a *true counter-example* to `init_c + 0.99` being an upper bound for the original program.

The following combinations are sound for *refutations*.
More details can be found in the [*Soundness* section](#soundness).
 * For `wlp`, use `@unroll(k, 1)` in a `proc` to refute a lower bound on the greatest fixed-point semantics.
 * For `wp`, use `@unroll(k, 0)` in a `coproc` to refute an upper bound on the least fixed-point semantics.

If the program *verifies* in the above cases, we do not know whether the specification holds for the original semantics.
For example, the example program above verifies if you change `k = 11`; however this gives you no guarantee that the original program `geo1_unroll` satisfies the specification.

:::info

At the moment, the [calculus annotations](./calculi.md) `@wlp`, `@wp`, `@ert` do not support the use of `@unroll` for refutations.
They currently require soundness for verification only, therefore they currently can not be used to check the soundness of a refutation.

:::


## Soundness

By Kleene's fixed-point theorem, the following soundness conditions hold:

 * $\mathrm{vc}\llbracket \texttt{@unroll(k, 1) while G \{ B \}} \rrbracket \sqsupseteq \mathrm{wlp}\llbracket \texttt{while G \{ B \}} \rrbracket$
 * $\mathrm{vc}\llbracket \texttt{@unroll(k, 0) while G \{ B \}} \rrbracket \sqsubseteq \mathrm{wp}\llbracket \texttt{while G \{ B \}} \rrbracket$
 * $\mathrm{vc}\llbracket \texttt{@unroll(k, 0) while G \{ B \}} \rrbracket \sqsubseteq \mathrm{ert}\llbracket \texttt{while G \{ B \}} \rrbracket$

For [the application of verification](#verification), this means:
 * `proc` verifies using `@unroll(k, 1)` $\implies$ specification also holds for the original `wlp` semantics.
 * `coproc` verifies using `@unroll(k, 0)` $\implies$ specification also holds for the original `wp` semantics.
 * `coproc` verifies using `@unroll(k, 0)` $\implies$ specification also holds for the original `ert` semantics.

For [the application of refutation (bounded model checking)](#bounded-model-checking), this means:
 * `coproc` refutes using `@unroll(k, 1)` $\implies$ specification does not hold for the original `wlp` semantics.
 * `proc` refutes using `@unroll(k, 0)` $\implies$ specification does not hold for the original `wp` semantics.
 * `proc` refutes using `@unroll(k, 0)` $\implies$ specification does not hold for the original `ert` semantics.

## Semantics

An annotated loop `@unroll(k, terminator) while G { B }`, is replaced its $k$-step unfolding.
Below, we show `k = 3` unfoldings.
The `terminator` is encoded by a `assert 0; assume 0` at the end of the `k = 3` loop iterations.

```heyvl
if cont {
    ... body ...
    if cont {
        ... body ...
        if cont {
            ... body ...
            assert 0; assume 0 // terminator = 0
        } else {}
    } else {}
} else {}
```

In terms of expectation transformer semantics ($\mathrm{vc}$) with respect to postexpectation $f$, the proof rule corresponds to the $k$-times application of the loop-characteristic function applied to the `terminator` $0$, $\Phi_f^k(0)$:
$$
    \mathrm{vc}\llbracket \texttt{@unroll(k, 0) while G \{ B \}} \rrbracket \quad=\quad \Phi_f^k(0)
$$

## Completeness

Loop unrolling is *not compelete* for *proving* specifications.
This is because there are programs for which the actual semantics of the loop is not captured by the unrolling.
A simple example is a loop that counts down a counter variable `c` in each iteration.
Any unrolling of size `k` will not capture the semantics of the loop if `c` is larger than `k`.

However, loop unrolling is *complete* for *refuting* specifications when the semantics is *continuous*.
This is the case for the `wlp`, `wp`, and `ert` semantics.
Then, any *wrong* bound on the pre can be refuted by *some* value of `k`.[^bmc-completeness]

[^bmc-completeness]: See [_Latticed k-Induction with an Application to Probabilistic Programs_](https://link.springer.com/chapter/10.1007/978-3-030-81688-9_25) (CAV 2021) for more information on the theory of *bounded model checking* on probabilistic programs.

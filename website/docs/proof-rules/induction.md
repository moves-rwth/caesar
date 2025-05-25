---
description: Induction and k-Induction are proof rules for while loops.
sidebar_position: 2
---

# Induction and k-Induction

_Induction_ and the more general _$k$-induction_ are built-in proof rules to reason about `while` loops.
The *non-probabilistic* intuition goes as follows: induction requires an _invariant_ that is maintained by each loop iteration.
The invariant must hold before the loop, and then we are guaranteed that the invariant holds after the loop.
The rule corresponds to the well-known [proof rule for loops from Hoare logic](https://en.wikipedia.org/wiki/Hoare_logic#While_rule).

Generalized to *probabilistic* `wlp` semantics, induction allows us to prove a lower bound on the `wlp`-semantics of a loop.
$I$ must be an expression whose expected value does not decrease with each loop iteration.
Formally:
$$
    I \sqsubseteq [G] \cdot \mathrm{wlp}\llbracket Body \rrbracket(I) + [\neg G] \cdot f \quad\text{implies}\quad I \sqsubseteq \mathrm{wlp}\llbracket \texttt{while G \{ Body \}} \rrbracket(f)
$$
A dual version exists for `wp` and `ert` semantics.

*$k$-induction* is a strictly stronger version of induction.
Refer to the [CAV 2021 paper presenting *latticed k-induction*](https://link.springer.com/chapter/10.1007/978-3-030-81688-9_25) for more details.
It allows us to reason about multiple loop iterations: the invariant is not required to be re-established after just one loop iteration, but may be re-established after $1$, $2$, ..., up to $k$ loop iterations.

## Usage

### Using Induction

To use _induction_, simply add an `@invariant(I)` annotation to your loop with a probabilistic invariant `I`.
In this case, it is `ite(cont, c + 1, c)`.
```heyvl
@wp coproc geo1_induction(init_c: UInt) -> (c: UInt)
    pre init_c + 1
    post c
{
    c = init_c
    var cont: Bool = true
    @invariant(ite(cont, c + 1, c))
    while cont {
        var prob_choice: Bool = flip(0.5)
        if prob_choice { cont = false } else { c = c + 1 }
    }
}
```

In a `coproc`, Caesar will use the *super-invariant* version to prove an upper bound on the least fixed-point semantics of the loop (`wp`, `ert` semantics):
$$
    I \sqsupseteq [G] \cdot \mathrm{wp}\llbracket Body \rrbracket(I) + [\neg G] \cdot f \quad\text{implies}\quad I \sqsupseteq \mathrm{wp}\llbracket \texttt{while G \{ Body \}} \rrbracket(f)
$$

In a `proc`, Caesar will use the *sub-invariant* version to prove a lower bound on the greatest fixed-point semantics of the loop (`wlp` semantics):
$$
    I \sqsubseteq [G] \cdot \mathrm{wlp}\llbracket Body \rrbracket(I) + [\neg G] \cdot f \quad\text{implies}\quad I \sqsubseteq \mathrm{wlp}\llbracket \texttt{while G \{ Body \}} \rrbracket(f)
$$

See the [section on soundness](#soundness) below for more information when it is sound to use induction.
The [section on semantics](#semantics) below explains the precise encoding and behavior also when the invariant is not inductive.

### Using k-Induction

To use _k-induction_, you can use the `@k_induction(k, I)` annotation on a loop.
It takes two parameters: The number literal `k` specifies the number of unrollings are to be done and `I` is the invariant.
```heyvl
@wp coproc geo1_2induction(init_c: UInt) -> (c: UInt)
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

Just like induction, the `@k_induction` annotation will result in a HeyVL encoding of the loop that checks whether the invariant is inductive.
Again, Caesar will encode the *super-invariant* version for upper bounds in a `coproc` and the *sub-invariant* version for lower bounds in a `proc`.
Check the [soundness section](#soundness) and the [semantics section](#semantics) below for more details.

We recommend reading the [*Latticed k-induction* paper](https://link.springer.com/chapter/10.1007/978-3-030-81688-9_25) for more details on the principle of k-induction applied to the verification of probabilistic programs.

## Soundness

:::tip

Use the [calculus annotations](./calculi.md) `@wp`, `@wlp`, `@ert` to have Caesar check that the applied proof rules are sound with respect to the semantics of the chosen calculus.
Then you don't have to worry about this section yourself.

:::

For all loops and all *invariant candidates* $I$, the following holds:
 * In `proc`s: $\mathrm{vc}\llbracket \texttt{@invariant(I) while G \{ B \}} \rrbracket \sqsubseteq \mathrm{wlp}\llbracket \texttt{while G \{ B \}} \rrbracket$ <small>&mdash; (wlp uses greatest fixed-point semantics)</small>,
    * Thus: `proc` verifies using `@invariant(I)` $\implies$ specification also holds for the original `wlp` semantics.
 * In `coproc`s: $\mathrm{vc}\llbracket \texttt{@invariant(I) while G \{ B \}} \rrbracket \sqsupseteq \mathrm{wp}\llbracket \texttt{while G \{ B \}} \rrbracket$ <small>&mdash; (wp uses least fixed-point semantics)</small>,
    * Thus: `coproc` verifies using `@invariant(I)` $\implies$ specification also holds for the original `wlp` semantics.
 * In `coproc`s: $\mathrm{vc}\llbracket \texttt{@invariant(I) while G \{ B \}} \rrbracket \sqsupseteq \mathrm{ert}\llbracket \texttt{while G \{ B \}} \rrbracket$ <small>&mdash; (ert uses least fixed-point semantics)</small>,
    * Thus: `coproc` verifies using `@invariant(I)` $\implies$ specification also holds for the original `ert` semantics.

Stated in terms of fixed points:
 * In `proc`s, `@invariant` *under-approximates* the *greatest fixed-point* loop semantics,
 * In `coproc`s, `@invariant` *over-approximates* the *least fixed-point* loop semantics.

The same statements hold for _k-induction_ (`@k_induction(k, I)`).

## Semantics

Let `@invariant(I) while G { Body }` be a loop with an invariant candidate `I` in a `proc`.
The `@invariant` annotation will result in the following HeyVL encoding of the loop:
```heyvl
assert I            // I must hold before the loop
havoc modified_vars // forget values of all variables modified by the loop
validate
assume I            // assume I holds before each iteration
if G {
    Body
    assert I        // I must hold after the loop body
    assume ?(false) // nothing else to establish but I
} else {}
```

The comments indicate the classical (Boolean) interpretation of the encoding, but of course it works for probabilistic semantics as well.

In effect, the semantics of the `proc` encoding evaluates to the following value in state $\sigma$ w.r.t. post $f$:
$$
    \mathrm{vc}\llbracket \texttt{@invariant(I) while G \{ B \}} \rrbracket(f)(\sigma) =
        \begin{cases}
            I(\sigma) & \text{if } I \text{ is an inductive invariant w.r.t. } f \text{ from } \sigma, \\
            0 & \text{otherwise~.}
        \end{cases}
$$
The check for whether $I$ is inductive corresponds to the part of the encoding above starting with the `assume I` statement.
In terms of `wlp` semantics, this condition is expressed as $I \sqsubseteq [G] \cdot \mathrm{wlp}\llbracket B \rrbracket(I) + [\neg G] \cdot f$.

The two cases:
 1. If the invariant $I$ is inductive in the initial state $\sigma$, then the encoding evaluates to $I(\sigma)$ (the value of the invariant in that state).
 2. If the invariant is *not* inductive, then the encoding evaluates to $0$.

Case 1 is sound by the theorem of Park induction, and case 2 is sound because $0$ is the trivial lower bound on the `wlp`-semantics of a loop.

The cases are dual for upper bound semantics in `coproc`s: If the invariant $I$ is not inductive, then the trivial *upper bound* $0$ is returned.
If the invariant is inductive, $I$ is returned as before.

The encoding is similar for k-induction (`@k_induction`).
It also evaluates to `I` if the invariant is *k-inductive* and to $0$ otherwise.
Refer to the [k-induction paper](https://link.springer.com/chapter/10.1007/978-3-030-81688-9_25) for the precise definition and properties of k-inductive invariants.

More formal details on the HeyVL encodings are provided in the [extended version of our OOPSLA '23 paper](https://arxiv.org/abs/2309.07781), both in the main text and in Appendix C.

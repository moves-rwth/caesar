---
description: Omega-invariants for bounds on loop expectations.
sidebar_position: 4
---

# ω-Invariants

*ω-invariants* ("omega-invariants") are a built-in proof rule for `while` loops.
The idea is to prove bounds on finite loop unfoldings by induction on the number of iterations.

For `wp` semantics, an ω-invariant is a family of expectations $(I_n)_{n\in\mathbb{N}}$ whose supremum lower-bounds the loop expectation.
Formally:

$$
    I_0 \sqsubseteq \Phi_f(0)
    \quad\text{and}\quad
    \forall n\in\mathbb{N}.\ I_{n+1} \sqsubseteq \Phi_f(I_n)
    \quad\text{imply}\quad
    \sup_{n\in\mathbb{N}} I_n \sqsubseteq \mathrm{wp}\llbracket \texttt{while G \{ Body \}} \rrbracket(f).
$$

Here, $\Phi_f(X) = [G] \cdot \mathrm{wp}\llbracket Body \rrbracket(X) + [\neg G] \cdot f$ is the loop's characteristic functional for postexpectation $f$.
The same rule applies to `ert`, and a dual version proves upper bounds for `wlp` semantics.

For more details on the proof rule, see the discussion following [Definition 5.3 of Benjamin Kaminski's PhD thesis](https://publications.rwth-aachen.de/record/755408/files/755408.pdf#page=122).

## Usage

Add `@omega_invariant(n, I)` to a `while` loop, where `I` describes the family $I_n$.
In the following example, each iteration decrements `x` and costs one tick.
The family $I_n = [x\leq n]\cdot x$ proves that the expected runtime is at least the initial value of `x`.

```heyvl
@ert proc omega(init_x: UInt) -> (x: UInt)
    pre init_x
    post 0
{
    x = init_x

    @omega_invariant(n, [x<=n] * x)
    while x > 0 {
        tick 1
        x = x - 1
    }
}
```

**Inputs:**

- `n`: A natural-number index bound only within the invariant expression.
- `I`: An expectation in the program variables and `n` that describes the candidate family.

The index is local to the loop and its annotation.

## Soundness

:::tip

Use the [calculus annotations](./approximations#calculus-annotations) `@wp`, `@wlp`, and `@ert` to select the intended semantics and have Caesar check whether verification or refutation is sound.

:::

For every candidate invariant family, the encoding gives:

- With `@wp` or `@ert`: an under-approximation of the least fixed point, giving sound verification in a `proc`.
- With `@wlp`: an over-approximation of the one-bounded greatest fixed point, giving sound verification in a `coproc`.

Without a calculus annotation, `proc` selects least fixed-point semantics and `coproc` selects unbounded greatest fixed-point semantics, starting at infinity.

## Internal Details

:::warning

The HeyVL encoding of the ω-invariant rule will generate a quantitative quantifier (infimum or supremum) that can not be eliminated by Caesar's quantifier elimination.
It will be naively passed to the SMT solver, which often struggles with it.
Learn more in the [*Debugging* section](../caesar/debugging.md).
Therefore, we generally recommend to avoid the use of ω-invariants in practice.

:::

### HeyVL Encoding

For least fixed-point semantics (`wp` and `ert`), Caesar replaces the annotated loop with the following encoding.
Here, `I(n)` denotes the invariant expression, and `I(0)` and `I(n + 1)` substitute the corresponding value for its index.

```heyvl
assert sup n. I(n)   // evaluate the bound at loop entry
havoc modified_vars // forget variables modified by the loop
if ⊓ {
    // Base case: I_0 <= Phi_f(0)
    validate
    assume I(0)
    if G {
        Body
        assert 0
        assume 0
    } else {}
} else {
    // Induction step: I_{n+1} <= Phi_f(I_n)
    havoc n
    validate
    assume I(n + 1)
    if G {
        Body
        assert I(n)
        assume 0
    } else {}
}
```

The demonic choice `if ⊓` checks both the base case and the induction step.
The `havoc modified_vars` statement makes both checks range over every valuation of the variables modified by the loop.
The additional `havoc n` makes the induction step hold for every index.
The empty `else` branches use the loop's postexpectation $f$.

For `wlp`, the encoding is dual: the entry bound becomes `coassert inf n. I(n)`, the choice is angelic (`if ⊔`), and the remaining statements use `cohavoc`, `covalidate`, `coassume`, and `coassert`.
The base case ends the loop body with `coassert 1; coassume \infty`, and the induction step with `coassert I(n); coassume \infty`.
The one in the base case is the starting expectation for the one-bounded greatest fixed point; the infinity in `coassume` belongs to the HeyVL encoding of a constant expectation.

### Verification Pre-Expectation Semantics

Let $C$ be `@omega_invariant(n, I) while G { Body }`, with postexpectation $f$ and loop-entry state $\sigma$.
Write $H(\sigma)$ for the states that agree with $\sigma$ on every program variable not modified by the loop, as in [local inductive invariants](./induction#local-inductive-invariants).
The checks of the encoding succeed from $\sigma$ if the base case holds in every state in $H(\sigma)$ and the induction step holds in every such state for every $n\in\mathbb{N}$.

For `wp` and `ert`, the encoding's verification pre-expectation is

$$
    \mathrm{vc}\llbracket C \rrbracket(f)(\sigma) =
    \begin{cases}
        \sup_{n\in\mathbb{N}} I_n(\sigma) & \text{if the checks succeed from } \sigma, \\
        0 & \text{otherwise.}
    \end{cases}
$$

For `wlp`, the checks use the dual inequalities described above, and the value is

$$
    \mathrm{vc}\llbracket C \rrbracket(f)(\sigma) =
    \begin{cases}
        \inf_{n\in\mathbb{N}} I_n(\sigma) & \text{if the checks succeed from } \sigma, \\
        \infty & \text{otherwise.}
    \end{cases}
$$

The supremum or infimum ranges over the index `n`, with the program variables fixed to their loop-entry values in $\sigma$.
`covalidate` maps a failed dual check to infinity, the top element of HeyVL's `EUReal` lattice, even for one-bounded `wlp` semantics.

### Local Invariants

As with [local inductive invariants](./induction#local-inductive-invariants), the base case and induction step only need to hold on $H(\sigma)$, rather than all program states.

<details>
<summary>Example: The Advantage of *Local Invariants*</summary>

Consider this termination proof for a countdown loop:

```heyvl
@wp proc countdown(init_p: UInt) -> ()
    pre [init_p == 0]
    post 1
{
    var p: UInt = init_p
    var x: UInt = 1
    @omega_invariant(n, [p > 0 || x <= n])
    while x > 0 {
        x = x - 1
    }
}
```

When `p == 0`, the family reduces to `[x <= n]` and proves termination.
Adding `p = p` to the loop body makes Caesar havoc `p` as well, so the base case fails for `p > 0` and `x > 0`.

</details>

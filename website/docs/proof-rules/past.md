---
sidebar_position: 6
---

# Positive Almost-Sure Termination

_Positive almost-sure termination_ (PAST for short) means that a program [terminates almost-surely](ast) and the expected runtime to termination is finite.
In terms of the [expected runtime calculus](./approximations#calculus-annotations), this means that `ert[C](0) < ∞` holds for a program `C`.

In Caesar, there are several ways to prove PAST:

```mdx-code-block
import TOCInline from '@theme/TOCInline';

<TOCInline toc={toc} maxHeadingLevel="2" />
```

## Upper Bounds on ert

The simplest way to prove positive almost-sure termination is by proving a finite upper bound $g$ on the expected runtime of a program using the expected runtime calculus, i.e. $\mathrm{ert}\llbracket C \rrbracket(0) \leq g$.
The upper bound $g$ must be finite: for every state $s$, $g(s) < \infty$ must hold.

Upper bounds on the expected runtime can be shown with [Park induction](./induction.md).
The ranking-superinvariant rule below can be viewed as a derived way of constructing such an `ert`-superinvariant.

## PAST from Ranking Superinvariants

Caesar supports proofs of PAST using *ranking superinvariants*, also called *ranking supermartingales*.
We use the `wp`-based formulation of [Theorem 6.3 in Benjamin Kaminski's PhD thesis](http://publications.rwth-aachen.de/record/755408/files/755408.pdf#page=143).
Closely related statements also appear as:

- Theorem 4 of [„*Probabilistic Program Analysis with Martingales*“](https://doi.org/10.1007/978-3-642-39799-8_34) by Chakarov and Sankaranarayanan (CAV 2013).
- Theorem 5.6 of [„*Probabilistic Termination: Soundness, Completeness, and Compositionality*“](https://doi.org/10.1145/2775051.2677001) by Fioriti and Hermanns (POPL 2015).

Ranking superinvariants are supported via Caesar's built-in `@past` annotation on `while` loops.

### Formal Theorem

Consider a loop `while G { Body }` whose `Body` is exact.[^exact-body]
The loop's used and modified variables, except the ones declared within the loop, are referred to as `vars`.
Let

- $I$, a function assigning a value $\mathbb{R}_{\geq 0}$ to every state,
- $\epsilon \in \mathbb{R}_{> 0}$,
- $K \in \mathbb{R}_{\geq 0}$,

such that all the following conditions are fulfilled:

1. $I$ is bounded on terminating states: $[\neg G] \cdot I \leq K$,
    <details>
    <summary>HeyVL Encoding</summary>

    ```heyvl
    proc I_bounded_on_exit(vars: ...) -> ()
    {
        assert ?(([!G(vars)] * I(vars)) <= K)
    }
    ```

    </details>
2. $K$ is small enough on states where the loop continues: $[G] \cdot K \leq [G] \cdot I + [\neg G]$,
    <details>
    <summary>HeyVL Encoding</summary>

    ```heyvl
    proc K_bounded_by_I(vars: ...) -> ()
    {
        assert ?(([G(vars)] * K) <= (([G(vars)] * I(vars)) + [!G(vars)]))
    }
    ```

    </details>
3. $I$ decreases in expectation by at least $\epsilon$ in each loop iteration:
    $[G] \cdot \mathrm{wp}\llbracket Body \rrbracket(I) \leq [G] \cdot (I - \epsilon)$,[^literature-condition-3]
    <details>
    <summary>HeyVL Encoding</summary>

    ```heyvl
    proc I_decreases(init_vars: ...) -> (vars: ...)
        pre [G(init_vars)] * (I(init_vars) - epsilon)
        post 0
    {
        vars = init_vars // set current state to input values
        if G {
            Body
            assert I(vars)
            assume 0
        } else {}
    }
    ```

    </details>

Then `while G { Body }` is universally positively almost-surely terminating, i.e. `ert[while G { Body }](0) < ∞`.

### Usage

Consider the following example, where we have a loop that decrements a variable `x` with probability `0.5` in each iteration.
The loop terminates with probability `1` and the expected number of iterations is finite.
We show this by using the `@past` annotation on the loop.

```heyvl
proc main(init_x: UInt) -> (x: UInt)
{
    var prob_choice: Bool
    x = init_x
    @past(
        /* invariant: */ x + 1,
        /* epsilon:   */ 0.5,
        /* K:         */ 1)
    while 0 < x {
        prob_choice = flip(0.5)
        if prob_choice {
            x = x - 1
        } else {}
    }
}
```

**Inputs:**

- `invariant`: The ranking superinvariant.
- `epsilon`: The expected decrease of the ranking superinvariant in one loop iteration.
- `K`: The constant from Conditions 1 and 2.

:::note

Mathematically, the rule requires $\epsilon > 0$.
Currently, Caesar requires `epsilon` and `K` to be literal `UReal` expressions and checks $\epsilon < K$.

:::

### PAST via `ert` Superinvariants

Every use of `@past` can be replaced by a proof via an `ert`-superinvariant.

Let `L = while G { Body }`.
Assume that $\mathrm{ert}\llbracket Body \rrbracket(0) = 0$ and that the decrease premise of `@past` holds for some $V \colon \mathrm{States} \to \mathbb{R}_{\geq 0}$ and some $\epsilon > 0$, i.e. $[G] \cdot \mathrm{wp}\llbracket Body \rrbracket(V) \leq [G] \cdot (V - \epsilon)$.

Then the following expectation is an `ert`-superinvariant of $L$ with respect to postexpectation $0$:
$$
    J = 1 + [G] \cdot \frac{V}{\epsilon}
$$
Hence, by [Park induction](./induction.md), $\mathrm{ert}\llbracket L \rrbracket(0) \leq J$.
In particular, $L$ is PAST since $J$ is finite.

<details>
<summary>Generalization and Proof</summary>

More generally, assume that $\mathrm{ert}\llbracket Body \rrbracket(0) \leq c$ holds for some constant $c \in \mathbb{R}_{\geq 0}$.
Then

$$
    J = 1 + [G] \cdot \frac{c + 1}{\epsilon} \cdot V
$$

is an `ert`-superinvariant of $L$.
The theorem above is the special case $c = 0$.

Write $\Phi_0$ for the `ert` loop-characteristic function of $L$ with postexpectation $0$.
Then

$$
\begin{align*}
    \Phi_0(J)
        &= 1 + [\neg G] \cdot 0 + [G] \cdot \mathrm{ert}\llbracket Body \rrbracket(J) \tag{definition} \\
        &= 1 + [G] \cdot \left(\mathrm{ert}\llbracket Body \rrbracket(0) + \mathrm{wp}\llbracket Body \rrbracket(J)\right) \tag{ert decomposition} \\
        &= 1 + [G] \cdot \left(\mathrm{ert}\llbracket Body \rrbracket(0) + \mathrm{wp}\llbracket Body \rrbracket\left(1 + \frac{c + 1}{\epsilon} \cdot [G] \cdot V\right)\right) \tag{definition of $J$} \\
        &= 1 + [G] \cdot \left(\mathrm{ert}\llbracket Body \rrbracket(0) + \mathrm{wp}\llbracket Body \rrbracket(1) + \mathrm{wp}\llbracket Body \rrbracket\left(\frac{c + 1}{\epsilon} \cdot [G] \cdot V\right)\right) \tag{linearity of wp} \\
        &= 1 + [G] \cdot \left(\mathrm{ert}\llbracket Body \rrbracket(0) + \mathrm{wp}\llbracket Body \rrbracket(1) + \frac{c + 1}{\epsilon} \cdot \mathrm{wp}\llbracket Body \rrbracket([G] \cdot V)\right) \tag{homogeneity of wp} \\
        &\leq 1 + [G] \cdot \left(c + \mathrm{wp}\llbracket Body \rrbracket(1) + \frac{c + 1}{\epsilon} \cdot \mathrm{wp}\llbracket Body \rrbracket([G] \cdot V)\right) \tag{$\mathrm{ert}\llbracket Body \rrbracket(0) \leq c$} \\
        &\leq 1 + [G] \cdot \left(c + 1 + \frac{c + 1}{\epsilon} \cdot \mathrm{wp}\llbracket Body \rrbracket([G] \cdot V)\right) \tag{feasibility} \\
        &\leq 1 + [G] \cdot \left(c + 1 + \frac{c + 1}{\epsilon} \cdot \mathrm{wp}\llbracket Body \rrbracket(V)\right) \tag{monotonicity of wp} \\
        &\leq 1 + [G] \cdot \left(c + 1 + \frac{c + 1}{\epsilon} \cdot (V - \epsilon)\right) \tag{decrease condition} \\
        &= 1 + [G] \cdot \left(c + 1 + \frac{c + 1}{\epsilon} \cdot V - (c + 1)\right) \tag{arithmetic} \\
        &= 1 + [G] \cdot \frac{c + 1}{\epsilon} \cdot V \tag{simplify} \\
        &= J \tag{arithmetic}
\end{align*}
$$

So $J$ is an `ert`-superinvariant of $L$, and [Park induction](./induction.md) yields $\mathrm{ert}\llbracket L \rrbracket(0) \leq J$.

</details>

[^exact-body]: Caesar only accepts `@past` in settings where the loop body is exact; see [Proof Rule Approximations](./approximations.md#proof-rule-approximations).
[^literature-condition-3]: Kaminski writes $\Phi_0(I) \leq [G] \cdot (I - \epsilon)$ instead for condition 3, where $\Phi_0$ is the loop-characteristic function with respect to postexpectation $0$. Our condition is equivalent to this, but simplified.

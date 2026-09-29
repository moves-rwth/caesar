---
sidebar_position: 5
---

# Almost-Sure Termination

_Almost-sure termination_ (AST for short) means that a program terminates with probability one.
In our probabilistic setting, this does not necessarily mean that all executions terminate (we would call that _certain termination_), but only that the expected value to reach a terminating state is one.
In terms of weakest pre-expectations, this means that `wp[C](1) = 1` holds for a program `C`.
For a nice overview of details and proof rules that are available in the literature, we refer to [Chapter 6 of Benjamin Kaminski's PhD thesis](https://publications.rwth-aachen.de/record/755408/files/755408.pdf#page=139).

In Caesar, there are several ways to prove almost-sure termination:

```mdx-code-block
import TOCInline from '@theme/TOCInline';

<TOCInline toc={toc} maxHeadingLevel="2" />
```

## Lower Bounds on Weakest Pre-Expectations

With an encoding of standard weakest pre-expectation reasoning (`wp`), it is sufficient to encode the proof of `1 <= wp[C](1)` in HeyVL, i.e. verify a `proc` with `pre` and `post` of value `1`.
Since `wp[C](1) <= 1` always holds (by a property often called _feasibility_), `1 <= wp[C](1)` implies `wp[C](1) = 1`, i.e. almost-sure termination.

Lower bounds on weakest pre-expectations need a proof rule like [omega-invariants](./omega-invariants.md) to reason about loops.
To _refute_ a lower bound on weakest pre-expectations, [unrolling](./unrolling.md) (also known as bounded model checking) can be used.

## A New Proof Rule for Almost-Sure Termination (`@ast` Annotation) {#new-proof-rule}

The `@ast` annotation proves almost-sure termination of a loop from every initial state satisfying a Boolean invariant $\mathtt{I}$.
Caesar's `@ast` rule adapts the _"new proof rule for almost-sure termination"_ by [McIver et al. (POPL 2018)](https://dl.acm.org/doi/10.1145/3158121).
An [extended version of the paper](https://arxiv.org/pdf/1711.03588.pdf) is available on arXiv.

The rule uses a _loop variant_ $\mathtt{V}$ to measure progress towards termination.
If an iteration starts with variant value $v$, it must exit or decrease $\mathtt{V}$ by at least $\mathtt{decrease}(v)$ with probability at least $\mathtt{prob}(v)$.
Both functions must be positive, and nonincreasing on positive arguments.

The variant may increase on individual iterations, but its expected value after an iteration must not exceed its value before the iteration.
For this expectation, the variant is treated as zero if the loop exits.
The invariant $\mathtt{I}$ must hold before the loop and after each iteration.

### Formal Theorem

Consider a loop `while G { Body }`.
In the encodings below, `vars` denotes the variables used by the loop or annotation, excluding loop-local variables and the logical argument `v`.
Choose:

- $\mathtt{I}$, a Boolean invariant,
- $\mathtt{V}$, a variant with values in $\mathbb{R}_{\geq 0}$,
- $\mathtt{prob} \colon \mathbb{R}_{\geq 0} \to (0,1]$,
- $\mathtt{decrease} \colon \mathbb{R}_{\geq 0} \to \mathbb{R}_{> 0}$.

Caesar checks the following five conditions:

1. Under `I`, $0 < \mathtt{prob}(v) \le 1$ for every $v \ge 0$, and $\mathtt{prob}(b) \le \mathtt{prob}(a)$ for every $0 < a \le b$.
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    proc prob_conditions(vars: ..., a: UReal, b: UReal) -> ()
        pre ?(I(vars) && a <= b)
        post ?(0 < prob(b))
        post ?(a > 0 ==> prob(b) <= prob(a))
        post ?(prob(a) <= 1)
    {}
    ```

    </p>
    </details>
2. Under `I`, $\mathtt{decrease}(v) > 0$ for every $v \ge 0$, and $\mathtt{decrease}(b) \le \mathtt{decrease}(a)$ for every $0 < a \le b$.
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    proc decrease_conditions(vars: ..., a: UReal, b: UReal) -> ()
        pre ?(I(vars) && a <= b)
        post ?(0 < decrease(b))
        post ?(a > 0 ==> decrease(b) <= decrease(a))
    {}
    ```

    </p>
    </details>
3. Under `I && G`, `wp[Body]([I]) = 1`: the body terminates almost surely and preserves `I`.
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    @wp
    proc I_wp_subinvariant(init_vars: ...) -> (vars: ...)
        pre [I(init_vars)]
        post [I(vars)]
    {
        vars = init_vars // set current state to input values
        if G {
            Body
        } else {}
    }
    ```

    </p>
    </details>
4. Under `I && G`, `awp[Body]([G] * V) <= V`: the expected variant, set to zero on exit, does not increase.
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    coproc V_awp_superinvariant(init_vars: ...) -> (vars: ...)
        pre !?(I(init_vars))
        pre V(init_vars)
        post [G(vars)] * V(vars)
    {
        vars = init_vars // set current state to input values
        if G {
            Body_awp
        } else {}
    }
    ```

    `Body_awp` replaces demonic choice with angelic choice and `havoc` with `cohavoc`.
    Conditions 3 (invariant) and 5 (progress) use the original body.

    </p>
    </details>
5. Under `I && G`, the probability of exit or a decrease by at least `decrease(v)` is at least `prob(v)`, with `v` fixed to the initial variant value.
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    @wp
    proc progress_condition(init_vars: ...) -> (vars: ...)
        pre ?(I(init_vars))
        pre ?(G(init_vars))
        pre prob(V(init_vars))
        post [!G(vars) || V(vars) + decrease(V(init_vars)) <= V(init_vars)]
    {
        vars = init_vars // set current state to input values
        Body
    }
    ```

    </p>
    </details>

If these conditions hold, `while G { Body }` terminates almost surely from every initial state satisfying `I`, i.e. `[I] <= wp[while G { Body }](1)`.

### Usage

Use `@ast(I, V, v, prob(v), decrease(v))` to generate the five checks above.
The following program encodes the "escaping spline" example from [Section 5.4 of the paper](https://dl.acm.org/doi/pdf/10.1145/3158121#page=18).

```heyvl
proc ast_example4() -> ()
    pre 1
    post 1
{
    var x: UInt
    @ast(
        /* invariant: */    true,
        /* variant: */      x,
        /* variable: */     v,
        /* prob(v): */      1/(v+1),
        /* decrease(v): */  1
    )
    while x != 0 {
        var prob_choice: Bool = flip(1 / (x + 1))
        if prob_choice {
            x = 0
        } else {
            x = x + 1
        }
    }
}
```

#### Inputs

The five parameters are:

 * `invariant`: The Boolean invariant `I`, which holds at loop entry and after each iteration.
 * `variant`: The variant `V`, of type `UReal`.
 * `variable`: The logical variable `v`, scoped to `prob(v)` and `decrease(v)`.
 * `prob(v)`: A lower bound on the probability of exit or a decrease of at least `decrease(v)`.
 * `decrease(v)`: The decrease required by the progress condition.

`prob` and `decrease` may depend only on `v` and variables not modified by the loop.
Include any required bounds on these unchanged variables in `I`.

The loop body must not contain angelic or additive choice, `cohavoc`, `havoc` over infinite domains, procedure calls, or uninitialized loop-local declarations.
Caesar warns if it cannot prove a `havoc` domain is finite; check such domains manually.

### Soundness

This rule is based on McIver et al.'s soundness theorem, with the adaptations listed below.
A formal soundness proof for these adaptations is still pending.

<details>
<summary>Differences from the published formulations</summary>

These comparisons use the same `I`, `V`, `prob`, and `decrease`.

Compared with [McIver et al., POPL 2018, Theorem 4.1](https://arxiv.org/pdf/1711.03588.pdf#page=7):

- **Function assumptions → conditions 1–2:** unchanged.
- **(i), invariant → condition 3:** unchanged; `I` is preserved and the body terminates almost surely under `I && G`.
- **(ii), positive active variant:** the paper requires `I && G ==> V > 0`; Caesar allows `V = 0` while the guard holds.
- **(iii), progress → condition 5:** the paper counts only `V + decrease(v) <= v` as progress; Caesar also counts `!G`.
- **(iv), supermartingale → condition 4:** the paper requires `[I && G] * (H ⊖ V) <= wp[Body](H ⊖ V)` for every `H > 0`, where `H ⊖ V = max(H - V, 0)`.
  With body termination from condition 3, this is equivalent to `awp[Body](V) <= V` under `I && G` ([Lemma B.1](https://arxiv.org/pdf/1711.03588.pdf#page=33)).
  Caesar instead checks `awp[Body]([G] * V) <= V`, so exit values do not affect the bound.

Compared with [Kaminski's thesis, Theorem 6.8](https://publications.rwth-aachen.de/record/755408/files/755408.pdf#page=149):

- **Function assumptions → conditions 1–2:** the bounds are the same, but the thesis additionally requires antitonicity at zero.
- **(a), invariant → condition 3:** unchanged, including body termination under `I && G`.
- **(b), termination indication:** the thesis requires `!G <==> V == 0` in every state; Caesar allows zero while active and positive values after exit.
- **(c), superinvariant → condition 4:** the thesis requires `awp[Body](V) <= V` under `G`, including outside `I`; Caesar checks `awp[Body]([G] * V) <= V` only under `I && G`.
- **(d), progress → condition 5:** as in POPL (iii), the thesis counts only `V + decrease(v) <= v`; Caesar also counts `!G`.

</details>

### HeyVL Encoding

Besides generating the five checks, Caesar replaces the loop with:

```heyvl
assert [I]
havoc modified_vars
validate
assume [I]
```

This checks `I` at loop entry and forgets modified variables, excluding loop-local declarations.
The following statements must verify for every resulting state satisfying `I`.
Unmodified variables retain their values.

---
sidebar_position: 7
description: Proof rule for lower bounds on least fixpoints.
---

# Optional Stopping Theorem

For the analysis of loops, the [induction proof rule](induction) allows obtaining upper bounds on the `wp`-semantics through superinvariants.
Under certain additional conditions, subinvariants `I` can also provide valid lower bounds on the `wp`-semantics (`I <= wp[C](f)`).
The Optional Stopping Theorem identifies conditions ensuring _uniform integrability_ of the subinvariant as one such constraint.

Intuitively, the proof rule requires that the loop executes finitely many iterations in expectation (e.g. that the loop is [PAST](past)) and that one can find a constant that bounds the expected change of the subinvariant by one loop iteration.

Caesar supports the "Optional Stopping Theorem for Weakest Preexpectation Reasoning" by Hark et al. as a built-in encoding.[^1]
You can find the [extended version of the paper on arxiv](https://arxiv.org/abs/1904.01117).
The paper was [published at POPL 2020](https://doi.org/10.1145/3371105).

## Formal Theorem

Consider a loop `while G { Body }` whose `Body` is [AST](ast).
The loop's used and modified variables, except the ones declared within the loop, are referred to as `vars`.
Give

- `I`, a function assigning a value $\mathbb{R}_{\geq 0}$ to every state,
- `PAST_I`, a function assigning a value $\mathbb{R}_{\geq 0}$ to every state,
- `c` $\in \mathbb{R}_{\geq 0}$,
- `f`, a function assigning a value $\mathbb{R}_{\geq 0}$ to every state,

such that all the following conditions are fulfilled:

1. `I` is a `wp`-subinvariant of `while G { Body }` with respect to `f`,
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    @wp
    proc I_wp_subinvariant(init_vars: ...) -> (vars: ...)
        pre I(init_vars)
        post f(vars)
    {
        vars = init_vars // set current state to input values
        @unroll(1, I(vars))
        while G {
            Body
        }
    }
    ```

    </p>
    </details>
2. `while G { Body }` performs finitely many loop iterations in expectation: `PAST_I` $< \infty$ is a `wp`-superinvariant[^modified-ert] of `while G { Body; tick 1 }` with respect to `PAST_I`,
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    @wp
    coproc PAST_I_ert_superinvariant(init_vars: ...) -> (vars: ...)
        pre PAST_I(init_vars)
        post PAST_I(vars)
    {
        vars = init_vars // set current state to input values
        if G {
            Body
            tick 1
        }
    }
    ```

    </p>
    </details>
3. `I` harmonizes with `f`: $\neg\mathtt{G} \implies (\mathtt{I} = \mathtt{f})$, i.e. `I` and `f` are equal on states that do not fulfill the loop guard `G`,
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    proc I_harmonizes_with_post(vars: ...) -> ()
        pre ?(!G(vars))
        post ?(I(vars) == f(vars))
    {}
    ```

    </p>
    </details>
4. The expected value of `I` after one loop iteration is finite,[^inv-iter-finite]
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    @wp
    coproc I_iter_finite(init_vars: ...) -> (vars: ...)
        pre 0
        post I(vars)
    {
        vars = init_vars // set current state to input values
        validate // maps finite expectation to 0, ∞ to ∞
        if G {
            Body
        }
    }
    ```

    </p>
    </details>
5. `I` is _conditionally difference bounded_ by `c`: the absolute change of `I` by one loop iteration is at most `c`.
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    @wp
    coproc I_conditionally_difference_bounded_by_c(init_vars: ...) -> (vars: ...)
        pre c
        post ite(I(init_vars) <= I(vars), I(vars) - I(init_vars), I(init_vars) - I(vars)) // |I(vars) - I(init_vars)|
    {
        vars = init_vars // set current state to input values
        Body
    }
    ```

    </p>
    </details>

Then, `I <= wp[while G { Body }](f)` holds.

## Usage

By applying the `@ost` annotation to a loop, Caesar will check the above requirements for a given invariant, PAST invariant, constant and post-expectation.
Below is the encoding of [Example 39 from the paper](https://dl.acm.org/doi/pdf/10.1145/3371105#page=18).
It is a _geometric loop_ program, which increments a counter `b` with probability $0.5$ or stops (setting `a = false`).
The HeyVL program uses the `@ost` annotation that proves a lower bound of `b + [a]` on the expected value of `b`.

```heyvl
proc ost_geo_loop_example(init_a: Bool, init_b: UInt, init_k: UInt) -> (a: Bool, b: UInt, k: UInt)
    pre init_b + [init_a]
    post b
{
    a = init_a
    b = init_b
    k = init_k

    @ost(
        /* invariant */ b + [a],
        /* past_invariant */ 2 * [a],
        /* cdb */ 1,
        /* post */ b
    )
    while a {
        var prob_choice: Bool = flip(1 / 2)
        if prob_choice {
            a = false
        } else {
            b = b + 1
        }
        k = k + 1
    }
}
```

### Inputs

You can see all four parameters are passed to the `@ost` annotation in sequence:

- `invariant`: The quantitative subinvariant which should lower bound the `wp`-semantics. Must harmonize with `post`.
- `past_invariant`: The quantitative invariant used to proof PAST.
- `cdb`: A constant of type `UReal` specifying the conditional difference bound for the `invariant`.
- `post`: The post-expectation after the loop.

:::warning

All parameters must be finite, i.e. cannot evaluate to $\infty$.
Currently, this is only checked by Caesar for `past_invariant` and `cdb`.

:::

[^1]: We present the conditions from the paper's Theorem 37 (b), as used by the built-in encoding to ensure uniform integrability of the subinvariant. Currently, using the paper's alternative conditions (a) or (c) requires a manual encoding.
[^modified-ert]: Our `PAST_I` condition effectively encodes an `ert`-superinvariant, where `ert` is a modified [expected runtime calculus](calculi) which counts the number of loop iterations of `while G { Body }` and does not count any nested loop iterations in `Body`.
[^inv-iter-finite]: In the paper, the condition to check is $\Phi_{\mathtt{f}}(\mathtt{I}) < \infty$. With the additional constraint that `I` harmonizes with `f`, we instead check the simpler but equivalent condition that $\Phi_{\mathtt{I}}(\mathtt{I}) < \infty$ holds.

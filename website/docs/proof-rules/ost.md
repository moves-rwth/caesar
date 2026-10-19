---
sidebar_position: 7
description: Proof rule for lower bounds on least fixpoints.
---

# Optional Stopping Theorem

The `@ost` annotation proves lower bounds on the expected result of a loop: `I <= wp[while G { Body }](f)`.
The candidate bound `I` must not decrease in expectation during an iteration and must equal the postexpectation `f` on exit.
The rule also requires a finite expected number of iterations and a constant bound on the expected absolute change of `I` in each iteration.

The rule is based on the "Optional Stopping Theorem for Weakest Preexpectation Reasoning" by [Hark et al. (POPL 2020)](https://doi.org/10.1145/3371105).
For upper bounds on expected results, use [induction](./induction.md).

## Formal Theorem

Consider a loop `while G { Body }` whose `Body` is purely probabilistic (without nondeterministic choices) and [AST](./ast.md).
Choose finite expectations `I`, `PAST_I`, and `f`, and a constant $c \geq 0$.
In the encodings below, `vars` denotes the variables used by the loop or annotation, excluding loop-local variables.

Caesar checks the following five conditions:

1. `I` is a `wp`-subinvariant of the loop with postexpectation `f`.
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
2. `PAST_I` is finite and bounds the expected number of loop iterations.
    It is a superinvariant for counting iterations, with `tick 1` added after `Body`.
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
        } else {}
    }
    ```

    </p>
    </details>
3. Whenever `G` is false, `I` equals `f`: `!G ==> I == f`.
    This is called _harmonization_.
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
4. `I` has finite expected value after `if G { Body } else {}`.
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
        } else {}
    }
    ```

    </p>
    </details>
5. Under `G`, the expected absolute change of `I` after `Body` is at most `c` (_conditional difference boundedness_).
    This includes iterations that exit the loop.
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
        if G {
            Body
        } else {}
    }
    ```

    </p>
    </details>

If these conditions hold, `I <= wp[while G { Body }](f)`.

## Usage

Use `@ost(I, PAST_I, c, f)` to generate the five checks above.

The following [geometric loop](https://arxiv.org/pdf/1904.01117v3#page=19) stops with probability $0.5$ in each iteration and otherwise increments `b`.
The invariant `b + [a]` gives a lower bound on the expected final value of `b`.

```heyvl
@wp
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

The four parameters are:

- `invariant`: The subinvariant `I`.
- `past_invariant`: The superinvariant `PAST_I` for counting iterations.
- `cdb`: The bound `c`, given as a `UReal` literal.
- `post`: The postexpectation `f`.

Use `@ost` with `@wp` and an [exact loop-body encoding](./approximations.md#proof-rule-approximations).
The annotated loop must be the last statement of its procedure.

## Soundness

The theorem assumes that `Body` terminates almost surely and contains no nondeterminism, and that `f` is finite in every state.
Caesar does not check these assumptions.
Finiteness of `I` and `PAST_I` follows from the generated checks.

<details>
<summary>Differences from the published formulations</summary>

Compared with [Hark et al., Theorem 38(b) in the extended paper](https://arxiv.org/pdf/1904.01117v3#page=17) (Theorem 37(b) in the published paper):

- **Scope:** `@ost` implements case (b).
  Cases (a) and (c) require a manual encoding.
- **Looping time:** `PAST_I` proves a finite bound on the expected number of outer-loop iterations.
  It does not count the runtime of `Body`.
- **Equivalent encodings:** harmonization is checked as a Boolean equality.
  The finiteness encoding above uses `I` on exit, where `I = f`.

Compared with [our OOPSLA '23 paper, Appendix C.5](https://arxiv.org/pdf/2309.07781v3#page=43):

- **Difference bound:** the paper checks the unguarded `Body` in every state.
  Caesar checks it only under `G`, as in [Hark et al.'s Definition 35](https://arxiv.org/pdf/1904.01117v3#page=16).
  This removes an unnecessary restriction: when `G` is false, no iteration executes and the change is zero.
- **Looping time:** the paper leaves PAST to a separate proof; `@ost` generates the iteration-count check.

</details>

---
sidebar_position: 7
description: Proof rule for lower bounds on least fixpoints.
---

# Optional Stopping Theorem

The `@ost` annotation proves lower bounds on the expected result of a loop: `I <= wp[while G { Body }](f)`.
The candidate bound `I` must be finite, must not decrease in expectation during an iteration, and must be at most the postexpectation `f` on exit.
The rule also requires a finite expected number of iterations and a constant bound on the expected absolute change of `I` in each iteration.

The rule is based on the "Optional Stopping Theorem for Weakest Preexpectation Reasoning" by [Hark et al. (POPL 2020)](https://doi.org/10.1145/3371105).
For upper bounds on expected results, use [induction](./induction.md).

## Formal Theorem

Consider a loop `while G { Body }` whose `Body` is purely probabilistic (without nondeterministic choices) and [AST](./ast.md).
Choose finite expectations `I` and `PAST_I`, a nonnegative postexpectation `f` that may take the value infinity, and a finite constant $c \geq 0$.
In the encodings below, `vars` denotes the variables used by the loop or annotation, excluding loop-local variables.

Caesar checks the following four conditions:

1. `I` is a `wp`-subinvariant of the loop with postexpectation `f`.
    This means that `I <= wp[Body](I)` under `G` and `I <= f` under `!G`.
    When the loop exits, `I` may be strictly smaller than `f`.
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
2. `PAST_I` is finite and bounds the expected looping time (the expected number of loop iterations).
    It counts executions of `Body`, independently of the runtime of `Body`.
    It is a superinvariant for counting iterations, with `tick 1` added after `Body`.
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    @wp
    proc PAST_I_finite(vars: ...) -> () {
        assert ?(PAST_I(vars) < ∞)
    }

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
3. `I` is finite in every state: `I < ∞`.
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    proc I_finite(vars: ...) -> () {
        assert ?(I(vars) < ∞)
    }
    ```

    </p>
    </details>
4. Under `G`, the expected absolute change of `I` after `Body` is at most `c` (_conditional difference boundedness_).
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

Use `@ost(I, PAST_I, c, f)` to check the four conditions above.
Caesar generates five procedures because it checks finiteness of `PAST_I` separately from its superinvariant condition.

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

- `invariant`: The finite subinvariant `I`.
- `past_invariant`: The superinvariant `PAST_I` for counting iterations.
- `cdb`: The bound `c`, given as a `UReal` literal.
- `post`: The postexpectation `f`, which may take the value infinity.

Use `@ost` with `@wp` and an [exact loop-body encoding](./approximations.md#proof-rule-approximations).
The annotated loop must be the last statement of its procedure.

## Soundness

The theorem assumes that `Body` terminates almost surely and contains no nondeterminism.
Caesar does not check these assumptions.
Caesar checks finiteness of `I` and `PAST_I` directly; `f` need not be finite.

The proof rule generalizes [Hark et al., Theorem 38(b)](https://arxiv.org/pdf/1904.01117v3#page=17), and simplifies the OST encoding in [Schröer et al., *A Deductive Verification Infrastructure for Probabilistic Programs*, Appendix C.5](https://arxiv.org/pdf/2309.07781v3#page=43).
Cases (a) and (c) require a manual encoding.

<details>
<summary>Differences from the published formulations</summary>

Compared with [Hark et al., Theorem 38(b) in the extended paper](https://arxiv.org/pdf/1904.01117v3#page=17) (Theorem 37(b) in the published paper):

- Caesar drops harmonization (`I = f` on exit).
  The exit inequality `I <= f` already follows from subinvariance.
- The postexpectation `f` may take the value infinity.
- Caesar checks `I < ∞` instead of $\Phi_f(I)<\infty$, where $\Phi_f$ is the loop characteristic function on nonnegative expectations with postexpectation $f$.

<details>
<summary>Justification of these simplifications</summary>

These simplifications follow by applying Theorem 38(b) with finite $I$ as both candidate and postexpectation.
Its harmonization premise is then $I=I$.
Conditional difference boundedness gives $\Phi_I(I)\leq I+c<\infty$, as required by the theorem.

The exit condition $I\leq f$ gives $\Phi_I(X)\leq\Phi_f(X)$ for every nonnegative expectation $X$.
For the annotated loop $C$, the theorem and monotonicity of least fixed points therefore give
$$
\begin{aligned}
    I
        &\leq\mathrm{wp}\llbracket C\rrbracket(I)
        &&\text{(Theorem 38(b))}\\
        &\leq\mathrm{wp}\llbracket C\rrbracket(f).
        &&\text{(monotonicity)}
\end{aligned}
$$
The comparison with $f$ holds for nonnegative extended expectations, so $f$ may take infinite values.

</details>

Compared with the [Encoding of the Optional Stopping Theorem for wp (Appendix C.5)](https://arxiv.org/pdf/2309.07781v3#page=43):

- Caesar drops harmonization and checks `I < ∞` directly in place of the finiteness condition on $\Phi_f(I)$.
- Caesar checks conditional difference boundedness only for states satisfying `G`, as in [Hark et al.'s Definition 35](https://arxiv.org/pdf/1904.01117v3#page=16).
  The unguarded check in Appendix C.5 can reject valid invariants whose change is unbounded outside the guard.
- Appendix C.5 requires [finite expected runtime](https://arxiv.org/pdf/2309.07781v3#page=23) of the whole loop.
  Here, `Body` may have infinite expected runtime, provided it is AST and the expected number of outer-loop iterations is finite.

#### Rewards and expected runtimes

For a purely probabilistic program $P$ and a nonnegative expectation $X$, [Hark et al., Section 8](https://arxiv.org/pdf/1904.01117v3#page=22) give
$$
\mathrm{ert}\llbracket P\rrbracket(X)
=\mathrm{ert}\llbracket P\rrbracket(0)+\mathrm{wp}\llbracket P\rrbracket(X).
$$
For nonnegative rewards, retain the cost term in subinvariance and use ordinary $\mathrm{wp}$ for iteration counts and absolute changes.

</details>

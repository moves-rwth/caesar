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

Caesar supports the _"new proof rule for almost-sure termination"_ by McIver et al. as a built-in encoding.
You can find the [extended version of the paper on arxiv](https://arxiv.org/pdf/1711.03588.pdf).
The paper was [published at POPL 2018](https://dl.acm.org/doi/10.1145/3158121).

The proof rule is based on a real-valued _loop variant_ $\mathtt{V}$ (also known as _super-martingale_) that decreases randomly with a certain probability $\mathtt{prob}(v)$ in each iteration by a certain amount $\mathtt{decrease}(v)$, where $v = V(s)$ is the variant's value in the current state $s$.
The latter two quantities are specified by user-provided _decrease_ and _probability_ functions.
Additionally, a Boolean _invariant_ $\mathtt{I}$ must be specified which limits the set of states on which almost-sure termination is checked.

### Formal Theorem

Consider a loop `while G { Body }`.
The loop's used and modified variables, except the ones declared within the loop, are referred to as `vars`.
Give
- $\mathtt{I}$ a Boolean predicate,
- $\mathtt{V}$ a variant function assigning a value $\mathbb{R}_{\geq 0}$ to every state,
- $\mathtt{prob} \colon \mathbb{R}_{\geq 0} \to (0,1]$,
- $\mathtt{decrease} \colon \mathbb{R}_{\geq 0} \to \mathbb{R}_{> 0}$,

such that all the following conditions are fulfilled:

1. $\mathtt{prob}$ is antitone,
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    proc prob_antitone(a: UReal, b: UReal) -> ()
        pre ?(a <= b)
        post ?(prob(a) >= prob(b))
    {}
    ```

    </p>
    </details>
2. $\mathtt{decrease}$ is antitone,
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    proc decrease_antitone(a: UReal, b: UReal) -> ()
        pre ?(a <= b)
        post ?(decrease(a) >= decrease(b))
    {}
    ```

    </p>
    </details>
3. `[I]` is a `wp`-subinvariant of `while G { Body }` with respect to `[I]`,
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
4. For states fulfilling the invariant `I`: if the loop guard `G` holds, then $\mathtt{V} > 0$,
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    proc termination_condition(vars: ...) -> ()
        pre ?(I(vars))
        post ?(G(vars) ==> V(vars) > 0)
    {}
    ```

    </p>
    </details>
5. Under `I`, `V` is an `awp`-superinvariant: its expected value does not increase under any demonic choice.
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    coproc V_awp_superinvariant(init_vars: ...) -> (vars: ...)
        pre ?(!I(init_vars))
        pre V(init_vars)
        post V(vars)
    {
        vars = init_vars // set current state to input values
        if G {
            Body_awp
        } else {}
    }
    ```

    `Body_awp` replaces demonic choice with angelic choice and `havoc` with `cohavoc`.
    Conditions 3 (invariant) and 6 (progress) use the original body.

    </p>
    </details>
6. `V` satisfies a _progress_ condition, ensuring that, in expectation, one loop iteration decreases the variant by at least `decrease` with probability at least `prob`.
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    @wp
    proc progress_condition(init_vars: ...) -> (vars: ...)
        pre [I(init_vars)] * [G(init_vars)] * prob(V(init_vars))
        post [V(vars) <= V(init_vars) - decrease(V(init_vars))]
    {
        vars = init_vars // set current state to input values
        Body
    }
    ```

    </p>
    </details>

Then `while G { Body }` is almost-surely terminating from all initial states satisfying `I`, i.e. `[I] <= wp[while G { Body }](1)`.


### Usage

Use `@ast(I, V, v, prob(v), decrease(v))` to generate the six checks above.
Below is the encoding of the "escaping spline" example [from Section 5.4 of the proof rule's paper](https://dl.acm.org/doi/pdf/10.1145/3158121#page=18).

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

 * `invariant`: A Boolean invariant that holds before, during, and after the loop.
 * `variant`: The variant of type `UReal`.
 * `variable`: The free variable `v` used in `prob(v)` and `decrease(v)`.
 * `prob(v)`: The minimum probability of a decrease at variant value `v`.
 * `decrease(v)`: The minimum decrease at variant value `v`.

:::warning[Manual checks]

Check that `prob` and `decrease` depend only on `v` and variables not modified by the loop.
Also check `0 < prob(v) <= 1` and `decrease(v) > 0` for every `v >= 0`.
Caesar does not verify these assumptions.
If Caesar warns about a `havoc` domain, also check that it is finite.

:::

The loop body must not contain angelic or additive choice, `cohavoc`, `havoc` over infinite domains, procedure calls, or uninitialized loop-local declarations.
Caesar warns on `havoc` if it cannot prove that each variable's type is finite.

### Soundness

`@ast` under-approximates `wp` for exact loop bodies, supporting sound verification in a `proc`.
Use [`@wp`](./approximations#calculus-annotations) to check the required approximations.

<details>
<summary>Differences from the published formulations</summary>

These comparisons use the same `I`, `V`, `prob`, and `decrease`.

Compared with [POPL Theorem 4.1](https://arxiv.org/pdf/1711.03588.pdf#page=7):

- **Conditions 1–2 (antitonicity), more restrictive:** Caesar checks `prob` and `decrease` also at zero; the paper requires antitonicity only for positive arguments.
- **Condition 5 (superinvariant), equivalent under condition 3:** Caesar checks `awp[Body](V) <= V` under `I && G`.
  The paper's condition (iv) instead checks `H ⊖ V <= wp[Body](H ⊖ V)` under `I && G` for every `H > 0`, where `H ⊖ V = max(H - V, 0)`.
  Condition 3 ensures that `Body` terminates almost surely under `I && G`, so [Lemma B.1](https://arxiv.org/pdf/1711.03588.pdf#page=33) gives equivalence for every demonic choice.
- **Condition 6 (progress), more permissive:** Caesar uses `V <= max(v - decrease(v), 0)` where the paper's condition (iii) uses `V <= v - decrease(v)`.
  These agree when `decrease(v) <= v`; otherwise Caesar accepts reaching `V = 0`, whereas the paper's event is impossible because its bound is negative.
  Conditions 3 and 4 ensure that reaching `V = 0` forces loop exit.

Compared with [Kaminski's thesis, Theorem 6.8](https://publications.rwth-aachen.de/record/755408/files/755408.pdf#page=149):

- **Condition 4 (termination), more permissive:** Caesar requires `I && G ==> V > 0`; the thesis's condition (b) requires `!G <==> V == 0` in all states.
  Caesar allows positive `V` after loop exit and imposes no positivity condition outside `I`.
- **Condition 5 (superinvariant), more permissive:** The thesis's condition (c) requires `awp[Body](V) <= V` whenever `G` holds; Caesar requires it only under `I && G`.
- **Condition 6 (progress), more permissive:** The thesis's condition (d) uses ordinary subtraction; Caesar's truncated subtraction also accepts reaching `V = 0` when `decrease(v) > v`.

</details>

### HeyVL Encoding

Besides generating the six checks, Caesar replaces the loop with:

```heyvl
assert [I]
havoc modified_vars
validate
assume [I]
```

This checks `I` at loop entry and forgets modified variables, excluding loop-local declarations.
The following statements must verify for every resulting state satisfying `I`.
Unmodified variables retain their values.

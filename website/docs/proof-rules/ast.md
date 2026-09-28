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

The proof rule uses a nonnegative _loop variant_ $\mathtt{V}$ whose expected value does not increase, counting its value as zero after loop exit.
Each iteration must exit or decrease the variant by at least $\mathtt{decrease}(v)$ with probability at least $\mathtt{prob}(v)$, where $v$ is the variant's initial value.
Additionally, a Boolean _invariant_ $\mathtt{I}$ must be specified which limits the set of states on which almost-sure termination is checked.

### Formal Theorem

Consider a loop `while G { Body }`.
The loop's and annotation's variables, except loop-local declarations and the logical argument `v`, are referred to as `vars`.
Give

- $\mathtt{I}$ a Boolean predicate,
- $\mathtt{V}$ a variant function assigning a value $\mathbb{R}_{\geq 0}$ to every state,
- $\mathtt{prob} \colon \mathbb{R}_{\geq 0} \to (0,1]$,
- $\mathtt{decrease} \colon \mathbb{R}_{\geq 0} \to \mathbb{R}_{> 0}$,

such that all the following conditions are fulfilled:

1. Under `I`, $0 < \mathtt{prob}(b) \le \mathtt{prob}(a) \le 1$ for every $0 \le a \le b$.
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    proc prob_conditions(vars: ..., a: UReal, b: UReal) -> ()
        pre ?(I(vars) && a <= b)
        post ?(0 < prob(b) && prob(b) <= prob(a) && prob(a) <= 1)
    {}
    ```

    </p>
    </details>
2. Under `I`, $0 < \mathtt{decrease}(b) \le \mathtt{decrease}(a)$ for every $0 \le a \le b$.
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    proc decrease_conditions(vars: ..., a: UReal, b: UReal) -> ()
        pre ?(I(vars) && a <= b)
        post ?(0 < decrease(b) && decrease(b) <= decrease(a))
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
4. Under `I && G`, `awp[Body](ite(G, V, 0)) <= V`: the expected variant does not increase under any demonic choice, counting zero on exit.
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    coproc V_awp_superinvariant(init_vars: ...) -> (vars: ...)
        pre ?(!I(init_vars))
        pre V(init_vars)
        post ite(G(vars), V(vars), 0)
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
        pre [I(init_vars)] * [G(init_vars)] * prob(V(init_vars))
        post [!G(vars) || V(vars) + decrease(V(init_vars)) <= V(init_vars)]
    {
        vars = init_vars // set current state to input values
        Body
    }
    ```

    </p>
    </details>

Then `while G { Body }` is almost-surely terminating from all initial states satisfying `I`, i.e. `[I] <= wp[while G { Body }](1)`.


### Usage

Use `@ast(I, V, v, prob(v), decrease(v))` to generate the five checks above.
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
 * `variable`: The logical variable `v`, scoped to `prob(v)` and `decrease(v)`.
 * `prob(v)`: The minimum probability of exit or decrease at variant value `v`.
 * `decrease(v)`: The minimum decrease when the loop does not exit.

Caesar checks that `prob` and `decrease` depend only on `v` and variables not modified by the loop.
Their bounds and antitonicity are checked for all nonnegative arguments, including zero, independently of the current variant value.
Any assumptions on unchanged parameters must follow from `I`.
The variant may be zero while the loop is active and positive after exit.

:::warning[Manual checks]

Check that sampling distributions are valid, for example `0 <= p <= 1` for `flip(p)`.
The body must encode a probabilistic program; arbitrary HeyVL logical statements need not satisfy this assumption.
Caesar does not check all of these requirements.
If Caesar warns about a `havoc` domain, also check that it is finite.

:::

The loop body must not contain angelic or additive choice, `cohavoc`, `havoc` over infinite domains, procedure calls, or uninitialized loop-local declarations.
Caesar warns on `havoc` if it cannot prove that each variable's type is finite.

### Soundness

Under these assumptions, `@ast` under-approximates `wp` for exact loop bodies, supporting sound verification in a `proc`.
Use [`@wp`](./approximations#calculus-annotations) to check the required approximations.
On each bounded range of variant values, conditions 1–2 give uniform positive progress bounds.
Condition 4 bounds the probability of leaving that range, and condition 5 forces eventual exit within it.

<details>
<summary>Differences from the published formulations</summary>

These comparisons use the same `I`, `V`, `prob`, and `decrease`.

Compared with [POPL Theorem 4.1](https://arxiv.org/pdf/1711.03588.pdf#page=7):

- **Function assumptions → conditions 1–2:** Caesar also checks antitonicity at zero; the paper only requires it at positive arguments.
- **(ii), positive active variant:** Caesar omits this condition; condition 5 requires a positive probability of exit when `V = 0`.
- **(iii), progress → condition 5:** the paper requires `V <= v - decrease(v)`; Caesar also counts exit as progress.
- **(iv), bounded complements → condition 4:** with body termination from condition 3, the paper's bound on `H ⊖ V` is equivalent to `awp[Body](V) <= V` by [Lemma B.1](https://arxiv.org/pdf/1711.03588.pdf#page=33).
  Caesar uses the smaller postexpectation `ite(G, V, 0)`, so exit values do not affect the bound.

Compared with [Kaminski's thesis, Theorem 6.8](https://publications.rwth-aachen.de/record/755408/files/755408.pdf#page=149):

- **(b), termination indication:** the thesis requires `!G <==> V == 0` globally; Caesar requires neither direction.
- **(c), superinvariant → condition 4:** the thesis bounds `awp[Body](V)` whenever `G` holds; Caesar bounds `awp[Body](ite(G, V, 0))` only under `I && G`.
- **(d), progress → condition 5:** the thesis requires ordinary decrease; Caesar also counts exit as progress.

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

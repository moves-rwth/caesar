---
sidebar_position: 5
---

# Almost-Sure Termination

_Almost-sure termination_ (AST for short) means that a program terminates with probability one.
In our probabilistic setting, this does not necessarily mean that all executions terminate (we would call that _certain termination_), but only that the expected value to reach a terminating state is one.
In terms of weakest pre-expectations, this means that `wp[C](1) = 1` holds for a program `C`.
For a nice overview of details and proof rules that are available in the literature, we refer to [Chapter 6 of Benjamin Kaminski's PhD thesis](https://publications.rwth-aachen.de/record/755408/files/755408.pdf#page=139).[^1]

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
        }
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
        post ?(G(vars) ==> V(vars) > 0]
    {}
    ```

    </p>
    </details>
5. For states fulfilling the invariant `I`: `V` is a `wp`-superinvariant of `while G { Body }` with respect to `V`, i.e. in expectation the variant does not increase after one loop iteration [^1]
    <details>
    <summary>HeyVL Encoding</summary>
    <p>

    ```heyvl
    @wp
    coproc V_wp_superinvariant(init_vars: ...) -> (vars: ...)
        pre ?(!I(init_vars))
        pre V(init_vars)
        post V(vars)
    {
        vars = init_vars // set current state to input values
        if G {
            Body
        }
    }
    ```

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

By applying the `@ast` annotation to a loop, Caesar will check the above requirements for a given invariant, variant, probability and decrease function.
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

You can see all five parameters are passed to the `@ast` annotation in sequence:

 * `invariant`: The Boolean invariant. Has to hold before the loop, be maintained in each iteration, and holds after the loop.
 * `variant`: The variant of type `UReal`.
 * `variable`: The free variable `v` in `prob(v)` and `decrease(v)` for their respective parameters.
 * `prob(v)`: Given a value of the variant `v`, give the probability of a decrease.
 * `decrease(v)`: Given a value of the variant `v`, give the amount of the decrease that happens with probability `prob(v)`.


:::warning

While the paper's proof rule supports (demonic and countable) nondeterminism, Caesar's implementation does not at this moment.
Users must manually ensure that no nondeterminism is present in the program.

The implementation might be extended in the future to support nondeterminism.
Refer to [Section 8.1 of the paper](https://dl.acm.org/doi/pdf/10.1145/3158121#page=25) for more details.

:::

[^1]: Note that the version of the "new proof rule for almost-sure termination" in Benjamin Kaminski's PhD Thesis Theorem 6.8 is slightly different from the one in the published paper at POPL 2018. We use a modified version of the latter.

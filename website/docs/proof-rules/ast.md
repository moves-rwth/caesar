---
sidebar_position: 5
---

# Almost-Sure Termination

_Almost-sure termination_ (AST for short) means that a program terminates with probability one.
In our probabilistic setting, this does not necessarily mean that all executions terminate (we would call that _certain termination_), but only that the expected value to reach a terminating state is one.
In terms of weakest pre-expectations, this means that `wp[C](1) = 1` holds for a program `C`.
For a nice overview of details and proof rules that are available in the literature, we refer to [Chapter 6 of Benjamin Kaminski's PhD thesis](https://publications.rwth-aachen.de/record/755408/files/755408.pdf#page=139).[^1]

:::info

In this documentation, we'll refer to almost-sure termination as probability of termination _from all initial states_.
This is often called _universal almost-sure termination_.
However, all definitions and proof rules can be refined to a subset of all possible initial states.

:::

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

## A New Proof Rule for Almost-Sure Termination (`@ast` Annotation)

Caesar supports the _"new proof rule for almost-sure termination"_ by McIver et al. as a built-in encoding.
You can find the [extended version of the paper on arxiv](https://arxiv.org/pdf/1711.03588.pdf).
The paper was [published at POPL 2018](https://dl.acm.org/doi/10.1145/3158121).

The proof rule is based on a real-valued _loop variant_ (also known as _super-martingale_) that decreases randomly with a certain probability in each iteration by a certain amount.
The latter two quantities are specified by user-provided _decrease_ and _probability_ functions.
Additionally, a Boolean _invariant_ must also be specified.
It allows to limit the set of states on which almost-sure termination is checked.

### Usage

Below is the encoding of the "escaping spline" example [from Section 5.4 of the paper](https://dl.acm.org/doi/pdf/10.1145/3158121#page=18).

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

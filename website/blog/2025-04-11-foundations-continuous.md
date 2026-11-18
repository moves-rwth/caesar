---
authors: phisch
tags: [publications]
---

# Foundations for Verification of Continuous Programs with Caesar

The paper [_"Foundations for Deductive Verification of Continuous Probabilistic Programs: From Lebesgue to Riemann and Back"_](https://dl.acm.org/doi/10.1145/3720429) by Kevin Batz, Joost-Pieter Katoen, Francesca Randone, and Tobias Winkler was recently published at [OOPSLA 2025](https://2025.splashcon.org/track/OOPSLA).

Before this work, Caesar was able to only verify simple *discrete* probabilistic programs, i.e. programs that only sample from discrete distributions.
This paper lays out the formal foundations for us to verify probabilistic programs that sample from continuous distributions, with support for loops, and conditioning.
One challenge is to integrate the integrals for the expected values that arise from continuous distributions into the deductive verification framework of Caesar.
The key idea is to soundly under- or over-approximate these integrals via [Riemann sums](https://en.wikipedia.org/wiki/Riemann_sum).
In addition to theoretical results such as convergence and completeness of the approach, the paper also provides case studies of continuous probabilistic programs that are encoded in HeyVL and verified with Caesar.

**In this post:**
1. [Encoding Riemann Sums in HeyVL](./2025-04-11-foundations-continuous.md#encoding-riemann-sums-in-heyvl)
2. [Tortoise-Hare Race Example](./2025-04-11-foundations-continuous.md#tortoise-hare-race-example)
3. [Beyond The Continuous Uniform Distribution](./2025-04-11-foundations-continuous.md#beyond-the-continuous-uniform-distribution)


<!-- truncate -->

## Encoding Riemann Sums in HeyVL

:::warning Reusing the encoding

This is a manual encoding of continuous sampling.
Check the [soundness conditions](/docs/getting-started/zoo/tortoise-hare#soundness-conditions) before adapting it to another model.

:::

The HeyVL encoding of the Riemann sum approximation is simple.
Consider sampling the variable `x` from the *continuous* uniform distribution over $[0,1]$.

The original sampling interval $[0,1]$ is divided into $N$ equally sized subintervals, where $N\ge1$.
For example, the following encoding uses $N=8$:
```heyvl
var N: UInt = 8
var x: UReal
var j: UInt = unif(0, 7)
cohavoc x
coassume ?!(j / N <= x && x <= (j+1) / N)
```

We sample a random integer $j$ uniformly from $0$ through $N-1$ using the [built-in `unif` distribution](/docs/stdlib/distributions).
Its bounds must be integer literals, so the code uses `unif(0, 7)`.
The sampled integer $j$ is then used to select the closed subinterval $I = [j/N, (j+1)/N]$.
The `cohavoc` and `coassume` statements take the supremum of the postexpectation over all values $x\in I$, giving an upper approximation on that subinterval.

Finer partitions can give sharper bounds on the expected value, at the cost of larger verification conditions.

The above encodes the Riemann sum over-approximation of the expected value of a function $f$ when sampling uniformly from the continuous interval $[0,1]$.
Formally:

$$
\int_0^1 f(x) \, dx \quad\leq\quad \frac{1}{N} \sum_{j=0}^{N-1} \sup_{x \in [j/N, (j+1)/N]} f(x)
$$

A dual version of the encoding can be used to obtain an *under*-approximation of the expected value.
Simply use `havoc` and `assume` statements instead of `cohavoc` and `coassume`, and use `?(...)` instead of `!?(...)`.

A more detailed explanation can be found in [Section 9.1 of the paper](https://dl.acm.org/doi/pdf/10.1145/3720429#page=21).


## Tortoise-Hare Race Example

[Example 9.2.3 from the paper](https://dl.acm.org/doi/pdf/10.1145/3720429#page=23) models a race between a tortoise and a hare.
As long as the hare did not overtake the tortoise, the hare flips a fair coin to decide whether to move or not.
If the hare decides to move, it samples a distance uniformly at random from $[0, 10]$.
The tortoise always moves exactly one step.
For initial positions $h\le t$, the following HeyVL code encodes a proof that $$\mathrm{wp}\llbracket\texttt{tortoise\_hare}\rrbracket(\texttt{count}) \leq 3.38 \cdot (t - h + 2)~,$$ where $h$ and $t$ are the initial positions of the hare and tortoise, respectively.
Here, we chose the parameter $N = 8$ for the Riemann sum approximation.
The [Tortoise-Hare Race case study](/docs/getting-started/zoo/tortoise-hare) provides the complete checked source and explains the approximation and the meaning of the final-count bound.

```heyvl
@wp
coproc tortoise_hare(init_h: UReal, init_t: UReal) -> (count: UReal)
    pre 3.38*((init_t - init_h) + 2)
    post count
{
    var h: UReal = init_h
    var t: UReal = init_t

    count = 0

    @invariant(ite(h <= t, count + 3.38*((t-h) + 2), count))
    while h <= t {
        var choice: Bool = flip(0.5)
        if choice {

            // -------------------------------------------
            // Over-approximating the continuous sampling:
            //      inc = unif[0,1]
            //
            var inc: UReal
            var N: UInt = 8
            var j: UInt = unif(0, 7) // discrete sampling
            cohavoc inc
            coassume ?!(j / N <= inc && inc <= (j+1) / N)
            // -------------------------------------------

            inc = 10 * inc
            h = h + inc
        } else {}

        t = t + 1
        count = count + 1
    }
}
```

[Section 9.3 of the paper](https://dl.acm.org/doi/pdf/10.1145/3720429#page=24) contains a detailed experimental evaluation with more examples.
[An associated artifact is available on Zenodo](https://doi.org/10.5281/zenodo.15175355).

## Beyond The Continuous Uniform Distribution

In the paper, only a statement to sample from the continuous uniform distribution is provided.
However, as their [*Remark 1*](https://dl.acm.org/doi/pdf/10.1145/3720429#page=10) states, this does not limit expressiveness.
By applying the [inverse transform sampling method](https://en.wikipedia.org/wiki/Inverse_transform_sampling), any continuous distribution can be sampled.
[This paper](https://link.springer.com/chapter/10.1007/978-3-030-55089-9_3) by Marcin Szymczak and Joost-Pieter Katoen contains some examples of how to sample from e.g. the normal distribution.

---
title: "Highly Incremental: A Simple Programmatic Approach for Many Objectives"
authors: phisch
tags: [publications]
---

Our new paper _"Highly Incremental: A Simple Programmatic Approach for Many Objectives"_ by Philipp Schröer and Joost-Pieter Katoen presents a one-fits-all approach for quantitative objectives on probabilistic programs, applicable to verification with Caesar.

The paper [will be presented](https://conf.researchr.org/details/fm-2026/fm-2026-research-paper/31/Highly-Incremental-A-Simple-Programmatic-Approach-for-Many-Objectives) at [_The 27th International Symposium on Formal Methods (FM 2026)_](https://conf.researchr.org/home/fm-2026) in Tokyo, Japan.

A preprint with a detailed appendix of proofs and case studies is available on arXiv:
[_"Highly Incremental: A Simple Programmatic Approach for Many Objectives (Extended Version)"_](https://arxiv.org/abs/2603.02405).

In this post, we:
1. [show how `reward` statements model runtime and related quantities](/blog/2026/03/04/highly-incremental#programmatic-reward-modeling).
2. [explain why verification of variance is difficult for runtime objectives](/blog/2026/03/04/highly-incremental#a-challenge-higher-moments-of-runtimes).
3. [introduce our sound program transformation for these objectives](/blog/2026/03/04/highly-incremental#programmatic-reward-transformations), including **higher moments**, **tail probabilities**, **CDFs**, **expected excess**, and **moment-generating functions**.
4. [work through a Caesar example for the second moment of runtime](/blog/2026/03/04/highly-incremental#example-with-caesar-second-moment-of-runtime).

## Programmatic Reward Modeling

The paper explores what can be encoded into probabilistic programs with `reward` statements, which collect a certain quantity &mdash; _rewards_ &mdash; during execution.
We then consider _expected rewards_, i.e. the expected value of rewards collected over the distribution of program executions.
This approach enables more applications for Caesar's weakest pre-expectation reasoning out-of-the-box.

<!-- truncate -->

We call this technique _programmatic reward modeling_ and start with simple examples.
First, we observe that we do not need dedicated `post`-expectation specifications, but can encode _rewards on termination_ by simply writing a `reward` statement at the end of the program.
From there, it is simple to generalize to _runtime modeling_ and the more general _resource consumption modeling_ by adding `reward` statements in between program statements.

By using auxiliary variables that are not used in the concrete program's execution &mdash; called _ghost variables_ &mdash;, we can reason about more objectives.
_Discounting_ (future rewards matter less), _step-indexed_ (reward at time point $N$), and even the _expected number of visits_, _first visit times_, and _first return times_, can all be modeled this way too.

## A Challenge: Higher Moments of Runtimes

Expected runtime alone is often not enough: two programs can have the same expected runtime but very different runtime variability.
To capture that difference, we need higher moments: the _second moment_ $\mathbb{E}(\tau^2)$ captures the expected value of the square of the runtime, and the _variance_ is $\mathbb{E}(\tau^2) - \mathbb{E}(\tau)^2$.

Consider the three different runtime encodings in the following figure.

<figure>
<div
  style={{
    display: "grid",
    gridTemplateColumns: "repeat(3, 1fr)",
    gap: "2rem",
    alignItems: "start",
  }}
>

  <div>
    <h4 style={{ textAlign: "center" }}>
      (a) Termination reward (runtime)
    </h4>

```heyvl
var tau: UInt = 0
while b {
  tau = tau + 1
  S'
}
reward tau
```

  </div>

  <div>
    <h4 style={{ textAlign: "center" }}>
      (b) Termination reward (squared runtime)
    </h4>

```heyvl
var tau: UInt = 0
while b {
  tau = tau + 1
  S'
}
reward tau * tau
```

  </div>

  <div>
    <h4 style={{ textAlign: "center" }}>
      (c) Incremental reward (runtime)
    </h4>

```heyvl
while b {
  reward 1
  S'
}
```

  </div>

</div>

<figcaption>
  Three runtime encodings with reward statements.
  (a) and (b) collect `tau` and `tau * tau` on termination, while (c) collects `reward 1` incrementally at each loop iteration.
</figcaption>
</figure>

For runtime objectives, only (c) is sound for all programs.
This becomes clear for `b = true` (i.e. `while true`), which has infinite runtime.
This is correctly captured by (c), which has an infinite expected reward, while (a) and (b) have an expected reward of $0$ because the final `reward` statement is never reached.

However, we'd like to retain the simplicity of being able to transform reward models like (a) into (b) to analyze higher moments.
This is the key motivation for our programmatic reward transformations, which we introduce next.

## Programmatic Reward Transformations

We introduce _programmatic reward transformations_.
Instead of inventing a separate reward model for each objective, we start from a sound incremental reward model and transform it systematically.

Given a program $P$ and a monotonic function $f$ between rewards, our transformation constructs a program $\mathcal{T}_f(P)$ whose expected reward is transformed by $f$.
For higher moments, we choose $f(\tau) = \tau^k$, so an expected reward $\mathbb{E}(\tau)$ becomes $\mathbb{E}(\tau^k)$.
This directly captures quantities such as the second moment, which is useful for analyzing runtime variance.

The idea is shown in the following sketch:

<figure>
<div
  style={{
    display: "grid",
    gridTemplateColumns: "repeat(2, minmax(0, 1fr))",
    gap: "2rem",
    alignItems: "start",
  }}
>

  <div>
    <h4 style={{ textAlign: "center" }}>
      (a) Original incremental reward model
    </h4>

```heyvl
while b {
  reward r
  S'
}
```

  </div>

  <div>
    <h4 style={{ textAlign: "center" }}>
      (b) Transformed model $\mathcal{T}_f(P)$
    </h4>

```heyvl
var tau: EUReal = 0
while b {
  reward f(tau + r) - f(tau)
  tau = tau + r
  S'
}
```

  </div>

</div>

<figcaption>
  Sketch of the transformation from a base reward model $P$ to $\mathcal{T}_f(P)$.
  A ghost variable `tau` tracks accumulated reward, and each transformed step adds the increment induced by $f$.
  For $f(\tau)=\tau^2$, this yields a sound encoding of second moments.
</figcaption>
</figure>

The transformation carefully constructs _incremental rewards_ so that the result is correct even for programs that do not terminate with probability $1$, in particular diverging programs that accumulate infinite rewards.
We show soundness of the transformation formally in the paper.

We also show how our program transformation recovers other objectives: **higher moments** via $f(\tau) = \tau^k$, **threshold/tail probabilities** via $f_N(\tau) = [\tau \ge N]$, **CDF values** by complement (equivalently via $f_N(\tau) = [\tau \le N]$), **expected excess** via $f_N(\tau) = \tau \ominus N$, and **moment-generating functions** via $f_\lambda(\tau) = \exp(\lambda \tau)$.

Finally, we show how our transformation can be generalized to _multi-reward settings_, where the program keeps track of multiple rewards structures like runtimes and memory usage.
This enables objectives like **expected runtime-memory products**, relevant for many cloud billing models.

## Example with Caesar: Second Moment of Runtime

Consider a simple program that sends requests to a database.
These requests can fail with some probability, in which case the program retries until it succeeds.

The following HeyVL program succeeds with probability $0.5$ on each try and models runtime with `reward 1` per retry.
Using the `@invariant` annotation and the `pre`-attribute on the `coproc`, we show that the expected runtime is at most $2$.

```heyvl
coproc retry_expected_runtime() -> (done: Bool)
    pre 2
    post 0
{
    done = false
    @invariant([!done] * 2)
    while !done {
        reward 1
        done = flip(0.5)
    }
}
```

Contrast this with the following program that succeeds with probability $\frac{2}{3}$, but incurs an additional constant cost of $0.5$ at startup.
The expected value is also $2$.
So first moments cannot distinguish the two programs.

```heyvl
coproc retry2_expected_runtime() -> (done: Bool)
    pre 2
    post 0
{
    done = false
    reward 0.5
    @invariant([!done] * 1.5)
    while !done {
        reward 1
        done = flip(2/3)
    }
}
```

These programs have different runtime distributions.
Applying our program transformation with $f(\tau) = \tau^2$ lets us analyze the second moment, $\mathbb{E}(\tau^2)$.

We introduce a ghost variable `tau` to track the original runtime and increment the reward by the second-moment change at each step.
This makes the transformed program's total reward equal to the original program's second moment, even for non-terminating executions.

Below is the transformed program for the first example.
Its second moment is $6$, and the per-step reward increment is $(\tau + 1)^2 - \tau^2 = 2 \cdot \tau + 1$.

```heyvl
coproc retry_second_moment() -> (done: Bool)
    pre 6
    post 0
{
    done = false
    var tau: UInt = 0
    @invariant([!done] * (6 + 4 * tau))
    while !done {
        reward (tau + 1) * (tau + 1) - tau * tau
        tau = tau + 1
        done = flip(0.5)
    }
}
```

For the second example, the second moment is $4.75$, so the runtime distribution is more concentrated around its mean.

```heyvl
coproc retry2_second_moment() -> (done: Bool)
    pre 4.75
    post 0
{
    done = false
    var tau: UReal = 0.5
    reward 0.25
    @invariant([!done] * (4.5 + 3 * (tau - 0.5)))
    while !done {
        reward (tau + 1) * (tau + 1) - tau * tau
        tau = tau + 1
        done = flip(2/3)
    }
}
```

Both programs have expected runtime $2$, but their variances are $6 - 2^2 = 2$ and $4.75 - 2^2 = 0.75$, so the second program is more predictable.

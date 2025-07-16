---
sidebar_position: 6
---

# Positive Almost-Sure Termination

_Positive almost-sure termination_ (PAST for short) means that a program [terminates almost-surely](ast) and the expected runtime to termination is finite.
In terms of the [expected runtime calculus](calculi), this means that `ert[C](0) < ∞` holds for a program `C`.

In Caesar, there are several ways to prove PAST:

```mdx-code-block
import TOCInline from '@theme/TOCInline';

<TOCInline toc={toc} maxHeadingLevel="2" />
```

## Upper Bounds on ert

The simplest way to prove positive almost-sure termination is by proving a finite upper bound $g$ on the expected runtime of a program using the expected runtime calculus, i.e. $\mathrm{ert}\llbracket C \rrbracket(0) \leq g$.
The upper bound $g$ must be finite: for every state $s$, $g(s) < \infty$ must hold.

Upper bounds on the expected runtime can be shown with [Park induction](./induction.md).

## PAST from Ranking Superinvariants

Caesar supports proofs of PAST using *ranking superinvariants* - also called *ranking supermartingales*.
We use the formulation of [Theorem 6.3 in Kaminski's PhD thesis](http://publications.rwth-aachen.de/record/755408/files/755408.pdf#page=143).
This theorem is a the wp-version of either
 * Theorem 4 of [„*Probabilistic Program Analysis with Martingales*“](https://doi.org/10.1007/978-3-642-39799-8_34) by Chakarov and  Sankaranarayanan (CAV 2013).
 * Theorem 5.6 of [„*Probabilistic Termination: Soundness, Completeness, and Compositionality*“](https://doi.org/10.1145/2775051.2677001) by Fioriti and Hermanns (POPL 2015).

Ranking superinvariants are supported via Caesar's built-in `@past` annotation on `while` loops.

### Formal Theorem

Let `while G { Body }` be a loop whose `Body` universally certainly terminating.
Let
 * `I` is an expression of type `UReal` called *ranking superinvariant*.
 * `epsilon` is a positive real number.
 * `K` is un upper bound on the change.
such that the following conditions hold:
 1. $[\neg G] \cdot I \leq K$,
 2. $[G] \cdot K \ll [G] \cdot I + [\neg G]$,
 3. $[G] \cdot \mathrm{wp}\llbracket Body \rrbracket(I) \leq [G] \cdot (I - \epsilon)$,[^literature-condition-3]

Then, `while G { Body }` terminates universally positively almost-surely, i.e. `ert[while G { Body }](0) < ∞`.

### Usage

Consider the following example, where we have a loop that decrements a variable `x` with probability `0.5` in each iteration.
The loop terminates with probability `1` and the expected number of iterations is finite.
We show this by using the `@past` annotation on the loop.

```heyvl
proc main(init_x: UInt) -> (x: UInt)
{
    var prob_choice: Bool
    x = init_x
    @past(
        /* invariant: */ x + 1,
        /* epsilon:   */ 0.5,
        /* K:         */ 1)
    while 0 < x {
        prob_choice = flip(0.5)
        if prob_choice {
            x = x - 1
        } else {}
    }
}
```

**Inputs:**
- `invariant`: The quantitative invariant which should decrease.
- `epsilon`: The expected decrease of the invariant after an iteration.
- `K`: The maximum change of the invariant in one iteration.

### Relation to the ert Calculus Approach

As Kaminski states in his thesis (p. 130), the PAST rule (Theorem 6.3) "is also very similar to and basically equivalent to [Park induction on ert]".
"The main difference is that [Park induction on ert] needs less preconditions and always uses $\epsilon = 1$, while still being complete."

[^literature-condition-3]: Kaminski writes $\Phi_0(I) \leq [G] \cdot (I - \epsilon)$ instead for condition 3, where $\Phi_0$ is the loop-characteristic function with respect to postexpectation $0$. Our condition is equivalent to this, but simplified.

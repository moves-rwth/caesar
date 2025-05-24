---
sidebar_position: 6
---

# Positive Almost-Sure Termination

_Positive almost-sure termination_ (PAST for short) means that a program [terminates almost-surely](ast) and the expected runtime to termination is finite.
In terms of the [expected runtime calculus](calculi), this means that `ert[C](0) < ∞` holds for a program `C`.

## Finite Expected Runtime

The simplest way to prove positive almost-sure termination is by proving a finite upper bound $g$ on the expected runtime of a program.
The upper bound $g$ must be finite: for every state $s$, $g(s) < \infty$ must hold.

Upper bounds on the expected runtime can be shown with [Park induction](./induction.md).

## PAST from Ranking Superinvariants

Caesar supports proofs of "PAST from Ranking Superinvariants" by [Chakarov and Sankaranarayanan (CAV 2013)](https://doi.org/10.1007/978-3-642-39799-8_34) as a built-in encoding with the `@past` annotation on `while` loops.

### Formal Theorem

:::danger[TODO]
:::

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
        /* k:         */ 1)
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
- `k`: The maximum change of the invariant in one iteration.

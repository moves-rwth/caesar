---
sidebar_position: 4
---

# ω-Invariants

*ω-invariants* ("omega-invariants") allow proving lower bounds on the `wp`/`ert`-semantics of loops and upper bounds on the `wlp`-semantics.
In essence, they are a proof rule that encodes an induction on the fixpoint iteration semantics of a loop.

The proof rule is explained well following [Definition 5.3 of Benjamin Kaminski's PhD thesis](http://publications.rwth-aachen.de/record/755408/files/755408.pdf#page=122).

Caesar supports ω-invariants as a built-in encoding with the `@omega_invariant` annotation on `while` loops.

## Usage

The example below shows how we can use an ω-invariant to prove a lower bound on the `ert`-semantics of a loop.
The loop decrements a variable `x` in each iteration, and we want to show that the expected runtime to termination is at least `x`.

```heyvl
@ert proc omega(init_x: UInt) -> (x: UInt)
    pre init_x
    post 0
{
    x = init_x

    @omega_invariant(n, [x<=n] * x)
    while 0 <= x {
        tick 1
        x = x - 1
    }
}
```

**Inputs:**
- `n`: A variable name for the count that shows up in the invariant.
- `invariant`: An invariant in the program variables and `n` that lower bounds the fixpoint iteration in every step.

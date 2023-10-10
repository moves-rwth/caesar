---
title: Loop Unrolling
description: Loop unrolling, also known as bounded model checking.
sidebar_position: 2
---

# Loop Unrolling (aka Bounded Model Checking)

*Loop unrolling*, also known as *bounded model checking*, replaces a `while` loop by a fixed number of iterations `k`.


:::danger

Loop unrolling is a technique for *refuting* verification, but can make successful verification *unsound*.
The encodings approximate in the opposite direction to the HeyVL context (`proc`/`coproc`).
Proceed very carefully.

:::

## Usage

A `while` loop is annotated by the `@unroll(k, terminator)` annotation where `k` is a number literal and `terminator` is an expression of type `EUReal`.
 
Usually, one chooses the `terminator` to encode the loop unrolling such that it
 * over-approximates greatest fixed-point semantics when in lower-bound contexts (`procs`);
    * commonly `1` for the one-bounded wlp semantics,
    * or `\infty` for the unbounded expectation-based semantics.
 * under-approximates least fixed-point semantics when in upper-bound contexts (`coprocs`);
    * commonly `0` for expectation-based semantics (wp, ert).

See the [section on soundness](#soundness) below.

## Example

In the following example, we use loop unrolling to *under-approximate* least fixed-point semantics in an *upper-bound context* (`coproc`). 
This means we know that if verification of an upper bound *fails*, then it cannot be a valid upper bound.
On the other hand, if verification succeeds, then we know nothing!

```heyvl
coproc geo1_bmc(init_c: UInt) -> (c: UInt)
    pre init_c + 0.99
    post c
{
    c = init_c
    var cont: Bool = true
    @bmc(12, 0) // k = 12, terminator = 0
    while cont {
        var prob_choice: Bool = flip(0.5)
        if prob_choice { cont = false } else { c = c + 1 }
    }
}
```
It is replaced by its unfolding, with an `assert 0` at the end of the `k = 12` loop iterations are exceeded.
```heyvl
if cont {
    ... body ...
    if cont {
        ... body ...
        if cont {
            ... more unfoldings ...
                assert 0
        }
    }   
}
```

Trying to verify `geo1_bmc` will yield a counter-example to verification.
Because this is loop unrolling, it is a *true counter-example* to `init_c + 0.99` being an upper bound.
On the other hand, if you change `k = 11`, then the program verifies.
But this tells you nothing about the actual program semantics.


## Soundness
 
See [_Latticed k-Induction with an Application to Probabilistic Programs_](https://link.springer.com/chapter/10.1007/978-3-030-81688-9_25) (CAV 2021) for more information on the theory of *bounded model checking* on probabilistic programs.

One needs to be very careful in choosing the `terminator` such that `@unroll` actually approximates the correct fixed-point corresponding to the desired semantics (see [Usage](#usage)).

Notice that you **cannot** *under-approximate a greatest fixed-point semantics* or *over-approximate a least fixed-point semantics* with loop unrolling, in contrast to the other proof rules such as [induction](./induction.md).

---
sidebar_position: 1
description: Procedure annotations for soundness of proof rules.
---

# Calculus Annotations

```mdx-code-block
import Link from '@docusaurus/Link';
```

Caesar supports annotations on procedures to specify a desired calculus to use.
By using these annotations, Caesar will help to check that only proof rules are used that are sound for that chosen calculus.

Right now, Caesar supports:
 * `@wp`: The **weakest pre-expectation calculus** that operates on non-negative real numbers and infinity.
    - It corresponds to expected values of probabilistic programs where non-termination yields expected value zero.
    - Correspondingly, it uses *least* fixpoint semantics for loops.
 * `@wlp`: The **weakest *liberal* pre-expectation calculus** that operates on real numbers in the closed interval from zero to one.
    - It corresponds to expected values of probabilistic programs where non-termination yields expected value 1.
    - It uses *greatest* fixpoint semantics for loops.
 * `@ert`: The **expected runtime calculus** for reasoning about expected runtimes or expected resource consumption of probabilistic programs.
    - The calculus is basically the same as the weakest pre-expectation calculus, with a lot of additonal `+ 1`s everywhere. In HeyVL, this corresponds to a bunch of `tick 1` statements.


The formal details of these three calculi are presented very nicely in [Benjamin Kaminski's PhD thesis](https://publications.rwth-aachen.de/record/755408/files/755408.pdf).

:::caution

The calculus annotations do not automatically guarantee that your HeyVL file encodes your verification problems in a sound way.
For one, there are some conditions that are not (yet) checked by Caesar's implementation.
See the section [What Is *Not* Checked](#what-is-not-checked) for more information.

:::

## Usage

Simply add the respective annotation to your `proc` or `coproc`.

For example, the following `proc` declaration will **not compile** because [induction](./induction.md) is not a sound proof rule to be used with `wp` reasoning about lower bounds.
A valid proof rule would be [ω-invariants](./omega-invariants.md).

```heyvl
@wp
proc main() -> () {
    var x: UInt
    @invariant(x)
    while 1 <= x {
        x = x - 1
    }
}
```

Each [built-in proof rule](./README.md) specifies their soundness theorem on their own documentation page (see the *"Soundness"* sections).

## Soundness Overview of Proof Rules

So, what are the proof rules that can be used to reason about which calculus and about which direction?
The following table contains combinations of *sound approximation* combinations, i.e. if the program with the proof rule verifies, then the original program with the true greatest/least fixpoint semantics satisfies the same specification as well.
The documentation pages on the individual proof rules explain the soundness guarantees in more detail.

<table>
    <thead>
        <tr>
            <td>Proof Rule</td>
            <td><code>@wp</code></td>
            <td><code>@wlp</code></td>
            <td><code>@ert</code></td>
        </tr>
    </thead>
    <tbody>
        <tr>
            <td><Link to="./induction">(k)-Induction</Link></td>
            <td>Overapproximation (<code>coproc</code>)</td>
            <td>Underapproximation (<code>proc</code>)</td>
            <td>Overapproximation (<code>coproc</code>)</td>
        </tr>
        <tr>
            <td><Link to="./unrolling">Loop Unrolling</Link></td>
            <td>Underapproximation (<code>proc</code>)</td>
            <td>Overapproximation (<code>coproc</code>)</td>
            <td>Underapproximation (<code>proc</code>)</td>
        </tr>
        <tr>
            <td><Link to="./omega-invariants">ω-invariants</Link></td>
            <td>Underapproximation (<code>proc</code>)</td>
            <td>Overapproximation (<code>coproc</code>)</td>
            <td>Underapproximation (<code>proc</code>)</td>
        </tr>
    </tbody>
</table>

The following proof rules implicitly assume that you do not approximate in your while loops, but encode *exact* `wp`/`ert` semantics of your program.
This is because these proof rules implicitly do both lower and upper bounds checks on the loop body and thus the exact loop body semantics are required.

<table>
    <thead>
        <tr>
            <td>Proof Rule</td>
            <td><code>@wp</code></td>
            <td><code>@wlp</code></td>
            <td><code>@ert</code></td>
        </tr>
    </thead>
    <tbody>
        <tr>
            <td><Link to="./ast">Almost-Sure Termination Rule</Link></td>
            <td>Exact (<code>proc</code>)</td>
            <td>Not Applicable</td>
            <td>Not Applicable</td>
        </tr>
        <tr>
            <td><Link to="./past">Positive Almost-Sure Termination Rule</Link></td>
            <td>Not Applicable</td>
            <td>Not Applicable</td>
            <td>Exact (<code>coproc</code>)</td>
        </tr>
        <tr>
            <td><Link to="./ost">Optional Stopping Theorem</Link></td>
            <td>Exact (<code>proc</code>)</td>
            <td>Not Applicable</td>
            <td>Not Applicable</td>
        </tr>
    </tbody>
</table>

## What Is *Not* Checked By Caesar {#what-is-not-checked}

HeyVL is designed as an intermediate verification language and so it allows some dangerous features on purpose.
See our [OOPSLA '23 paper](../publications.md#oopsla-23) for more information.
However, some items from the list below might also be disallowed in the future.

 * You can easily introduce contradictions that lead to unsoundness.
    * E.g. `assume ?(false)` can be used in `proc`s to make everything verify trivially.
    * [Unsoundness may come from axioms with contradictions](../heyvl/domains.md#axioms-as-assumptions).
 * `tick` statements may be used with `@wp` and `@wlp`, and it is not checked that a `tick` statement actually occurs in an `@ert` procedure.

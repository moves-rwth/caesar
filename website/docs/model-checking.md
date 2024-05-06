---
sidebar_position: 7
description: Caesar can export models to the JANI format.
---

# Model Checking

Caesar has some support to export probabilistic programs written in (an executable fragment of) HeyVL to [the *jani-model* format](https://jani-spec.org/).
The JANI project defines exchange formats for quantitative model checking problems (and more).

[Executable HeyVL programs](#supported-programs) are essentially programs without verification statements, where therefore the Markov chain semantics is clearly defined and the program can be executed forwards in a step-by-step fashion.

After exporting HeyVL programs to JANI, we can use our favorite probabilistic model checkers to calculate and/or verify expected rewards.
For now, we have only tested with the [model checker *Storm*](https://www.stormchecker.org/).

:::caution

This feature is still under development.
There are sure to be bugs and missing functionality.
The encoding is sure to change in the near future.

:::

## Usage

For a simple example, consider the HeyVL program below.


```heyvl
@wp
proc geo_mc(init_c: UInt) -> (c: UInt, cont: Bool)
    pre ?(true)
    post [!cont]
{
    c = init_c
    cont = true
    while cont && c <= 20 {
        var prob_choice: Bool = flip(0.5)
        if prob_choice { cont = false } else { c = c + 1 }
    }
}
```

To export JANI files for the model checker, simply run Caesar with the `--jani-dir DIR` option to instruct it to save all translateable (co)procs to `.jani` files in the directory `DIR`:

```bash
caesar example.heyvl --jani-dir DIR
```

We use the probabilistic model checker [Storm](https://www.stormchecker.org).
Running Storm on the produced file gives us the optimal value.[^1]
Procedure inputs to are translated to JANI's *constants*, and must be given to Storm via the flag `--constants init_c=0` (any other initial value can be chosen).

```bash
$ storm --jani DIR/FILE.jani -jprop reward --exact --sound --constants init_c=0
```

Part of the output:

```
Model checking property "reward": R[exp]{"reward"}min=? [C] ...
Result (for initial states): 2097151/2097152 (approx. 0.9999995232)
```

:::note

In this particular case, we can obtain the optimal lower bound in Caesar by using the [unrolling proof rule](./proof-rules/unrolling.md).
The annotation `@unroll(22, 0)` for unrolling depth 22 finds the fixpoint in this case.
But this is only exact if we can bound the number of loop iterations statically.

:::

## Supported Programs

The currently implemented translation only supports a subset of the executable fragment of HeyVL.

### Supported Declarations

 * `proc` and `coproc` specifications with:
    * Inputs and output declarations,
    * `pre` declarations that are only Boolean conditions of the form `?(b)`.
    * `post` declarations (arbitrary operands).

### Supported Statements

In the body, statements:

 * [Blocks](./heyvl/statements.md#blocks),
 * [Variable declarations](./heyvl/statements.md#variable-declarations) with initializers,
 * Assignments with pure expressions,
 * Sampling from [Bernoulli distributions](./stdlib/distributions.md#bernoulli) with assignments,
 * [`assert` statements](./heyvl/statements.md#assert-and-assume) with Boolean condition of the form `assert ?(b)`,
 * [`reward` statements](./heyvl/statements.md#reward-formerly-tick),
 * [Binary demonic choices](./heyvl/statements.md#nondeterministic-choices) in `proc`s,
 * [Binary angelic choices](./heyvl/statements.md#nondeterministic-choices) in `coproc`s,
 * [If-then-else statements](./heyvl/statements.md#boolean-choices),
 * While loops
    * They are always assumed to have **least fixed-point semantics** when model-checking.[^2] That means we just accumulate rewards over all terminating executions in the Markov chain, as opposed to adding `1` or `\infty` if there is a diverging path.
 * Annotations, in particular [proof rule annotations](./proof-rules/), will be ignored.

### Supported Types

The supported types of values are:

 * [`Bool`](./stdlib/booleans.md),
 * [`UInt`](./stdlib/numbers.md#uint),
 * [`Int`](./stdlib/numbers.md#int),
 * [`UReal`](./stdlib/numbers.md#ureal),
 * [`Real`](./stdlib/numbers.md#real).

Make sure to check in your model checker's documentation how these types are realized.
For example, [Storm](https://www.stormchecker.org) assumes 32-bit numbers by default for unbounded integer types.

[`EUReal`](./stdlib/numbers.md#eureal) values are currently only supported as values in `pre`/`post` declarations and in `assert` statements.
The value `\infty` cannot be explicitly represented in JANI, therefore `EUReal` expressions that go beyond the specific supported verification constructs are not supported.

### Not Supported

In particular, the following constructs are *not* supported:
 * Calls to uninterpreted functions or to `proc`s/`coproc`s,
 * Uninitialized variable declarations or `havoc`/`cohavoc` statements,
 * Quantitative verification statements such as `assume`/`assert` in arbitrary locations.
 * Distributions other than Bernoulli are not yet supported.
 * [User-defined domains](./heyvl/domains.md), axioms will be ignored.


[^1]: We use the `--exact` and `--sound` flags to ensure that Storm is forced to use exact arithmetic and only sound algorithms to produce the solution. Consult your chosen model checker's documentation to see which guarantees they give.
[^2]: As far as we can tell, encoding greatest fixpoint/weakest *liberal* pre-expectation semantics is not possible with a single JANI property.
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

### Generating JANI Files

To export JANI files for the model checker, simply run Caesar with the `--jani-dir DIR` option to instruct it to save all translateable (co)procs to `.jani` files in the directory `DIR`:

```bash
caesar example.heyvl --jani-dir DIR
```

The output JANI files will have the following structure that you can use:
 * Properties:
   * `reward`: This is the expected value of the verification conditions (cf. [Statements](./heyvl/statements.md)).
   * `diverge_prob`: The probability of not reaching the end of the (co)proc.
   * `can_diverge`: Boolean property whether the program has a path that does not reach the end of the (co)proc.[^5]
 * Constants:
   * One constant for each input variable of the (co)proc (constant has same name as variable).


### Model Checking with Storm

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

:::info Infinite-State Programs

Model checkers usually work with finite-state models, therefore programs with an infinite state space often just lead to nontermination of the model checker.
 * **Bounded model checking:** Since [PR #521](https://github.com/moves-rwth/storm/pull/521) (nightly only), Storm can be used with a state limit so that the model generation will just stop at some number of states. Use the `--build:state number <limit>` command-line flag.
 * **Parametric models:** If the program has input variables, [Storm's parametric model checking](https://www.stormchecker.org/documentation/usage/running-storm-on-parametric-models.html) may be of interest.

:::

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
 * [Sampling from distributions](./stdlib/distributions.md),
 * [`reward` statements](./heyvl/statements.md#reward-formerly-tick),
 * In `proc`s:
   * [`assert` statements](./heyvl/statements.md#assert-and-assume) with Boolean condition of the form `assert ?(b)`,
   * [Binary demonic choices](./heyvl/statements.md#nondeterministic-choices),
 * In `coproc`s:
   * [Binary angelic choices](./heyvl/statements.md#nondeterministic-choices),
 * [If-then-else statements](./heyvl/statements.md#boolean-choices),
 * While loops (with least-fixed point semantics &mdash; [see below for semantics details](#loop-semantics)),
 * Annotations, in particular [proof rule annotations](./proof-rules/), will be ignored.

#### Loop Semantics

:::warning

In the JANI translation, while loops are always assumed to have **least fixed-point semantics** when model-checking.[^2]
That means we just accumulate total expected rewards over all terminating executions in the Markov chain.
This corresponds to [wp/ert](./proof-rules/calculi.md) semantics.

:::

Notice that in `proc`s, this is different from the default behavior of Caesar's [proof rules such as induction](./proof-rules/induction.md).
They would assume greatest fixed-point (wlp) semantics in `proc`s.
We recommend always adding the [`@wp` or `@ert` annotations](./proof-rules/calculi.md) to your `proc`/`coproc`.
They instruct Caesar to enforce that sound proof rules for least fixed-point semantics are being used.

If you want [one-bounded wlp semantics](./proof-rules/calculi.md) (greatest fixed-points), then you can use the generated property `diverge_prob` to obtain the probability of divergence.
Then the result should be the sum of the `reward` and `diverge_prob` properties (Storm: `-jprop reward,diverge_prob`).[^3]

If you want *unbounded* greatest fixed-point semantics, then you can use the generated property `can_diverge` to check whether there is a diverging path.
Then the result is `\infty` if `can_diverge` is `true`, otherwise the result is `reward`.[^4]
This property is currently not supported by Storm.[^5]

We intentionally avoid using the *reachability reward* properties (i.e. setting the `reach` property of `ExpectedValueExpression` in JANI) as it will assign the expected reward `\infty` to any state from which goal states are not reachable with probability 1.
If the program is not AST, then this does not correspond to either least or greatest fixpoint semantics weakest pre-expectation style semantics that we know of.

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
 * [User-defined domains](./heyvl/domains.md), axioms will be ignored.


[^1]: We use the `--exact` and `--sound` flags to ensure that Storm is forced to use exact arithmetic and only sound algorithms to produce the solution. Consult your chosen model checker's documentation to see which guarantees they give.
[^2]: We always use least-fixed point semantics because encoding greatest fixpoint/weakest *liberal* pre-expectation semantics seems to be impossible with a single JANI property right now.
[^3]: [Corollary 4.26 of Benjamin Kaminski's PhD thesis](https://publications.rwth-aachen.de/record/755408/files/755408.pdf#page=115) states that (one-bounded) `wlp` can be computed via `wp` plus the probability of divergence.
[^4]: This is similar to the qualitative wlp, which evaluates to the top element of the Boolean lattice (`true`) if the loop has a possibility of nontermination. In the quantitative setting, we have `\infty` as our top element of the [`EUReal`](./stdlib/numbers.md#eureal) lattice.
[^5]: Storm currently does not support the qualitative analysis required for the `can_diverge` property and will throw an error. The feature is tracked in the issue [moves-rwth/storm#529](https://github.com/moves-rwth/storm/issues/529).

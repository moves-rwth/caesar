---
sidebar_position: 7
description: Caesar can export models to the JANI format.
---

# Model Checking

```mdx-code-block
import Link from '@docusaurus/Link';
```

Caesar has some support to export probabilistic programs written in (an executable fragment of) HeyVL to [the *jani-model* format](https://jani-spec.org/).
The JANI project defines exchange formats for quantitative model checking problems (and more).
Caesar outputs [Markov chains](https://en.wikipedia.org/wiki/Markov_chain) (MCs) or [Markov decision processes](https://en.wikipedia.org/wiki/Markov_decision_process) (MDPs), depending on which HeyVL language features are used.

The translation supports [executable HeyVL programs](#supported-programs).
These are written in a subset of HeyVL, for which we have well-defined forwards-stepping MC/MDP semantics.
[Not supported right now](#not-supported) is local unbounded nondeterminism (`havoc` or uninitialized local variables), procedure calls or quantitative `assume` statements.

After exporting HeyVL programs to JANI, we can use probabilistic model checkers to calculate and/or verify expected rewards.
In contrast to Caesar, these do not need user annotations like [invariants](./proof-rules/induction.md), but are fully automatic.
On the other hand, probabilistic model checkers often struggle with large or infinite state spaces.
Thus, the two approaches complement each other.

Caesar's developers recommend the [probabilistic model checker *Storm*](https://www.stormchecker.org/).

<small>
  Note: Caesar should not be confused with the set of tools in the <Link to="https://cadp.inria.fr/">CADP toolbox</Link> by INRIA, which includes tools like CAESAR, CAESAR.ADT, or OPEN/CAESAR.
  These also enable model checking of software, but are unrelated to this project.
</small>

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

To export JANI files for the model checker, run Caesar with the `to-jani` subcommand and the `--jani-dir DIR` option to instruct it to save all translateable (co)procs to `.jani` files in the directory `DIR`:

```bash
caesar to-jani example.heyvl --jani-dir DIR
```

The output JANI files will have the following structure that you can use:
 * Properties:
   * `reward`: This is the expected value of the verification conditions (cf. [Statements](./heyvl/statements.md)).
   * `diverge_prob`: The probability of not reaching the end of the (co)proc.
   * `can_diverge`: Boolean property whether the program has a path that does not reach the end of the (co)proc.[^5]
 * Constants:
   * One constant for each input variable of the (co)proc (constant has same name as variable).


### Model Checking with Storm

We use the [probabilistic model checker *Storm*](https://www.stormchecker.org).

<details>
    <summary>Quick Start: Using Storm via Docker.</summary>

    Using [Docker](https://www.docker.com/), you can download and run the latest version of Storm with just one command.

    ```bash
    docker run --mount type=bind,source="$(pwd)",target=/pwd -w /pwd --rm -it --name storm movesrwth/storm:stable storm [ARGS...]
    ```

    This command will automatically download the latest stable build of Storm (c.f. [list of Storm Docker image releases](https://hub.docker.com/r/movesrwth/storm/tags/)).
    The container will have the current directory mounted as `/pwd` and the container will use that as the working directory.
    Note that this means you can only access files from your working directory inside the container.
    After running the command, the container will be deleted.

    Read more on [Storm's documentation page for its Docker containers](https://www.stormchecker.org/documentation/obtain-storm/docker.html).
</details>

Running Storm on the produced file computes the expected reward.[^1]
Caesar translates procedure inputs to JANI's *constants*, and values for constants can be given to Storm via the flag `--constants init_c=0` (any other initial value can be chosen).

```bash
storm --jani DIR/FILE.jani -jprop reward --exact --sound --constants init_c=0
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
 * [If-then-else statements](./heyvl/statements.md#boolean-choices),
 * While loops (with least-fixed point semantics &mdash; [see below for semantics details](#loop-semantics)),
 * [`reward` statements](./heyvl/statements.md#reward-formerly-tick),
 * In `proc`s:
   * [`assert` statements](./heyvl/statements.md#assert-and-assume),
   * [Binary demonic choices](./heyvl/statements.md#nondeterministic-choices),
 * In `coproc`s:
   * [`coassert` statements](./heyvl/statements.md#assert-and-assume),
   * [Binary angelic choices](./heyvl/statements.md#nondeterministic-choices),
 * [Assumptions](./heyvl/statements.md#assert-and-assume) of the form `assume ?(b)` and `coassume !?(b)`,
 * Annotations, in particular [proof rule annotations](./proof-rules/), will be ignored.

#### Initial Values of Output Variables

Caesar will try to choose valid initial values for variables of built-in types such as `Bool`.
This reduces the number of initial states the model checker has to check.
We do this in a way that is not observable to the program, with one exception.

:::warning

By default, the JANI translation will assign arbitrary initial values to output variables.
This is correct when output variables are never read before they are written to.
However, if uninitialized output variables are read, then the choice is observable.

:::

This behavior can be disabled with the `--jani-uninit-outputs` option so that output variables are left uninitialized in the JANI model.

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
Then the result is $\infty$ if `can_diverge` is `true`, otherwise the result is `reward`.[^4]
This property is currently not supported by Storm.[^5]

We intentionally avoid using the *reachability reward* properties (i.e. setting the `reach` property of `ExpectedValueExpression` in JANI) as it will assign the expected reward $\infty$ to any state from which goal states are not reachable with probability 1.
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
The value $\infty$ cannot be explicitly represented in JANI, therefore `EUReal` expressions that go beyond the specific supported verification constructs are not supported.

### Not Supported

In particular, the following constructs are *not* supported:
 * Calls to uninterpreted functions or to `proc`s/`coproc`s,
 * Uninitialized variable declarations or `havoc`/`cohavoc` statements,
 * Quantitative `assume` or `coassume` statements.
 * [User-defined domains](./heyvl/domains.md), axioms will be ignored.


[^1]: We use the `--exact` and `--sound` flags to ensure that Storm is forced to use exact arithmetic and only sound algorithms to produce the solution. Consult your chosen model checker's documentation to see which guarantees they give.
[^2]: We always use least-fixed point semantics because encoding greatest fixpoint/weakest *liberal* pre-expectation semantics seems to be impossible with a single JANI property right now.
[^3]: [Corollary 4.26 of Benjamin Kaminski's PhD thesis](https://publications.rwth-aachen.de/record/755408/files/755408.pdf#page=115) states that (one-bounded) `wlp` can be computed via `wp` plus the probability of divergence.
[^4]: This is similar to the qualitative wlp, which evaluates to the top element of the Boolean lattice (`true`) if the loop has a possibility of nontermination. In the quantitative setting, we have $\infty$ as our top element of the [`EUReal`](./stdlib/numbers.md#eureal) lattice.
[^5]: Storm currently does not support the qualitative analysis required for the `can_diverge` property and will throw an error. The feature is tracked in the issue [moves-rwth/storm#529](https://github.com/moves-rwth/storm/issues/529).

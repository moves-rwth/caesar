---
sidebar_position: 7
description: Caesar can export models to the JANI format.
---

# Model Checking

```mdx-code-block
import Link from '@docusaurus/Link';
```

Caesar can export HeyVL programs to the [*jani-model* format](https://jani-spec.org/) so they can be analyzed using probabilistic model checkers.
The JANI project defines exchange formats for quantitative model checking problems (and more).
Caesar outputs [Markov chains](https://en.wikipedia.org/wiki/Markov_chain) (MCs) or [Markov decision processes](https://en.wikipedia.org/wiki/Markov_decision_process) (MDPs), depending on which HeyVL language features are used.

The translation supports [executable HeyVL programs](#supported-programs).
These are written in a subset of HeyVL, for which we have well-defined forwards-stepping MC/MDP semantics.
[Not supported right now](#not-supported) is local unbounded nondeterminism (`havoc` or uninitialized local variables), procedure calls or quantitative `assume` statements.

After exporting HeyVL programs to JANI, we can use probabilistic model checkers to calculate and/or verify expected rewards.
In contrast to Caesar, these do not need user annotations like [invariants](./proof-rules/induction.md), but are fully automatic.
On the other hand, probabilistic model checkers often struggle with large or infinite state spaces.
Thus, the two approaches complement each other.

We like the [probabilistic model checker *Storm*](https://www.stormchecker.org/).
Caesar has a dedicated [backend for Storm](#caesars-storm-backend) to automatically run Storm and extract the results.

<small>
  Note: Caesar should not be confused with the set of tools in the <Link to="https://cadp.inria.fr/">CADP toolbox</Link> by INRIA, which includes tools like CAESAR, CAESAR.ADT, or OPEN/CAESAR.
  These also enable model checking of software, but are unrelated to this project.
</small>

## Usage

For a simple example, consider the HeyVL program below.


```heyvl
@wp
proc geo_mc() -> (c: UInt, cont: Bool)
    post [!cont]
{
    c = 0
    cont = true
    while cont && c <= 20 {
        var prob_choice: Bool = flip(0.5)
        if prob_choice { cont = false } else { c = c + 1 }
    }
}
```

You can either use Caesar's [automatic *Storm* backend](#caesars-storm-backend) or [generate JANI manually](#generating-jani-manually) to use them however you wish.

Caesar will assign arbitrary initial values to *output parameters* and assumes that they are never read before they are written to.
To disable this or learn more, read the section on [initial values of output parameters](#initial-values-of-output-parameters).
In addition, note that we always [use least-fixed point semantics for loops in the JANI translation](#loop-semantics), therefore [`wlp` semantics](./proof-rules/calculi.md) is not supported.

The generated Markov chain model is *finite-state* and has a single initial state (no input parameters).
You'll usually want to maintain these restrictions when using a model checker.
Read more about [infinite-state and parametric models](#parametric-and-infinite-state-models) below.

### Option A: Caesar's *Storm* Backend {#caesars-storm-backend}

Caesar can automatically generate JANI files and run the [probabilistic model checker *Storm*](https://stormchecker.org).

To enable it, pass the `--run-storm OPTION` parameter to the command-line with one of the following values for `OPTION`:
 * `path`: Search for the Storm binary on the [`PATH`](https://en.wikipedia.org/wiki/PATH_(variable)).
 * `docker-stable`: Run Storm via the [`movesrwth/storm:stable` Docker image](https://www.stormchecker.org/documentation/obtain-storm/docker.html).
 * `docker-ci`: Run Storm via the [`movesrwth/storm:ci` Docker image](https://www.stormchecker.org/documentation/obtain-storm/docker.html).

The latter two options need to have [Docker](https://www.docker.com/) installed and running.
If the images are not installed, Docker will download them automatically.
This might take a while.
<small>
Caesar does not automatically update these images.
To update the `:ci` image for example, run `docker pull movesrwth/storm:ci`.
</small>

The above flag can be used with Caesar's `to-jani` command:
For example:
```bash
caesar to-jani --run-storm path example.heyvl
```
The result will look like this:
```
Expected reward from Storm: ≈ 0.9999995232
```
The result is approximate because it was computed via floating-point arithmetic.
To get exact results at the expense of slower computation, you can add the `--storm-exact` flag.

You can also use the `--run-storm` flag with the [`verify` command](./caesar/README.md#subcommand-caesar-verify) or with [our LSP server](./caesar/vscode-and-lsp.md).
Furthermore, you can set the `--no-verify` flag to only run model checking and not run Caesar's deductive verification.

### Option B: Generating JANI Manually {#generating-jani-manually}

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

Now you can use your favorite model checker with the resulting JANI files.

#### Running Storm Manually

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

```bash
storm --jani DIR/FILE.jani -jprop reward --exact --sound
```

Part of the output:

```
Model checking property "reward": R[exp]{"reward"}min=? [C] ...
Result (for initial states): 2097151/2097152 (approx. 0.9999995232)
```

## Parametric and Infinite-State Models

Model checkers usually work with finite-state models with a single initial state, therefore programs that do not fit into this category are often not so simple to model check.
We modified our original example and added  an input parameter `init_c` (multiple initial states, therefore "parametric") and removed the bound on the loop (infinite number of states).

```heyvl
@wp
proc geo_mc(init_c: UInt) -> (c: UInt, cont: Bool) // added input parameter init_c
    post [!cont]
{
    c = init_c
    cont = true
    while cont { // removed condition && c <= 20
        var prob_choice: Bool = flip(0.5)
        if prob_choice { cont = false } else { c = c + 1 }
    }
}
```

With Caesar, we could run the following command to approximate the expected reward for the program with `init_c = 5` with 10000 states:

```bash
caesar to-jani --run-storm <VALUE> example.heyvl --storm-constants init_c=5 --storm-state-limit 10000
```
And we get a result like this:
```
Expected reward from Storm: ⪆ 0.9999847412
```

**Inputs Are Translated to Constants.**
The input parameters of the program are translated by Caesar to constants in the JANI model.

 * For the [Caesar's Storm backend](#caesars-storm-backend) can fix values with the `--storm-constants <name>=<value>,...,<name>=<value>` command-line flag.
  * Storm itself uses the `--constants <name>=<value>,...,<name>=<value>` command-line flag.

Caesar can also be instructed to translate inputs to variables instead of constants with the `--jani-no-constants` flag.

**State Limits to Approximate Infinite-State Models.**
Storm can be used with a state limit so that the model generation will stop its exploration at some number of states.
This will yield a correct *under*-approximation of the expected reward.

 * For [Caesar's Storm backend](#caesars-storm-backend), this as the `--storm-state-limit <limit>` command-line flag.
 * Storm itself uses the `--state-limit <limit>` command-line flag.

<small>
  This feature is available since Storm 1.9.0 ([PR #521](https://github.com/moves-rwth/storm/pull/521)).
</small>

**Parametric Model Checking.**
If the program has input variables, [Storm's parametric model checking](https://www.stormchecker.org/documentation/usage/running-storm-on-parametric-models.html) may be of interest.

## Relation to Caesar's Unrolling Proof Rule

Caesar's [unrolling proof rule](./proof-rules/unrolling.md) can also be used to obtain sound bounds on expected rewards.
The unrolling proof rule is also sometimes called *bounded model checking*.
However, that proof rule is a bounded unrolling of the weakest pre-expectation semantics and therefore essentially an unrolling of all possible *paths* in the Markov chain.
In contrast, the complexity of probabilistic model checking scales only in the number of *states* and not in the number of paths.
Therefore, these techniques are somewhat related, but distinct.

For the original non-parametric example from the [Usage section](#usage), we obtain the optimal lower bound in Caesar without using a model checker.
The annotation `@unroll(22, 0)` for unrolling depth 22 finds the optimal value in this case.

<details>
    <summary>Unrolling Proof Rule Example</summary>

    ```heyvl
    @wp
    proc geo_mc() -> (c: UInt, cont: Bool)
        post [!cont]
    {
        c = 0
        cont = true
        @unroll(22, 0)
        while cont && c <= 20 {
            var prob_choice: Bool = flip(0.5)
            if prob_choice { cont = false } else { c = c + 1 }
        }
    }
    ```

    Because we gave no `pre`, Caesar will try to verify whether $\infty$ is a lower bound to the expected value.
    We get a counter-example:
    ```
    Counter-example to verification found!

    the pre-quantity evaluated to:
        0.99999... (2097151/2097152)
    ```

</details>

## Supported Programs

The translation to JANI supports a large subset of the HeyVL language.
You can use for example assignments, loops, conditionals, and probabilistic choices.
Nondeterministic choices and assertions are also supported, as well as Boolean `assume` statements.
[Not supported right now](#not-supported) is local unbounded nondeterminism (`havoc` or uninitialized local variables), procedure calls or quantitative `assume` statements.

### Supported Declarations

 * `proc` and `coproc` specifications with:
    * Inputs and output declarations,
    * `pre` declarations that are only Boolean conditions of the form `?(b)`.
    * `post` declarations (arbitrary operands).
 * [pure `func`s](./heyvl/domains.md#pure-functions) (*not* uninterpreted functions)

### Supported Statements

In the body, statements:

 * [Blocks](./heyvl/statements.md#blocks),
 * [Variable declarations](./heyvl/statements.md#variable-declarations) with initializers,
 * Assignments with pure expressions,
 * [Sampling from distributions](./stdlib/distributions.md),
 * [If-then-else statements](./heyvl/statements.md#boolean-choices),
 * While loops (with least-fixed point semantics &mdash; [see below for semantics details](#loop-semantics)),
 * [`reward` statements](./heyvl/statements.md#reward),
 * In `proc`s:
   * [`assert` statements](./heyvl/statements.md#assert-and-assume),
   * [Binary demonic choices](./heyvl/statements.md#nondeterministic-choices),
 * In `coproc`s:
   * [`coassert` statements](./heyvl/statements.md#assert-and-assume),
   * [Binary angelic choices](./heyvl/statements.md#nondeterministic-choices),
 * [Assumptions](./heyvl/statements.md#assert-and-assume) of the form `assume ?(b)` and `coassume !?(b)`,
 * Annotations, in particular [proof rule annotations](./proof-rules/), will be ignored.

#### Initial Values of Output Parameters

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
 * In [user-defined domains](./heyvl/domains.md), uninterpreted functions are not supported and axioms will be ignored.


[^1]: We use the `--exact` and `--sound` flags to ensure that Storm is forced to use exact arithmetic and only sound algorithms to produce the solution. Consult your chosen model checker's documentation to see which guarantees they give.
[^2]: We always use least-fixed point semantics because encoding greatest fixpoint/weakest *liberal* pre-expectation semantics seems to be impossible with a single JANI property right now.
[^3]: [Corollary 4.26 of Benjamin Kaminski's PhD thesis](https://publications.rwth-aachen.de/record/755408/files/755408.pdf#page=115) states that (one-bounded) `wlp` can be computed via `wp` plus the probability of divergence.
[^4]: This is similar to the qualitative wlp, which evaluates to the top element of the Boolean lattice (`true`) if the loop has a possibility of nontermination. In the quantitative setting, we have $\infty$ as our top element of the [`EUReal`](./stdlib/numbers.md#eureal) lattice.
[^5]: Storm currently does not support the qualitative analysis required for the `can_diverge` property and will throw an error. The feature is tracked in the issue [moves-rwth/storm#529](https://github.com/moves-rwth/storm/issues/529).

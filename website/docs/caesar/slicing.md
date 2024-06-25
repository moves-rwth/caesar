---
sidebar_position: 2
description: Caesar supports program slicing on the HeyVL intermediate verification language.
---

# Program Slicing

Caesar supports _program slicing_ on the HeyVL intermediate verification language.
It is the basis for Caesar's localized error reporting (e.g. "this loop invariant may not be inductive"), but we support more generalized slicing criteria as well.

Caesar has support for [*slicing for errors*](#slicing-for-errors), which aims at a sliced program that fails with a counter-example.
[*Assertion slicing*](#assertion-slicing) with its purpose of localizing error messages falls is a kind of slicing for errors.
[*Slicing for correctness*](#slicing-for-correctness) is aimed at finding a sliced program that verifies.
[*Assumption slicing*](#assumption-slicing) is one kind of slicing for correctness.

Fun fact: Caesar's slicing feature was developed with the project name *Brutus* &mdash; alluding to Caesar's adopted son, who also famously participated in a very different way of slicing...

---

**In this document:**

```mdx-code-block
import TOCInline from '@theme/TOCInline';

<TOCInline toc={toc} />
```

---

## Overview

[_Assertion slicing_](#assertion-slicing) is enabled by default on every verification query to help interpret a counterexample.
It does this by finding a minimal set of `assert`-like statements that must be in the code to obtain a verification error.
Caesar's built-in [proof rules](../proof-rules/) have annotations that provide interpretations to every `assert`.
For example, there is an assertion in the encoding of [induction](../proof-rules/induction.md) whose presence in a minimal counterexample slice means that the invariant might not be inductive.

[*Assumption slicing*](#assumption-slicing) must be enabled with the `--slice-verify` command-line flag.
It can be used to find a minimal set of `assume`-like statements with which the program verifies.
This may help optimizing or understanding a HeyVL proof.
For example, there's an `assume` in the induction encoding inside a verifying HeyVL program.
The removal of that `assume` indicates that a `while` loop could also be just a simple `if` statement for verification.
This could indicate a problem in the specification to be proved if the user knows a `while` statement should be necessary.

[*Slicing for errors*](#slicing-for-errors) generalizes assertion slicing to statements that are not necessarily `assert`-like and [*slicing for correctness*](#general-slicing-for-correctness) does the same for statements that are not necessarily `assume`-like.
We discuss these generalized applications in the respective sections [General Slicing for Errors](#general-slicing-for-errors) and [General Slicing for Correctness](#general-slicing-for-correctness).

On a very high level, Caesar's program slicing works by trying all different combinations of removing all candidate statements for the slice.
Our [theory of slicing](#a-theory-of-slicing-for-heyvl) for HeyVL formalizes the ideas of *`assert`-like* and *`assume`-like* via the *discordant* and *concordant* definitions and specifies soundness of slicing using these terms.
Caesar's [annotations for slicing](#slicing-annotations) can be used to add slicing information to statements such as error messages for assertions.
In the last section of this document, we describe [implementation details](#implementation-details) of the slicing algorithm in Caesar.

Interestingly, Caesar's slicing is in essence not very different from slicing-like approaches in classical deductive verifiers.
We just generalized the ideas to the *quantitative* setting of our intermediate verification language HeyVL, but the ideas are equally applicable to the *qualitative* setting.

:::info

Since our approach generalizes the qualitative setting and to simplify the presentation here, we will mostly give *qualitative* examples in the following to illustrate the ideas.
But keep in mind that everything also works for quantitative verification tasks in the same way.

:::

To our knowledge, Caesar's implementation of slicing is the first one that combines both slicing for errors, for correctness, on an IVL, in the quantitative setting.

:::note

Our slicing approach is still a work-in-progress which we hope to present in an upcoming academic publication.

:::

The following flowchart illustrates Caesar's slicing algorithm.


```mermaid
flowchart TD
    start[/Program/]
    query1{Verifies?}
    start --> query1

    verifies1(Verifies)
    cex1(Counter-Example)
    query1 --> cex1
    query1 --> verifies1

    %% unknown1(Unknown)
    %% query1 --> unknown1

    cex1 --> slicing_errors
    subgraph slicing_errors[Slicing for Errors]
        cex1_slice[[Slice statements]]
        cex1_slice --> cex1_slice
        cex1_done[/Minimal cex'ing slice/]
        cex1_slice --> cex1_done
        cex1_conclusion{Selection <br>assert-like?}
        cex1_done --> cex1_conclusion
        cex1_discordant[/Cex also valid <br>for original program/]
        cex1_unknown[/New cex'ing program/]
        cex1_conclusion --Yes --> cex1_discordant
        cex1_conclusion --No --> cex1_unknown
    end

    verifies1 -- --slice-verify --> slicing_correctness
    subgraph slicing_correctness[Slicing for Correctness]
        verifies1_slice[[Slice statements]]
        verifies1_slice --> verifies1_slice
        verifies1_done[/Minimal verifying slice/]
        verifies1_slice --> verifies1_done
        verifies1_conclusion{Selection <br>assume-like?}
        verifies1_done --> verifies1_conclusion
        verifies1_concordant[/Program also verifies <br>with less assumptions/]
        verifies1_unknown[/New verifying program/]
        verifies1_conclusion --Yes --> verifies1_concordant
        verifies1_conclusion --No --> verifies1_unknown
    end
```

## Slicing for Errors

*Slicing for errors* takes a HeyVL program and tries to remove as many statements from the *slice selection* as possible such that the resulting program fails verification with a counter-example.

### Assertion Slicing

_Assertion slicing_ is program slicing with the specific purpose of interpreting counter-examples for verification from the SMT solver.
The slice selection consists of all `assert`-like statements (cf. [*A Theory of Slicing for HeyVL*](#a-theory-of-slicing-for-heyvl) for details).

Consider the following HeyVL proc which does not verify:

```heyvl
proc two_asserts(x: UInt) -> ()
{
    assert ?(x >= 0)
    assert ?(x >= 1)
}
```

Clearly, the first assertion is not a problem since all `UInt` values are non-negative.
The second one fails when the input is `x = 0`.
The SMT solver will indeed give us that counter-example, but we still need to associate this counter-example to a specific assertion.
While we can simply try to evaluate all assertions in state `x = 0` for this example, this becomes impossible when we do not know what the exact state will be in a later statement.
This can happen after nondeterministic and probabilistic choices, or after unbounded loops.

Caesar instead looks at different counterfactuals for the current verification problem.

 1. Does a verification failure still occur with the first assert removed? Yes.
 2. Does a verification failure still occur with the second assert removed? No.

From this we can conclude that the second assert is at fault and *responsible* for the verification failure.
In general, Caesar will try to find a minimal *set* of assertions that will lead to a verification error.
The result is an error message like this:
```
program.heyvl::two_asserts: Counter-example to verification found!
    input variables:
        x: 0                                       (program.heyvl:1:12)

    the pre-quantity evaluated to:
        0

    program slice:
        ❌ assertion might not hold                  (program.heyvl:4:5)
```

This message's "program slice" section points to the second assertion in line 4.

Note that the minimal sets of assertions from counter-examples are not necessarily unique!
There might be even more verification failures after the assertions from slicing are removed.
The program slice from slicing for errors only constitutes a set from which no assertion can be removed while still getting an error (hence, *minimal*).

In theory, we could also look at assertions which are not present in *any* minimal slice for errors to determine assertions which are *never* a problem.
However, we have not found this useful and have not looked at this further.


### General Slicing for Errors

Only trying to remove `assert`-like statements may be too restrictive for certain applications.
Consider the following simple example:

```heyvl
proc assign_error() -> (x: UInt) {
    x = 2
    x = x * 2
    x = x * 2
    x = x * 2
    assert ?(x < 8)
}
```

This example will fail to verify since `x = 16` holds at the `assert`.
Caesar will also report the assertion as the culprit, but which assignments are problematic?

We can annotate the assignments to instruct Caesar to also try to remove them to still get a counterexample (cf. [slicing annotations documentation](#slicing-annotations)).
```heyvl
proc assign_error() -> (x: UInt) {
    x = 2
    @slice_error {
        @error_msg("first needed") x = x * 2
        @error_msg("second needed") x = x * 2
        @error_msg("third needed") x = x * 2
    }
    assert ?(x < 8)
}
```

The result is something like this:
```
program.heyvl::assign_error: Counter-example to verification found!
    the pre-quantity evaluated to:
        0

    program slice:
        ❌ first needed                             (program.heyvl:4:36)
        ❌ third needed                             (program.heyvl:6:36)
        ❌ assertion might not hold                  (program.heyvl:8:5)
```

While this example is somewhat silly, one can imagine a more complicated example where removing assignments might be helpful to narrow down the problem.

You may ask: why do we not try slice assignments by default?
The answer is that assignments are not *discordant* according to our [*theory of slicing for HeyVL*](#a-theory-of-slicing-for-heyvl), i.e. removing them does not allow us to conclude something about the original program directly.
In general, a counterexample of a HeyVL program with a removed assertion might imply that the original also has a counterexample (as is the case here), but it could also not imply it.
It might even imply that the original program verified!
Consider a program like `x = true; x = !x; assert ?(x)` for example.

## Slicing for Correctness

*Slicing for correctness* takes a HeyVL program and tries to remove as many statements from the *slice selection* as possible such that the resulting program verifies.

:::danger

The current implementation of slicing for correctness is **unsound** for programs that contain [uninterpreted functions](../heyvl/domains.md).
This unsoundness also follows for assumption slicing.
Note that uninterpreted functions may also be generated internally for [quantitative quantifiers](../heyvl/expressions.md#quantifiers) if they are not eliminated by Caesar's quantifier elimination procedure.
If you enable `--slice-verify`, you must currently **check yourself** that you do not use uninterpreted functions.

:::

### Assumption Slicing

*Assumption slicing* selects all `assume`-like statements as candidates to remove from the program and slices so that the resulting program verifies.
After this process, we can get a minimal set of assumptions which are needed for the program to still verify.
From the set of assumptions which are *not* included in the minimal necessary slice to verify, we can generate warnings which might indicate a problem to the user.
For example we might find out that a pre to a proc is not necessary.

Consider the following program:

```heyvl
proc assumes(x: UInt) -> ()
    pre ?(x == 42)
{
    assume 0
    assert ?(x >= 1)
}
```

Caesar will emit an output similar to this:

```
program.heyvl::assumes: Verified.
    program slice:
        🤷 assumption is not necessary              (program.heyvl:4:5)
```

As is the case in [assertion slicing](#assertion-slicing), the minimal set of assumptions is not necessarily unique.
We also do not search for assumptions which are included in no minimal set of assumptions, instead for just one minimal set from which we cannot remove an assumption without the program not verifying.

### General Slicing for Correctness

Consider the following example, in which we sample two bits with fair coin flips.
The specification says that the probability of a value of the sampled value `r >= 2` is at least `1/2`.
The specification holds, but only one assignment is actually necessary!

```heyvl
proc bits() -> (r: EUReal)
    pre 1/2
    post [r >= 2]
{
    var b0: UInt; var b1: UInt

    @slice_verify() {
        var choice: Bool = flip(0.5)
        if choice { b0 = 0 } else { b0 = 1 }
        choice = flip(0.5)
        if choice { b1 = 0 } else { b1 = 1 }
        r = b0 + 2 * b1
    }
}
```

Running Caesar with the `--slice-verify` option on this program, we get the following output:

```
program.heyvl::bits: Verified.
    program slice:
        🤷 statement in line 9 is not necessary       (program.heyvl:9:21)
        🤷 statement in line 9 is not necessary       (program.heyvl:9:37)
        🤷 statement in line 11 is not necessary     (program.heyvl:11:21)
```

From this we can conclude that all but the `b1 = 1` assignment are actuallly not necessary to satisfy the specification.

Analogous to the case in [general slicing for errors](#general-slicing-for-errors), we need to explicitly instruct Caesar to try to remove assignments during slicing for correctness using the `@slice_verify` annotation (cf. [slice selection annotations](#slicing-selections)).
If Caesar tried to remove all assignments by default, we would not necessarily gain any knowledge about the original program.
More details in the [theory of slicing for HeyVL](#a-theory-of-slicing-for-heyvl).

## Slicing Annotations

For both slicing for errors and correctness, Caesar has some built-in defaults.
This includes a default *slice selection* and messages for the statements (such as "assertion might not hold").
These defaults can be overwritten by annotations on statements.
Internally, Caesar also uses these statements, e.g. in the generated encodings for [proof rules](../proof-rules/) to attach messages to statements such as an assertion for an inductiveness check of a loop.

The annotations can be added to blocks and compositional statements such as `if`-statements and will be inherited by all sub-statements.

### Slicing Message Annotations

The `@error_msg` and the `@success_msg` annotations can be used to attach messages in case a statement is sliced for errors and correctness, respectively.
For example:

```heyvl
proc two_asserts(x: UInt) -> ()
{
    @error_msg("x at least zero not necessary") assert ?(x >= 0)
    @error_msg("x at least one not necessary") assert ?(x >= 1)
}
```

Will result in the following section in the counter-example:

```
[...]
    program slice:
        ❌ x at least one does not hold             (program.heyvl:4:48)
```

The `@success_msg` annotation is used in the same way.

Tip: You can inspect the internally generated slicing message annotations from built-in proof rules by passing the `--print-core-procs` command-line option to Caesar.

### Slicing Selections

By default, Caesar selects `assert`-like statements ("discordant") for slicing for errors and `assume`-like statements ("concordant") for slicing for correctness.
The terms *discordant* and *concordant* are defined in our [theory of slicing for HeyVL](#a-theory-of-slicing-for-heyvl).

In addition to these defaults, Caesar has annotations to add other statements to the slice selection:
 * `@slice_verify`: Also slice this statement during *slicing for correctness*.
 * `@slice_error`: Also slice this statement during *slicing for errors*.

Note that these annotations will enable slicing for individual sub-statements, not whole blocks.

## A Theory of Slicing for HeyVL

When is it "correct" to slice a statement?
What does it mean if we know a statement has been removed from the program?
Our theory of slicing for HeyVL aims to give clear correctness criteria for slicing.

:::info

The theory is based on the verification condition semantics of HeyVL.
You can find some information in the [statements documentation](../heyvl/statements.md) and all relevant formal background in our [OOPSLA '23 paper](../publications.md#oopsla-23).
We are working on an academic publication about these ideas that goes into more detail.

:::

### Slice Effects

At the core of our theory of slicing for HeyVL are _slice effects_, which categorize each HeyVL statement into one of three categories: *concordant*, *discordant*, and *ambiguous*.
You can think of *concordant* statements as *like assumptions* and of *discordant* statements as *like assertions*.
Slice effects depend on the current *direction* in which we verify.
In a `proc`, our direction is *down* (*lower bounds*), and in a `coproc`, the direction is *up* (*upper bounds*).

Formally, we define *concordant*  and *discordant* as follows:
 * In `proc`s:
   * A statement `S` is *concordant* when for all `post` it holds that `post = vc[skip](post) <= vc[S](post)`.
   * A statement `S` is *discordant* when for all `post` it holds that `post = vc[skip](post) >= vc[S](post)`.
 * In `coproc`s, the definitions are reversed:
   * A statement `S` is *concordant* when for all `post` it holds that `post = vc[skip](post) >= vc[S](post)`.
   * A statement `S` is *discordant* when for all `post` it holds that `post = vc[skip](post) <= vc[S](post)`.

Informally, introducing *concordant*  will make them only *verify more*, i.e. the `vc` semantics will at most increase in `proc`s (or at least decrease in `coproc`s).
This means if we removed them, we can re-insert concordant statements and the program will still verify.
On the other hand, *discordant* statements will make programs *verify less*, i.e. the `vc` semantics will at most decrease in `proc`s (or at least increase in `coproc`s).
That means if we removed them, we can re-insert concordant statements and if the sliced program failed to verify, the original program will also fail to verify.

Below is a table of HeyVL statements and their slice effects.
It should be pretty intuitive: `assume` statements are concordant with respect to lower bounds, and `assert`, `havoc`, and `validate` are discordant.
When they're used in upper bound contexts, then their effects are reversed.
For the `co`-statements, the situation is also exactly reversed.

<>
    <table style={{float: "left", "padding-right": "2em"}}>
        <thead>
            <tr>
                <td>Statement</td>
                <td><code>proc</code></td>
                <td><code>coproc</code></td>
            </tr>
        </thead>
        <tbody>
            <tr>
                <td><code>assume</code></td>
                <td>Concordant</td>
                <td>Discordant</td>
            </tr>
            <tr>
                <td><code>assert</code></td>
                <td>Discordant</td>
                <td>Concordant</td>
            </tr>
            <tr>
                <td><code>havoc</code></td>
                <td>Discordant</td>
                <td>Concordant</td>
            </tr>
            <tr>
                <td><code>validate</code></td>
                <td>Discordant</td>
                <td>Concordant</td>
            </tr>
        </tbody>
    </table>
    <table style={{float: "left"}}>
        <thead>
            <tr>
                <td>Statement</td>
                <td><code>proc</code></td>
                <td><code>coproc</code></td>
            </tr>
        </thead>
        <tbody>
            <tr>
                <td><code>coassume</code></td>
                <td>Discordant</td>
                <td>Concordant</td>
            </tr>
            <tr>
                <td><code>coassert</code></td>
                <td>Concordant</td>
                <td>Discordant</td>
            </tr>
            <tr>
                <td><code>cohavoc</code></td>
                <td>Concordant</td>
                <td>Discordant</td>
            </tr>
            <tr>
                <td><code>covalidate</code></td>
                <td>Concordant</td>
                <td>Discordant</td>
            </tr>
            <tr>
                <td><code>tick</code>*</td>
                <td>Concordant</td>
                <td>Discordant</td>
            </tr>
        </tbody>
    </table>
    <div style={{clear: "both"}} />
</>

Note that Caesar only tries to slice `(co)assume` and `(co)assert` statements, but not `(co)havoc` nor `(co)validate`.

*: `tick`/`reward` statements are currently not sliced by default.
This must be enabled with the `--slice-ticks` command-line option.

## Implementation Details

Caesar's implementation of slicing is a two-stage approach.
It first does a [program transformation](#program-transformation) to prepare the input program for slicing.
Then we use the SMT solver to minimize the number of enabled statements in the slice in the [solving for minimal slices](#solving-for-minimal-slices) stage.

### Program Transformation

To prepare a HeyVL program for slicing, Caesar starts with a *slice selection* of potential statements to slice.
Usually, that's discordant statements and those enabled with explicit [slice selection annotations](#slicing-selections).
If the option `--slice-verify` is set, then we also transform concordant statements as well.

For each potentially sliceable statement `S`, we create a new Boolean input variable `slice_S` to the program.
The statement `S_i` is (logically) replaced by `if slice_i { S } else {}`.
In the implementation, we have specialized transformations for almost all kinds of statements to avoid exponential blow-up of the generated verification conditions.

Consider an assumption `assume f`.
If we just wrapped it into an `if` statement, then we would get verification conditions that contain the post twice:
```
vc[if slice_1 { assume f } else {}](post) = ite(slice_1, f ==> post, post)
```
However, we do an equivalent transformation so that the post is not duplicated:
```
vc[assume ite(slice_1, f, 0)](post) = (ite(slice_1, f, 0) ==> post)
```

### Solving for Minimal Slices

After this program transformation, every potentially sliceable statement is associated with a Boolean variable that we can use to turn it on or off.
That means we can just set constraints on the number of enabled statements in the SMT solver to query for a new slice.
We do *not* need to re-generate verification conditions, nor do we re-do our optimizations.
This allows us to take advantage of the abilities of modern SMT solvers to try a lot of Boolean combinations very quickly.

When we [slice for errors](#slicing-for-errors), we can generate a nice exists-exists query that looks for a counter-example to verification with an assignment to the enabled variables.
It is of the form
```
exists slice_1,...,slice_n: exists initial_state: vc[S](\infty) != \infty
```

[Slicing for correctness](#slicing-for-correctness) unfortunately generates a quantifier alternation.
We ask the SMT solver to find an assignment to the slice variables such that *for all* initial states the program verifies:
```
exists slice_1,...,slice_n: forall initial_state: vc[S](\infty) == \infty
```

After building these new verification queries for slicing, we minimize the number of enabled statements by iteratively asking the SMT solver for a solution with a smaller number of enabled slice variables.
We do a kind of binary search that takes into account the possibility of an "unknown" result from the SMT solver.

As far as we could tell, using e.g. Z3's built-in optimizer for these tasks is often infeasible as it is restricted to a (not particularly well-defined) fragment of input formulas and _may return unsound results_ on other inputs.
It also seems to be designed to find actually optimal results, whereas we are also happy with a "good" result if some timeout expires.

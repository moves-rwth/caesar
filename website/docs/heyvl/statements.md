---
description: Statements are executed sequentially and may have side-effects.
sidebar_position: 2
---

# Statements

Statements in HeyVL are instructions that are interpreted sequentially and that have side-effects.
They are used inside the body of [procedures](./procs.md).

We can categorize HeyVL's statements into either *concrete* or *verification* statements.
We have [concrete statements](#concrete-statements) and [verification statements](#verification-statements).
Concrete statements include [assignments](#assignments), [Boolean choices](#boolean-choices), and [while loops](#while-loops).

The purpose of *verification statements* is to encode either *proof obligations* and *proof assumptions*.
For example, [assert and assume statements](#assert-and-assume) are used to do this.
When you are verifying programs, you ideally do not use these verification statements directly but instead use Caesar's built-in set of [proof rules](../proof-rules/).
They internally use verification statements, but Caesar's proof rules guarantee correct usage so that the proofs are sound.

Below is an overview of HeyVL's statements with links to the respective documentation sections:

| [Concrete Statements](#concrete-statements) | [Verification Statements](#verification-statements) |
|-----------------------|-------------------------|
| [Blocks](#blocks)                | [Assert and Assume](#assert-and-assume)       |
| [Variable Declarations](#variable-declarations) | [Havoc](#havoc)                   |
| [Assignments and Procedure Calls](#assignments)           | [Reward](#reward)                  |
| [Boolean Choices](#boolean-choices)           | [Nondeterministic Choices](#nondeterministic-choices)|
| [While Loops](#while-loops)                      |          |

There are also some [deprecated verification statements](#deprecated-statements).


## Semantics: The Meaning of HeyVL Programs {#semantics}

Since HeyVL is an intermediate verification language, not all statements allow an operational interpretation of their effects.
All HeyVL statements should be understood through their (quantitative) verification condition semantics.
These are defined in reverse order, starting from an initial verification condition and proceeding from the last statement backwards to the front.
We describe the *formal semantics of HeyVL statements* [in our paper on Caesar (cf. Section 3)](https://arxiv.org/pdf/2309.07781.pdf#page=10).


## Concrete Statements


### Blocks

A block is a sequence of statements enclosed by curly braces.
Statements _may_ be separated by semicolons, but those can be omitted.
Each block creates a _local scope_ into which variables are declared.
Blocks can be nested.
For example:
```heyvl
x = 1
{
    var y: UInt
}
y = 1 // y is not declared in this scope
```


### Variable Declarations

A variable declaration creates a new local variable of type `Type` in the current scope:
```heyvl
var name: Type
```
See the [standard library](../stdlib/) for Caesar's built-in types and [domains](./domains.md) for user-defined types.

A variable declaration can be combined with an assignment to initialize the variable:
```heyvl
var forty_two: UInt = 42
```

If a variable is not initialized, the program will be verified *for all* possible values of that variable.

### Assignments and Procedure Calls {#assignments}

An assignment evaluates the expression on the right-hand side in the current state and assigns the result to the variable on the left-hand side.
For example:
```heyvl
x = 39 + y
```
The right-hand side must evaluate to a value of a type that can be matches the type of `x`.

The right-hand side of the assignment can be a procedure call.
See the [reference on procedure calls](./procs.md#calling-procedures) for more information.[^calls-concrete]

The left-hand side of an assignment may be a list of variables to unpack a tuple.
For example, imagine a procedure `two_numbers` whose return type is `(x: UInt, y: UInt)`.
The following statement assigns the result of a call to `two_numbers` to `x` and `y`:
```heyvl
x, y = two_numbers()
```
If the procedure does not have any return values, the call may be written without the equals sign and the left-hand side, i.e. simply:
```heyvl
fn(arg1, arg2)
```


### Boolean Choices

HeyVL supports a binary choice depending on the value of a Boolean expression:
```heyvl
if x + 1 == 2 {
    ...
} else {
    ...
}
```

### While Loops

HeyVL supports while loops that run a block of code while a condition evaluates to true.
```heyvl
var cont: Bool = true
@invariant(...)
while cont {
    cont = flip(0.5)
}
```

For verification, **while loops need to have [proof rule annotations](../proof-rules/)** such as the [`@invariant(...)` annotation](../proof-rules/induction.md) in the example.
If a while loop does not have a proof rule annotation, Caesar cannot verify the program and will show an error.

The proof rule annotations also implicitly specify whether the loop has least or greatest fixpoint semantics.
This choice can be made explicit with the [calculus annotations](../proof-rules/calculi.md) on procedures, which we recommend you use.

With the **[model checking translation](../model-checking.md), proof rule annotations are not necessary**.
It allows usage of a *probabilistic model checker* such as [Storm](https://www.stormchecker.org/) for a subset of HeyVL programs.
This can be helpful to e.g. get an initial estimation of expected values.

## Verification Statements


### Havoc

A `havoc` statement can be used to "forget" previous values of variables in the following code.
It also comes in a `co` variant.
```heyvl
havoc x, y, z
cohavoc a, b, c
```

The verification condition semantics of `havoc` and `cohavoc` create an infimum respectively supremum over the specified variables.


### Assert and Assume

These statements generate binary operators in the verification condition semantics.
All three statements also come in `co` variants.
`(co)assert` generates an infimum respectively supremum.
`(co)assume` generates an implication respectively co-implication.

```heyvl
assert 1 + x
assume 0
```


### Reward

The `reward` statement accepts an expression and adds it to the current verification condition.
For example,
```heyvl
reward 2 * x
```
has the following semantics: `vc[reward 2 * x](f) = f + (2 * x)`.

`tick` is another name that Caesar accepts for `reward`.


### Nondeterministic Choices

HeyVL supports two kinds of binary nondeterministic choices: The "demonic" one (`if ⊓`) and the "angelic" one (`if ⊔`).
```heyvl
if ⊓ {
    ...
} else {
    ...
}
```

You can also use Latex-style syntax instead of Unicode.
Caesar supports `\cap` and `\cup` instead of `⊓` and `⊔`, respectively.
(We're looking for better syntax for these statements. If you have an idea, [please start a discussion](https://github.com/moves-rwth/caesar/discussions).)


## Deprecated Statements

Caesar supports some HeyVL statements that are not part of the HeyVL language [published in our OOPSLA '23 paper](../publications.md#oopsla-23).


:::caution

These statements were used for previous iterations of HeyVL, but may be removed from Caesar at any time.

:::

### Compare

A `compare f` statement corresponds to an abbreviation of `validate; assume f`.

The dual `cocompare f` statement corresponds to an abbreviation of `covalidate; coassume f`.

### Negations

We have a `negate` and an `conegate` statement, whose semantics correspond to HeyLo's negations.

The `validate` statement corresponds to `conegate; conegate` and `covalidate` corresponds to `negate; negate`.

It is recommended that you avoid negations for the reasons detailed in the warning below.

:::danger

Negation statements in HeyVL break _monotonicity_, an important property of HeyVL semantics that is required for sound [(co)procedure calls](procs.md#calling-procedures).
If negations are used in such a way that monotonicity is broken, then (co)procedure calls are unsound.
Refer to our [OOPSLA '23 paper](../publications.md#oopsla-23) for details on monotonicity and soundness of (co)procedure calls.

:::


[^calls-concrete]: Note that a procedure does not necessarily need to have a body.
Caesar will verify calls only based on their specification.
In those cases, a procedure call is thus not concrete.

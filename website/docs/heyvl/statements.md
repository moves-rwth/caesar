---
description: Statements are executed sequentially and may have side-effects.
sidebar_position: 2
---

# Statements

Statements in HeyVL are instructions that are interpreted sequentially and that have side-effects.
They are used inside the body of [procedures](./procs.md).

## Semantics

Since HeyVL is an intermediate verification language, not all statements allow an operational interpretation of their effects.
All HeyVL statements should be understood through their (quantitative) verification condition semantics.
These are defined in reverse order, starting from an initial verification condition and proceeding from the last statement backwards to the front.
We describe the *formal semantics of HeyVL statements* [in our paper on Caesar (cf. Section 3)](https://arxiv.org/pdf/2309.07781.pdf#page=10).

## Blocks

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

## Variable Declarations

A variable declaration `var name: Type` creates a new local variable in the current scope.
A variable declaration can be combined with an assignment to initialize the variable:
```heyvl
var forty_two: UInt = 42
```

## Assignments

An assignment `x = 39 + y` evaluates the expression on the right-hand side in the current state and assigns the result to the variable on the left-hand side.

The left-hand side of an assignment may be a list of variables to unpack a tuple.
For example, imagine a procedure `two_numbers` whose return type is `(x: UInt, y: UInt)`.
The following statement assigns the result of a call to `two_numbers` to `x` and `y`:
```heyvl
x, y = two_numbers()
```

If the right-hand side of the assignment is a (pure) expression, then the verification condition semantics amounts to a substitution of the left-hand side by the right-hand side.

The right-hand side of the assignment can be a procedure call.
See the [reference on procedure calls](./procs.md#calling-procedures) for more information.

If the procedure does not have any return values, the call may be written without the equals sign and the left-hand side, i.e. simply `fn(arg1, arg2)`.

## Havoc

A `havoc` statement can be used to "forget" previous values of variables in the following code.
It also comes in a `co` variant.
```heyvl
havoc x, y, z
cohavoc a, b, c
```

The verification condition semantics of `havoc` and `cohavoc` create an infimum respectively supremum over the specified variables.

## Assert and Assume

These statements generate binary operators in the verification condition semantics.
All three statements also come in `co` variants.
`(co)assert` generates an infimum respectively supremum.
`(co)assume` generates an implication respectively co-implication.

```heyvl
assert 1 + x
assume 0
```

## Reward (formerly Tick)

The `reward` statement accepts an expression and adds it to the current verification condition.
For example,
```heyvl
reward 2 * x
```
has the following semantics: `vc[reward 2 * x](f) = f + (2 * x)`.

`tick` is another name that Caesar accepts for `reward`.

## Nondeterministic Choices

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

## Boolean Choices

HeyVL supports a binary choice depending on the value of a Boolean expression:
```heyvl
if x + 1 == 2 {
    ...
} else {
    ...
}
```

## While Loops

HeyVL supports while loops that run a block of code while a condition evaluates to true.
```heyvl
var cont: Bool = true
while cont {
    cont = flip(0.5)
}
```

However, for verification while loops need to be annotated with [proof rules](../proof-rules/), otherwise Caesar will show an error.
These proof rule annotations also implicitly specify whether the loop has least or greatest fixpoint semantics.
This choice can be made explicit with the [calculus annotations](../proof-rules/calculi.md) on procedures, which we recommend you use.

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

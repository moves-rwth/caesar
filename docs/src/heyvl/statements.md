# HeyVL Statements

Statements in HeyVL are instructions that are interpreted sequentially and that have side-effects.
They are usually used inside the body of [procedures](./procs.md), but caesar also accepts an input file that consists solely of a sequence of statements without any declarations (via `--raw`, cf. [caesar documentation](../caesar.md)).

Since HeyVL is an intermediate verification language, not all statements allow an operational interpretation of their effects.
All HeyVL statements should be understood through their (quantitative) verification condition semantics.
These are defined in reverse order, starting from an initial verification condition and proceeding from the last statement backwards to the front.

More information can be found on the [statements](./statements.md) page.

## Blocks

A block is a sequence of statements enclosed by curly braces.
Statements _may_ be separated by semicolons, but those can be omitted.
Each block creates a _local scope_ into which variables are declared.
Blocks can be nested.
For example:
```
x = 1
{
    var y: UInt
}
y = 1 // y is not declared in this scope
```

## Variable Declarations

A variable declaration `var name: Type` creates a new local variable in the current scope.
A variable declaration can be combined with an assignment to initialize the variable:
```
var forty_two: UInt = 42
```

## Assignments

An assignment `x = 39 + y` evaluates the expression on the right-hand side in the current state and assigns the result to the variable on the left-hand side.

The left-hand side of an assignment may be a list of variables to unpack a tuple.
For example, imagine a procedure `two_numbers` whose return type is `(x: UInt, y: UInt)`.
The following statement assigns the result of a call to `two_numbers` to `x` and `y`:
```
x, y = two_numbers()
```

If the right-hand side of the assignment is a (pure) expression, then the verification condition semantics amounts to a substitution of the left-hand side by the right-hand side.

If the right-hand side is a call to a procedure, then the assignment is translated to a combination of `assert`, `havoc`, and `compare` statements.
See the [reference on procedures](./procs.md) for more information.

If the procedure does not have any return values, the call may be written without the equals sign and the left-hand side, i.e. simply `fn(arg1, arg2)`.

## Havoc

A `havoc` statement can be used to "forget" previous values of variables in the following code.
It also comes in a `co` variant.
```
havoc x, y, z
cohavoc a, b, c
```

The verification condition semantics of `havoc` and `cohavoc` create an infimum respectively supremum over the specified variables.

## Assert, Assume, Compare

These statements generate binary operators in the verification condition semantics.
All three statements also come in `co` variants.
`(co)assert` generates an infimum respectively supremum.
`(co)assume` generates an implication respectively co-implication.
`(co)compare` generates a hard (co-)implication.

```
assert 1 + x
assume 0
cocompare 7 * 10
```

## Tick

The `tick` statement accepts an expression and adds it to the current verification condition.
For example,
```
tick 2 * x
```
has the following semantics: `vc[tick 2 * x](f) = f + (2 * x)`.

## Negations

We have a `negate` and an `conegate` statement.

## Nondeterministic Choices

HeyVL supports two kinds of binary nondeterministic choices: The "demonic" one (`if ⊓`) and the "angelic" one (`if ⊔`).
```
if ⊓ {
    ...
} else {
    ...
}
```

## Boolean Choices

HeyVL supports a binary choice depending on the value of a Boolean expression:
```
if x + 1 == 2 {
    ...
} else {
    ...
}
```

---
description: Domain blocks are used to create user-defined types and uninterpreted functions.
sidebar_position: 4
---

# Domains, Uninterpreted Functions, and Axioms

`domain` blocks are used to create user-defined types and uninterpreted functions.
A domain has a name which can be used as a type in HeyVL code.
The domain block contains a list of `func`s and `axiom`s defined on this domain.

Every domain type supports the binary operators `==` and `!=`.
All other operations must be encoded using functions and axioms.

:::warning Unsoundness from Axioms

`axiom` declarations behave like [`assume` statements](./statements.md) and can quickly make verification unsound.
E.g. `axiom unsound ?(false)` behaves like `assume ?(false)`, making everything verify.
[See below for a longer example](#unsoundness-from-axioms).

:::

:::tip Incompleteness from Quantifiers

Note that axioms with quantifiers quickly introduce *incompleteness* of Caesar, making it unable to prove or disprove verification.
Read the documentation section on [SMT Theories and Incompleteness](../caesar/debugging.md#incompleteness) for more information.

:::

## Example: Exponentials of ½

HeyVL does not support exponentiation expressions natively.
But we can define an uninterpreted function `ohfive_exp` and add axioms that specify its result.
`ohfive_exp(n)` should evaluate to `(½)ⁿ`, so we add two axioms that define this exponential recursively.

`ohfive_exp_base` states that `ohfive_exp(0) == 1` and `ohfive_exp_step` ensures that `ohfive_exp(exponent + 1) == 0.5 * ohfive_exp(exponent)` holds.
This is sufficient to axiomatize our exponential function.

```heyvl
domain Exponentials {
    func ohfive_exp(exponent: UInt): EUReal

    axiom ohfive_exp_base ohfive_exp(0) == 1
    axiom ohfive_exp_step forall exponent: UInt. ohfive_exp(exponent + 1) == 0.5 * ohfive_exp(exponent)
}
```
Note that this domain declaration creates a new type `Exponentials`, but we do not use it.

We can check that `ohfive_exp(3)` evaluates to `0.125` by declaring a [procedure](procs.md) with pre-condition `true` and post-condition `ohfive_exp(3) == 0.125`.
This procedure verifies:
```heyvl
proc ohfive_3() -> ()
    pre ?(true)
    post ?(ohfive_exp(3) == 0.125)
{}
```

Do not forget the _empty_ block of statements `{}` at the end.
If you omit it, [Caesar will not attempt to verify the procedure](./procs.md#procs-without-body) and thus will not check the specification.

## Pure Functions

You can also declare _pure_ or _interpreted_ functions.
These are defined by a single expression that computes the result of the function.

The following function declaration has a such a definition (`= x + 1`):
```heyvl
func plus_one(x: UInt): UInt = x + 1
```

One can intuitively understand the above syntax as syntactic sugar for a function declaration with an additional axiom, i.e.
```heyvl
func plus_one(x: UInt): UInt
axiom plus_one_def forall x: UInt. plus_one(x) == x + 1
```
However, the *pure* function syntax allows Caesar to make certain optimizations, therefore it should always be preferred.

## Unsoundness From Axioms

Axioms are a dangerous feature because they can make verification unsound.

An easy example is this one:
```heyvl
domain Unsound {
    axiom unsound false
}

proc wrong() -> ()
    pre ?(true)
    post ?(true)
{
    assert ?(false)
}
```
The axiom `unsound` always evaluates to `false`.
But for verification, Caesar assumes the axioms hold for all program states.
In other words, Caesar only verifies the program states in which the axioms evaluate to `true`.
Thus, Caesar does not verify any program state and the procedure `wrong` incorrectly verifies!

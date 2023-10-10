---
title: Procedures
description: Procedures are HeyVL's logical units of code.
sidebar_position: 1
---

# Procedures and Coprocedures

HeyVL [statements](statements.md) are placed inside the body of _(co)procedures_ or _(co)procs_ for short.
A *procedure* has a name, a list of parameters, a list of return values, and a list of specification attributes.
Caesar tries to verify each procedure in the given HeyVL files using the specification.
*Coprocedures* are like procedures, but the specification is interpreted differently (see below).

Procedures can be called inside other procedures.
This enables modular reasoning about code: Prove that some code satisfies the specification once, and then use the specification when at the call site - without reasoning about the procedure's body again.

There are also procedures without an associated body.
They are not verified by Caesar, but can be called inside other procedures.

## Example

The following procedure named `forty_two` accepts a single parameter, `x` of type `UInt` and returns a value `y` of type `UInt`:
```heyvl
proc forty_two(x: UInt) -> (y: UInt)
    pre ?(x == 41)
    post ?(y == 42)
{
    y = x + 1;
}
```
There are two specification attributes: `pre` and `post`.
Intuitively, both attributes assert that if `forty_two` is called with `x == 41`, the result `y` will have value `42`.
The expressions inside the `pre` and `post` statements are expectations, i.e. have type [`EUReal`](../stdlib/numbers.md#eureal).
We use [embed expressions](expressions.md) to convert Boolean expressions to `EUReal` values.
The procedure has a body with just a single assignment statement that increments `x` by 1 and saves the result in `y`.

Writing `coproc` instead of `proc` will will do an upper bound check for verification instead of a lower bound one.

The specification is optional; if it's not provided, Caesar will add a default specification: `pre ?(true)` and `post ?(true)` for procedures and `pre ?(false)` and `post ?(false)` for coprocedures.

## Verification of Procedures

If a procedure has a body with statements, then Caesar will try to verify the procedure based on the specification attributes.
The verificiation of procedures can be entirely framed as a verification of HeyVL statements.

### Verification Encoding Internals

To verify the `forty_two` procedure, Caesar generates the following HeyVL statements:
```heyvl
assume ?(x == 41)
y = x + 1;
assert ?(y == 42)
```
Each `pre` attribute generates an `assume`/`coassume` statement at the beginning.
Then the unmodified procedure body follows.
After that, an `assert`/`coassert` statement is generated for each `post` attribute.

For coprocedures, the generated HeyVL statements will be preceded by a `negate` and ended by a `conegate` statement.

## Calling Procedures

Procedures can be called inside other procedures.
Just like for the verification task, a call of a procedure is replaced by a sequence of HeyVL statements based on the specification.

### Procedure Call Internals

A call to `forty_two`, e.g. `y = forty_two(x);` is replaced by three basic HeyVL statements:
```heyvl
assert ?(x == 41)
havoc y
validate
assume ?(y == 42)
```
Now we `assert` each `pre` to ensure that the preceding code has actually established the pre-condition.
Then we `havoc` the modified variable `y`.
At this point, we know nothing about the value of `y`.
At the end, we `assume` the expression from the `post` attribute.
Now we know `y` has value `42`.
The `validate` statement is necessary to encode a Boolean check against the post.

The body of the procedure is not used to encode a procedure call.
This is why it is also possible to declare `forty_two` without an associated body, but still call it inside another procedure.

You can find more details in our [OOPLSA '23 paper](../publications.md#oopsla-23).

:::caution

Right now, you can call procedures inside coprocedures and vice-versa.
This is basically never sound.
We'll fix that soon.

:::
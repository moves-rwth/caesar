# Expressions

## If-Then-Else

The `ite` built-in function allows to choose one of two expressions based on the result of a Boolean expression.
For example:
```
var x: UInt = ite(true, 32, 64);
```
The first parameter is the Boolean expression.
If it evaluates to `true`, the result of evaluating the second expression is returned.
Otherwise, the third expression is evaluated.

## Let

`let` expressions enable the declaration of local variables within an expression.
For example:
```
var x: UInt = let(b, true, ite(b, 32, 64));
```
The `let` expression creates a new local variable `b` and sets its value to `true`.
This variable `b` is available within the `let` expression's third argument.

In contrast to variable declaration statements using `var`, `let` expressions do not require type annotations.
The type of the variable is inferred from the second expression.

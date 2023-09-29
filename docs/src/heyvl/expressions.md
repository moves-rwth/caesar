# Expressions

For now, expressions are sparsely documented.
We refer to [`src/front/parser/grammar.lalrpop`](https://github.com/moves-rwth/caesar/blob/master/src/front/parser/grammar.lalrpop) for now for an exhaustive grammar for the complete language.

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

## Quantifiers

HeyVL features Boolean and quantitative quantifiers: `forall`, `exists`, `inf`, `sup`.
For example:
```
forall x: Int, y: UInt. x == y || x != y
```

**Triggers.**
We also support *triggers* for quantifiers via annotations.
They are *patterns* that will instruct the SMT solver to instantiate quantifiers if the pattern is found in the current list of terms it maintains.
For example:
```
forall list: []Int @trigger(len(list)). len(list) >= 0
```

*Multi-patterns* are also supported, by writing a comma-separated list inside the `@trigger` annotation:
```
forall list: []Int @trigger(len(list), len(list)). len(list) >= 0
```

For more information on how triggers/patterns work in general, see the [Z3 User Guide](https://microsoft.github.io/z3guide/docs/logic/Quantifiers/#patterns) and the [Dafny documentation](https://dafny.org/latest/DafnyRef/DafnyRef#sec-trigger).

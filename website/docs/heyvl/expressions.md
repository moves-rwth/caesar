---
description: HeyVL's expressions evaluate to a value in a state.
sidebar_position: 3
---

# Expressions

HeyVL expressions can be used inside [specifications](./procs.md) and [statements](./statements.md) and evaluate to values in some program state.

## Expression Syntax

The syntax of expressions (`Expr`) consists of the following parts:

* [Quantifiers](#quantifiers):
  * `inf Ident: Type, Ident: Type. Expr`
  * `sup Ident: Type, Ident: Type. Expr`
  * `forall Ident: Type, Ident: Type. Expr`
  * `exists Ident: Type, Ident: Type. Expr`
  * Quantifier annotations such as [triggers](#triggers) are also allowed, e.g. `forall Ident: Type @trigger(Expr). Expr`
* Boolean Operators (returning [type `Bool`](../stdlib/booleans.md)):
  * Logical And: `Expr && Expr`
  * Logical Or: `Expr || Expr`
  * Equals: `Expr == Expr`
  * Less Than: `Expr <= Expr`
  * Not Equals: `Expr != Expr`
  * Greater Or Equals: `Expr >= Expr`
  * Greater: `Expr > Expr`
* Binary Lattice and Heyting Algebra Operators (on types [`Bool`](../stdlib/) and [`EUReal`](../stdlib/numbers.md#eureal)):
  * Binary Minimum/Infimum: `Expr ⊓ Expr` or `Expr \cap Expr`
  * Binary Maximum/Supremum: `Expr ⊔ Expr` or `Expr \cup Expr`
  * Implication: `Expr → Expr` or `Expr ==> Expr`
  * Coimplication: `Expr ← Expr` or `Expr <== Expr` <small>(note that this is **not** just a flipped version of the implication `→`, but rather its lattice-theoretic dual!)</small>
  * Comparison: `Expr ↘ Expr`
  * Cocomparison: `Expr ↖ Expr`
* Arithmetical Operators (c.f. [number types](../stdlib/numbers.md)):
  * Addition: `Expr + Expr`
  * Subtraction/Monus: `Expr - Expr`
  * Multiplication: `Expr * Expr`
  * Division: `Expr / Expr`
  * Modulo: `Expr % Expr`
* Other Expressions:
  * [Let Expressions](#let-expressions): `let(Ident, Expr, Expr)`
  * [If-Then-Else Expressions](#if-then-else): `ite(Expr, Expr, Expr)`
  * [Function Calls](domains.md): `Ident(Expr, ..., Expr)`
  * Negation: `!Expr`
  * Conegation: `~Expr`
  * Embed: `?Expr` (usually written with parentheses: `?(Expr)`)
  * Iverson: `[Expr]`
  * Parentheses: `(Expr)`
* Literals:
  * String Literals: text enclosed by `"` characters (regular expression: `"[^"]*"`). <small>Note that Caesar does not support a proper `String` type yet.</small>
  * Integers: given by regular expression `[0-9]+` (default type: `UInt`)
  * Decimals: given by regular expression `[0-9]+\.[0-9]+` (default type: `UReal`)
  * Boolean Constants: `true` and `false`
* Identifiers (`Ident`): Names of things, from the language of the regular expression `[_a-zA-Z][_a-zA-Z0-9']*`.

Types (`Type`) are types from Caesar's [standard library](../stdlib/) and user-defined types from [domains](domains.md).

The above list is presented roughly in order of operator precedence.
Note that we plan to change some operator precedences, so when in doubt, use more parentheses to guarantee the correct interpretation.

The most precise grammar specification can be found in Caesar's source code ([`src/front/parser/grammar.lalrpop`](https://github.com/moves-rwth/caesar/blob/main/src/front/parser/grammar.lalrpop)).


## Semantics and Under-Specified Expressions

In [our paper on HeyVL (cf. Section 2)](https://arxiv.org/pdf/2309.07781.pdf#page=5), we give a formal semantics for *HeyLo*, our logic for reasoning about expected values.
HeyLo includes operators such as `==>`, `<==`, `!`, `~`, `?(e)`, and more.
Caesar's expressions are a superset of HeyLo.
In particular, the paper explains in detail the lattice and Heyting algebra operators that Caesar supports.

Note that some operations are not fully specified (*under-specified*).
The division and remainder operators (`Expr / Expr` and `Expr % Expr`) are not fully defined for all values.
Caesar translates these operators directly to SMT, where the SMT solver may assign arbitrary interpretations to e.g. divisions by zero.
You can find more information in the [Z3 documentation on division](https://microsoft.github.io/z3guide/docs/theories/Arithmetic/#division).

The `-` operator is always fully defined in Caesar.
On unsigned types such as `UInt`, it corresponds to *monus*, i.e. truncating subtraction that is always at least `0`.
On signed types such as `Int`, it corresponds to the usual subtraction.

## If-Then-Else

The `ite` built-in function allows to choose one of two expressions based on the result of a Boolean expression.
For example:
```heyvl
var x: UInt = ite(true, 32, 64);
```
The first parameter is the Boolean expression.
If it evaluates to `true`, the result of evaluating the second expression is returned.
Otherwise, the third expression is evaluated.

## Let Expressions

`let` expressions enable the declaration of local variables within an expression.
For example:
```heyvl
var x: UInt = let(b, true, ite(b, 32, 64));
```
The `let` expression creates a new local variable `b` and sets its value to `true`.
This variable `b` is available within the `let` expression's third argument.

In contrast to variable declaration statements using `var`, `let` expressions do not require type annotations.
The type of the variable is inferred from the second expression.

## Quantifiers

HeyVL features Boolean and quantitative quantifiers: `forall`, `exists`, `inf`, `sup`.
For example:
```heyvl
forall x: Int, y: UInt. x == y || x != y
```

### Triggers

We also support *triggers* for the Boolean quantifiers via annotations.
They are patterns that will instruct the SMT solver to instantiate quantifiers if the pattern is found in the current list of terms it maintains.
For example:
```heyvl
forall list: []Int @trigger(len(list)). len(list) >= 0
```

*Multi-patterns* are also supported, by writing a comma-separated list inside the `@trigger` annotation:
```heyvl
forall list: []Int @trigger(len(list), len(list)). len(list) >= 0
```

For more information on how triggers/patterns work in general, see the [Z3 User Guide](https://microsoft.github.io/z3guide/docs/logic/Quantifiers/#patterns) and the [Dafny documentation](https://dafny.org/latest/DafnyRef/DafnyRef#sec-trigger).


## Relative Completeness

Caesar's expression syntax is based on [the expressive assertion language for probabilistic verification by Batz et al](https://dl.acm.org/doi/10.1145/3434320).
In theory, *expressiveness* means that for many programs and properties, we know that we can express *all* pre-expectations and invariants in the expression syntax when a post-expectation is written in that syntax.

Formally, we have that the [weakest pre-expectation calculus](../proof-rules/calculi.md) `wp` is *relatively complete* with respect to this language, which means that `wp[P](post)` is effectively constructible for all programs `P` and expectations `post` in their syntax.

Their syntax includes enough constructs to specify many interesting properties, such as termination probabilities or the distribution over final states, even including stuff like harmonic numbers.
See [the paper's Section 12 for more details](https://dl.acm.org/doi/pdf/10.1145/3434320#page=26).

Of course, this does not mean that all of these verification problems are decidable.
It just means that in theory, the undecidable part is *only* in the final inequality check `pre <= wp[P](post)` instead of the computation of `wp[P](post)`.
[The section on SMT theories and incompleteness](../caesar/debugging.md#incompleteness) specifies which of these inequalities are actually decidable with Caesar.

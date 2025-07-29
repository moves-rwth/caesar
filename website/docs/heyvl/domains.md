---
description: User-defined functions, both definitional and uninterpreted with equality (EUF).
sidebar_position: 4
---

# Functions, Axioms, and Domains

This section covers how to extend HeyVL with custom functionality through domains.
Domains allow you to define your own functions and data types that can be used throughout your HeyVL programs.
This is useful for modeling operations or data structures that aren't built into the language.

Functions (`func`s) and axioms are always contained inside `domain` declarations.
A `domain` declaration is a way to group related functions and axioms together, and it also [creates a new type](#defining-types-with-domains) that can be used in HeyVL code.

There are two ways to define `func`s:
 1. [Definitional functions](#definitional-functions) with a body, which are preferred.
 2. [Uninterpreted functions](#axiomatizing-uninterpreted-functions) without a body, which are more flexible but allow less optimizations.

---

:::note Incompleteness

Note that definitional functions and axioms with quantifiers quickly introduce *incompleteness* of Caesar, making it unable to prove or disprove verification.
Read the documentation section on [SMT Theories and Incompleteness](../caesar/debugging.md#incompleteness) for more information.

:::

Caesar does some limited dependency tracking to determine which functions, axioms, and domains to translate into the final SMT formula.
In essence, a declaration will be translated only if there is a sequence of declarations starting from the translated procedure that leads to it.[^dependency-tracking]

[^dependency-tracking]: An axiom like `axiom unsound false` would never be translated by Caesar, because it does not mention any other declarations.
Therefore, Caesar will throw an error on such axioms.

## Definitional Functions

The preferred way to declare `func`s is to give a definition of the body with them.

Consider the following silly example, declaring a function for exponentials of ½.
```heyvl
domain Exponentials {
    func exp_05(exponent: UInt): UReal = ite(exponent == 0, 1, 0.5 * exp_05(exponent - 1))
}

proc ohfive_6() -> ()
    pre ?(true)
    post ?(exp_05(6) == 0.5 * 0.5 * 0.5 * 0.125)
{}
```


The domain `Exponentials` contains one func declaration `exp_05` with one parameter, `exponent` of type `UInt`.
It returns a value of type `UInt`, and its recursive definition is given after the equality sign.

:::note Function Encodings

Caesar supports many different encodings of definitional functions, which can be selected via the `--function-encoding` command-line option.
These can be used to tweak the SMT solver's reasoning and even guarantee termination of the underlying quantifier instantiation strategy.
[More information can be found in the debugging documentation](../caesar/debugging.md#function-encodings-and-limited-functions).

:::


## Axiomatizing Uninterpreted Functions

The alternative to defining funcs with bodies is to define them *uninterpreted*, that is, only defined by a bunch of axioms.

This is how the above example would look like then:
```heyvl
domain Exponentials {
    func exp_05(exponent: UInt): EUReal

    axiom exp_05_base exp_05(0) == 1
    axiom exp_05_step forall exponent: UInt. exp_05(exponent + 1) == 0.5 * exp_05(exponent)
}

proc ohfive_6() -> ()
    pre ?(true)
    post ?(exp_05(6) == 0.5 * 0.5 * 0.5 * 0.125)
{}
```

Here, we do not specify a body for `exp_05`.
Instead, we give two axioms, with names `exp_05_base` and `exp_05_step` respectively, to define both cases.
The first axiom simply specifies that `exp_05(0) == 1` holds (the base case), and the second one specifies that for all `exponent`, we can equate `exp_05(exponent + 1)` with `0.5 * exp_05(exponent)` (inductive case).

This way of defining functions is more flexible than [definitional functions](#definitional-functions), but Caesar cannot apply important optimizations this way.
Therefore, definitional functions should always be preferred if possible.

### Computable Annotation

The `@computable` annotation should be used on uninterpreted functions which are computable when given *literal* parameters.
This is only relevant when using the [`fuel-mono-computation` or `fuel-param-computation` function encodings](../caesar/debugging.md#function-encodings-and-limited-functions).
Then, calls to uninterpreted functions *inside definitional functions* with literal parameters are also considered literals, and the definitional function can be unfolded as many times as needed.

The annotation follows the definition, e.g.:
```heyvl
domain Exponentials {
    func exp_05(exponent: UInt): EUReal @computable
    // ...
}
```

## Axioms

### Axioms for Hints

Axioms can be used for both definitional functions and for uninterpreted functions.
For example, the verifier might need to know the fact that `exp_05(x) >= 1` always holds.
We can add the following axiom for both of the above definitions to let Caesar know this fact:
```heyvl
axiom exp_05_one forall exponent: UInt. exp_05(exponent) >= 1
```

### Axioms as Assumptions

One can see any axiom simply as an [`(co)assume` statement](./statements.md) added before the procedure to be verified.
For example,
```heyvl
axiom exp_05_step forall exponent: UInt. exp_05(exponent + 1) == 0.5 * exp_05(exponent)
```
can be written via an `assume` in just the same way:
```heyvl
assume ?(forall exponent: UInt. exp_05(exponent + 1) == 0.5 * exp_05(exponent))
```

:::warning Unsoundness from Axioms

Because axiom declarations behave like `assume` statements, they can introduce unsoundness in the same way.

<details>
    <summary>Example for unsoundness from axioms.</summary>

    ```heyvl
    domain Unsound {
        func f(): Bool
        axiom unsound false && f()
    }

    proc wrong() -> ()
        pre ?(true)
        post ?(true)
    {
        assert ?(false && f())
    }
    ```
    The axiom `unsound` always evaluates to `false`.
    But for verification, Caesar assumes the axioms hold for all program states.
    In other words, Caesar only verifies the program states in which the axioms evaluate to `true`.
    Thus, Caesar does not verify any program state and the procedure `wrong` incorrectly verifies!

</details>

:::

### Axioms and Limited Functions

When using [limited functions](../caesar/debugging.md#function-encodings-and-limited-functions), calls inside axioms have to be defined with respect to a certain *fuel* value, i.e. how many unfoldings of the function are allowed.

At the moment, Caesar will *only* define the axiom with one specific fuel value, which is the maximum defined by the `--max-fuel` command-line option (default: 2).
For example, the axiom from above would be translated to:
```heyvl
axiom exp_05_one forall exponent: UInt. exp_05($S($S($Z)), exponent) >= 1
```
where `$S($S($Z))` represents the fuel value of 2.
This behavior has implications with respect to [triggers](./expressions.md#triggers): the quantifier will only be instantiated by e-matching for the specific fuel value of 2.

## Defining Types with Domains

A `domain` declaration always creates a new uninterpreted type that can also be axiomatized.

Every domain type supports the binary operators `==` and `!=`.
All other operations must be encoded using functions and axioms.

The following example declares a `Tree` type with left and right branches, and where each leaf has a value of type `Int`.

```heyvl
domain Tree {
    func leaf(value: Int): Tree
    func node(left: Tree, right: Tree): Tree

    func is_leaf(tree: Tree): Bool
    axiom is_leaf_leaf forall value: Int. is_leaf(leaf(value)) == true
    axiom is_leaf_node forall t1: Tree, t2: Tree. is_leaf(node(t1, t2)) == false

    func get_value(tree: Tree): Int
    axiom get_value_def forall value: Int. get_value(leaf(value)) == value
}
```

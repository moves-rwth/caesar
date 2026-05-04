---
sidebar_position: 8
description: Caesar can export a Boolean fragment of HeyVL to Dafny.
---

# Dafny Backend

Caesar can export a supported Boolean fragment of HeyVL to [Dafny](https://dafny.org/).
This backend is **experimental** and currently aimed at **proof-oriented, Boolean** HeyVL programs:
top-level `proc`s with classical control flow, specifications of the form `?(b)`, and a small set of helper declarations.

The output is intended to be useful for verification, not especially idiomatic Dafny.
Generated methods use `decreases *`, declarations without bodies are translated axiomatically, and some translated files still need manual cleanup before Dafny accepts them.

## Usage

For a simple example, consider the following HeyVL procedure:

```heyvl
proc max_value(x: Int, y: Int) -> (m: Int)
    post ?(x <= m && y <= m)
    post ?(m == x || m == y)
{
    if x <= y {
        m = y
    } else {
        m = x
    }
}
```

This is the kind of input the backend is designed for:
classical control flow with Boolean specifications written as `?(b)`.

To export the file to Dafny, run:

```bash
caesar dafny example.heyvl --dafny-dir out --run-dafny
```

Caesar emits **one `.dfy` file per input `.heyvl` file** and mirrors the input path under the output directory.
The generated Dafny will contain a method shaped roughly like this:

```dafny
method max_value(x: int, y: int) returns (m: int)
    ensures ((x <= m) && (y <= m))
    ensures ((m == x) || (m == y))
    decreases *
{
    if (x <= y) {
        m := y;
    } else {
        m := x;
    }
}
```

In particular:

 * the output file is written as `out/.../example.dfy`
 * each `post ?(...)` becomes a Dafny `ensures`
 * a `proc` with a body becomes a Dafny `method` with `decreases *`
 * `--run-dafny` asks Caesar to invoke `dafny verify` on the generated file

For example,

```text
tests/boolean/procs/proc-smoke.heyvl
```

is written to

```text
out/tests/boolean/procs/proc-smoke.dfy
```

This requires the `dafny` executable to be available on the [`PATH`](https://en.wikipedia.org/wiki/PATH_(variable)).
If `--run-dafny` is used without `--dafny-dir`, Caesar writes the generated files to a temporary directory and verifies them there.

The command is also available as:

```bash
caesar to-dafny ...
```

`--filter <regex>` selects the root procedures to translate.
`--dafny-scope reachable` (the default) emits the selected procedures together with everything reachable from them.
`--dafny-scope all` emits every declaration from the selected file that the backend can translate, plus any reachable helpers needed from other files.
Unsupported declarations that are unreachable in `all` mode are skipped with a warning; unsupported required declarations still make translation fail.

## Supported Fragment

The backend expects ordinary HeyVL input using supported declarations and Boolean specifications.
Quantitative features and most proof-rule-specific encodings are out of scope.

### Declarations

 * top-level `proc` declarations
 * domain declarations
 * definitional `func`s
 * functions without bodies
 * axioms

### Specifications and Statements

 * `pre` and `post` conditions of the form `?(b)`
 * `assert ?(b)` and `assume ?(b)`
 * assignments, blocks, local variables, and conditionals
 * recursive and non-recursive procedure calls
 * `while` loops written as `@invariant(?(...)) while ...`
 * `havoc`

### Expressions and Types

 * `Bool`, `Int`, `UInt`
 * lists `[]T`, translated to Dafny sequences `seq<T>`
 * arithmetic and comparison operators
 * `&&`, `||`, `==>`, `!`, and `ite`
 * `forall` and `exists`
 * function and procedure calls
 * built-in list intrinsics `len`, `select`, and `store`
 * explicit quantifier triggers

## Translation

The translation is intentionally direct.
The most important choices are:

 * `Bool` becomes `bool`, `Int` becomes `int`, `UInt` becomes `nat`, and `[]T` becomes `seq<T>`.
 * Abstract HeyVL domains become Dafny type declarations of the form `type D(0,==)`.
 * `proc`s with bodies become Dafny `method`s with `decreases *`.
 * `proc`s without bodies become `method {:axiom}` declarations.
 * Definitional HeyVL functions become Dafny `function`s or `predicate`s.
 * `assert ?(b)` becomes `assert b`.
 * `assume ?(b)` becomes `assume {:axiom} b`.
 * `@invariant(?(b)) while ...` becomes a Dafny loop invariant together with `decreases *`.
 * Reachable HeyVL axioms are inserted as `assume {:axiom} ...;` statements into translated method bodies.

## Limitations

The backend currently does **not** support:

 * `coproc`
 * probabilistic primitives such as `flip`
 * quantitative expressions, quantitative casts, and non-Boolean embeddings
 * proof-rule-specific encodings and the richer quantitative core language
 * most proof-rule annotations beyond `@invariant(?(...))`

Some translated files still need manual adjustment before they pass `dafny verify`.
The most common issue at the moment is Dafny rejecting recursive helper functions over symbolic domains for lack of an acceptable termination argument.

At the moment, the backend is best viewed as a working export path for a supported Boolean fragment and a basis for experimenting with Dafny-oriented encodings.

## Examples

The repository contains small examples that exercise the backend:

 * translation smoke tests in [tests/dafny](https://github.com/moves-rwth/caesar/tree/main/tests/dafny)
 * curated Boolean examples in [tests/boolean/dafny_comparison](https://github.com/moves-rwth/caesar/tree/main/tests/boolean/dafny_comparison)

These include sequence-based sorting examples, symbolic list examples, and symbolic binary-search-tree examples.

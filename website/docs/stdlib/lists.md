---
sidebar_position: 3
---

# Lists

Caesar provides a built-in list type `[]T` where `T` is the element type.
Lists are array-like values with an associated length.

Use `[]T` for index-based algorithms.
If you need constructors such as `cons`, head/tail recursion, or structural induction, define your own datatype with [domains](../heyvl/domains.md).

## Operations

### `len`

```heyvl
func len(list: []T): UInt
```

Returns the length of `list`.

### `select`

```heyvl
func select(list: []T, index: UInt): T
```

Returns the element at `index`.

This operation is only specified for indices with `index < len(list)`.
For indices outside that range, do not rely on the result.

### `store`

```heyvl
func store(list: []T, index: UInt, value: T): []T
```

Returns a list obtained from `list` by replacing the element at `index` with `value`.

This operation is only specified for indices with `index < len(list)`.
For indices outside that range, do not rely on the result.

`store` preserves the length of the list.

## Equality

Lists support `==` and `!=`.

Built-in list equality is encoded *extensionally* in the SMT backend.
In the backend, the corresponding quantified formula is named `list_eq`.
Two lists are equal if they have the same length and the same elements at all valid indices.

```heyvl
len(a) == len(b) &&
forall i: UInt. (i < len(a)) ==> (select(a, i) == select(b, i))
```

This extensionality encoding is quantified, so it can make SMT proofs more brittle.

## Examples

The built-in API is enough for many length-preserving transformations.
For example, `fill` rewrites every valid index with the same value:

```heyvl
proc fill(list: []UInt, value: UInt) -> (res: []UInt)
    post ?(len(res) == len(list))
    post ?(forall k: UInt. (k < len(list)) ==> (select(res, k) == value))
{
    res = list
    var i: UInt = 0
    @invariant(?(
        i <= len(list) &&
        len(res) == len(list) &&
        (forall k: UInt. (k < i) ==> (select(res, k) == value))
    ))
    while (i < len(list)) {
        res = store(res, i, value)
        i = i + 1
    }
}
```

Operations that change the length are different.
The built-in API does not provide a constructor for a fresh longer list, so `append` and `concat` are currently best written as specification-only procedures:

```heyvl
proc append(list: []UInt, value: UInt) -> (res: []UInt)
    post ?(len(res) == len(list) + 1)
    post ?(select(res, len(list)) == value)
    post ?(forall k: UInt. (k < len(list)) ==> (select(res, k) == select(list, k)))

proc concat(left: []UInt, right: []UInt) -> (res: []UInt)
    post ?(len(res) == len(left) + len(right))
    post ?(forall k: UInt. (k < len(left)) ==> (select(res, k) == select(left, k)))
    post ?(forall k: UInt. (k < len(right)) ==> (select(res, len(left) + k) == select(right, k)))
```

More checked examples are in [`tests/boolean/procs/list_ops.heyvl`](https://github.com/moves-rwth/caesar/blob/main/tests/boolean/procs/list_ops.heyvl).

## Remarks

Built-in lists are encoded as an SMT array together with a length.
Bounds such as `i < len(list)` should usually be stated explicitly in specifications.

Counterexamples print lists in a compact form such as `[4, 10] (len=2, oob: default=4, -1 -> 12)`.
The bracketed part shows the in-bounds elements.
The optional `oob` part shows values that the SMT model assigns outside the valid range `0 .. len(list) - 1`; these are not part of the specified list contents.
Longer lists may be truncated to `[a, b, ...] (len=n, ...)`.

Many list properties are quantified.
For nontrivial quantified proofs, [triggers](../heyvl/expressions.md#triggers) may matter.
See [debugging quantifier instantiations](../caesar/debugging.md#debugging-quantifier-instantiations) for details.

The built-in `[]T` type is intended for index-based reasoning.
If you need a recursive list datatype, define one with [domains](../heyvl/domains.md).

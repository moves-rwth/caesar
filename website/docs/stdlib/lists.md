---
sidebar_position: 3
---

# Lists

The standard library includes a type for lists `[]T` where `T` is the type of elements.

 * **Length**: `func len(list: []T): UInt`.
 * **Element Access**: `func select(list: []T, index: UInt): T`.
 * **Storing elements**: `func store(list: []T, index: UInt, value: T): []T`.

## Discussion

The SMT-LIB translation of lists is based on SMT-LIB's arrays, but our lists have a length associated with it.
You are only supposed to access elements at indices `< len(list)`.

Some SMT solvers also support [Sequences](https://microsoft.github.io/z3guide/docs/theories/Sequences), but we do not yet understand those well enough to say how they compare to our lists.


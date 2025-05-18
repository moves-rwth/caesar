---
sidebar_position: 4
---

# Optimizations & Alternative Implementations

By default, Caesar uses a set of optimizations to speed up validity checking of verification conditions.
You can experiment with them by disabling them and choosing between alternative implementations of some algorithms.

## Command-Line Options

See `--help` for more detailed information.

 * Disabling quantifier elimination: `--no-qelim`.
 * Strict verification condition unfolding: `--strict`.
 * Enable e-graph optimization: `--egraph`. The result is currently not used for the SMT encoding.

## Compilation Options

Most of Caesar's behaviour can be changed with command-line flags, but there are three possible SMT encodings of the `EUReal` type which must be chosen from at compile time.

Compile with `--features datatype-eureal` to build an executable that encodes `EUReal` values using SMT-LIB datatypes instead of an encoding that uses a Boolean and a Real number directly.
Our experiments have shown that this is usually slower.

You can also compile with `--features datatype-eureal-funcs` to use the datatype SMT-LIB encoding where additionally implementations of multiplications, additions, and less-than-or-equal relations are encoded as SMT-LIB functions.
This is the slowest encoding, but it's the easiest to read.

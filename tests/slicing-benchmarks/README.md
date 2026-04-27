# Slicing Benchmarks

This directory contains benchmark programs for Caesar's slicing
implementation. Some benchmarks are standalone examples, while others are
derived from programs that also appear in the regular `tests` tree.

The slicing copies are kept when they are modified for a slicing experiment,
for example by adding `@slice_verify`, expanding a loop rule into explicit
proof obligations, or deliberately introducing an error for error-witnessing
slices. Exact byte-for-byte duplicates of regular tests should not be kept here.

Canonical non-slicing tests live outside this directory, typically under
`tests/loop-rules`, `tests/core`, or `tests/case-studies`.

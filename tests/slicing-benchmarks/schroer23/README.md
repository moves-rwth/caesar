# Schroer 2023 Slicing Benchmarks

These files are based on examples used around the slicing experiments by
Schroer. Several subdirectories mirror examples from `tests/loop-rules`, but
the files here are benchmark variants rather than the canonical regression
tests.

- `park_induction_ert/original`: header-stripped source programs used as input
  examples for slicing.
- `park_induction_ert/verification_preserving`: variants annotated with
  `@slice_verify` to exercise verification-preserving slicing.
- `park_induction_ert/error_witnessing`: deliberately broken variants used to
  exercise error-witnessing slices.
- `k_induction`: explicit k-induction proof-obligation encodings derived from
  the corresponding `tests/loop-rules/k_induction` examples.
- `other_loop_rules`: slicing benchmarks for loop rules not covered by the
  Park-induction families.

Exact duplicates of regular tests are intentionally omitted from this subtree.

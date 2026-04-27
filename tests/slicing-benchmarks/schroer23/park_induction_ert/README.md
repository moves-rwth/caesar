# Park Induction ERT Benchmarks

These benchmarks are derived from the ERT Park-induction examples in
`tests/loop-rules/induction`.

The `original` directory contains source programs with the normal test headers
removed. The `verification_preserving` directory contains variants annotated
with `@slice_verify` to show statements or blocks considered by
verification-preserving slicing. The `error_witnessing` directory contains
deliberately modified programs whose proof obligations fail, so slicing can
identify smaller error witnesses.

Because these files are benchmark variants, they may share filenames with
regular tests without being byte-for-byte duplicates.

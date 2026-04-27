# K-Induction Slicing Benchmarks

These files are derived from `tests/loop-rules/k_induction`.

The regular tests use the `@k_induction` loop annotation. The slicing benchmark
versions expand that rule into explicit proof obligations using
`assert`/`coassert`, `havoc`/`cohavoc`, `validate`/`covalidate`, and
`assume`/`coassume`, followed by explicit copies of the loop body. This makes
the generated obligations available to the slicing implementation as ordinary
HeyVL code.

The `_wlp` files are the corresponding WLP versions.

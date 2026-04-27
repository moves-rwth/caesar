# Bounded Model Checking Slicing Benchmarks

These files are derived from `tests/loop-rules/bmc`.

The regular tests use bounded unrolling annotations such as `@unroll(k, 0)`.
The slicing benchmark versions replace those loops with explicit nested `if`
statements and terminal error-witness statements. They are intentionally not
byte-for-byte copies of the canonical BMC tests.

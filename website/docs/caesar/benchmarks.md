---
sidebar_position: 5
---

# Benchmarks

The following command checks all examples that we know to work.
It completes in about 20s on my machine.

```shell
export RUST_LOG="caesar=trace"
cd pgcl/examples-heyvl
cargo run --release  -- --raw unif_gen1.heyvl rabin1.heyvl rabin2.heyvl brp1.heyvl geo1.heyvl
```

The CAV artifact image includes `artifact/run-all-benchmarks.sh`, which executes
the checked-in HeyVL tests under `tests/` through the `// RUN:` directives at the
top of the files. The script writes a console log to `benchmark-results.txt` and
per-file timing data to `benchmark-results.csv`.

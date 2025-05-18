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

You can run the benchmark set with evaluations by executing `fish run-benchmarks.fish` ([fish shell](https://fishshell.com/) is required).

One possible output of `fish run-benchmarks.fish | column -ts ","` is the following:
```
Name             Result  Total Time  VCgen Time  SAT Check Time
brp1.heyvl       IND     1.54s       0.02s       1.2s
brp2.heyvl       OOM     17.39s
brp3.heyvl       OOM     17.29s
fail-geo1.heyvl  REF     0.18s       0s          0.03s
geo1.heyvl       IND     0.2s        0s          0.04s
linear01.heyvl   IND     0.19s       0s          0.02s
rabin1.heyvl     IND     0.5s        0s          0.03s
rabin2.heyvl     IND     13.95s      0.23s       10.1s
unif_gen1.heyvl  IND     6.97s       0.02s       6.61s
unif_gen2.heyvl  TO      0.52s
unif_gen3.heyvl  TO      0.48s
unif_gen4.heyvl  OOM     17.54s
```


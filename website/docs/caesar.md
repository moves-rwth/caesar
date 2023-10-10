---
sidebar_position: 6
---

# The Caesar CLI

The `caesar` verifier takes a HeyVL program as input and tries to determine whether it _verifies_.

**Compile** the `caesar` binary with `cargo build --release`.
The executable can be found at `target/release/caesar`.
In the following, we just write `caesar` for the executable.
Omit `--release` for the a binary with less optimizations; the result will be in `target/debug/caesar`.

**Print help:**
`caesar --help`.

**Verify HeyVL files:**
`caesar file1.heyvl file2.heyvl ...`
Adding `--raw` indicates that input files consist only of a sequence [HeyVL statements](./heyvl/statements.md) and that no declarations such as procedures are expected.

**Timeouts and memory limits:**
Set a timeout of 60 seconds using `--timeout 60`.
Set a memory limit of 16000 megabytes with `--mem 16000`.

**Print tracing messages:**
Caesar uses the [`tracing` library](https://github.com/tokio-rs/tracing) to print (debugging) information during its operation.
Set the `RUST_LOG` environment variable to specify a filter, e.g. `export RUST_LOG="caesar=debug"` or `export RUST_LOG="caesar::smt=trace"`.

**Print intermediate data:**
* With the `--print-parsed` flag, Caesar pretty-prints the HeyVL code after parsing.
* With the `--print-core` flag, Caesar prints the HeyVL code after parsing, type-checking, and desugaring.
* With the `--print-theorem` flag, Caesar prints the theorem that is encoded into SMT.
* With the `--print-smt` flag, Caesar prints the SMT-LIB query for each verification task. You can also use `--smt-dir DIR` with a directory `DIR` to have Caesar write the SMT-LIB queries to files in `DIR`.

## Benchmarks

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

## Optimizations & Alternative Implementations

By default, Caesar uses a set of optimizations to speed up validity checking of verification conditions.
You can experiment with them by disabling them and choosing between alternative implementations of some algorithms.

### Command-Line Options

See `--help` for more detailed information.

 * Disabling quantifier elimination: `--no-qelim`.
 * Strict verification condition unfolding: `--strict`.
 * Enable e-graph optimization: `--egraph`. The result is currently not used for the SMT encoding.

### Compilation Options

Most of Caesar's behaviour can be changed with command-line flags, but there are three possible SMT encodings of the `EUReal` type which must be chosen from at compile time.

Compile with `--features datatype-eureal` to build an executable that encodes `EUReal` values using SMT-LIB datatypes instead of an encoding that uses a Boolean and a Real number directly.
Our experiments have shown that this is usually slower.

You can also compile with `--features datatype-eureal-funcs` to use the datatype SMT-LIB encoding where additionally implementations of multiplications, additions, and less-than-or-equal relations are encoded as SMT-LIB functions.
This is the slowest encoding, but it's the easiest to read.

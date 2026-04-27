# Caesar CAV 2026 Artifact

Artifact for **_Caesar: A Deductive Verifier for Probabilistic Programs_**.

This Docker image contains Caesar v4.0.0, Storm 1.12.0, Caesar's source code, the HeyVL benchmark set, the slicing benchmark suite, and scripts for smoke testing and running all core benchmarks. The image does not install the older `pgcl2heyvl` frontend; all benchmark inputs are included as HeyVL files.

The main Caesar website is <https://www.caesarverifier.org/> and the online documentation is at <https://www.caesarverifier.org/docs/>. The online documentation is the preferred way to read the docs because navigation, search, and links are most convenient there. For artifact review, this image also contains the same documentation offline in Markdown source form and as compiled static HTML. The website may use Google Analytics, so anonymity cannot be guaranteed when using the online site.

## Quick Start

Run the smoke test:

```bash
artifact/run-smoke.sh
```

Expected result: `tests/case-studies/zeroconf.heyvl` verifies two procedures.

Run the model-checking smoke test:

```bash
artifact/run-model-checking-smoke.sh
```

Expected result: Caesar runs checked-in examples through Storm: bounded-loop Markov chains, the Crowds anonymity protocol, Herman's self-stabilizing token-ring protocol, a noisy-OR Bayesian-network style model, and a BRP send-packet instance.

Run all benchmarks:

```bash
artifact/run-all-benchmarks.sh
```

The full run executes `python3 benchmarks.py`, which discovers checked-in HeyVL benchmark tests and runs their `RUN` commands with the Caesar binary from the image. The script writes `benchmark-results.txt`.

Many HeyVL test files begin with comments such as `// RUN:`, `// XFAIL:`, or `// IGNORE:`. These are test-runner directives: `RUN` gives the command to execute for that file, `XFAIL` marks an expected failure, and `IGNORE` excludes a file from the automatic benchmark run.

Offline documentation in this container:

* Markdown source: `/root/caesar/website/docs/`
* Compiled HTML: `/root/caesar/website/build/index.html`

## Claims And Tests

| Claim | How to test it | Expected result |
| --- | --- | --- |
| Caesar and Storm are available in this container. | `caesar --help` and `storm --version` | Caesar prints usage information; Storm reports version 1.12.0. |
| Caesar verifies quantitative HeyVL programs automatically using SMT-generated verification conditions. | `artifact/run-smoke.sh` | `tests/case-studies/zeroconf.heyvl` verifies both procedures. |
| Caesar can translate executable HeyVL programs to JANI and run probabilistic model checking through Storm. | `artifact/run-model-checking-smoke.sh` | Caesar invokes `storm` via `--run-storm path` on the examples in `tests/model-checking/` and checks the expected results. |
| Representative tests cover the main verification features discussed in the paper. | Run the commands in **Tests By Feature**. | Each command reports verified procedures and exits successfully. |
| Program slicing support and slicing benchmarks are included. | `caesar verify --slice-verify tests/slicing-benchmarks/navarro20/example4_3.heyvl` | The representative slicing benchmark verifies with slicing for correctness enabled. |
| The paper benchmark set is included and executable. | `artifact/run-all-benchmarks.sh` | `benchmarks.py` discovers the checked-in benchmark tests, prints pass/fail results, and writes `benchmark-results.txt`. |
| Benchmark provenance is documented. | Read **All Benchmarks**. | Each benchmark group is mapped to a source paper, benchmark family, or Caesar case study. |
| Caesar's documentation is available both online and offline. | Read <https://www.caesarverifier.org/docs/> or inspect `/root/caesar/website/docs/` and `/root/caesar/website/build/`. | The artifact provides Markdown documentation sources and a compiled static HTML copy. |

## Tests By Feature

| Feature | Representative command |
| --- | --- |
| Quantitative HeyVL verification | `caesar verify tests/case-studies/zeroconf.heyvl` |
| Domains and axioms | `caesar verify tests/loop-rules/induction/rabin_hurd2004.heyvl` |
| Loop induction | `caesar verify pgcl/examples-heyvl/rabin1.heyvl` |
| k-induction | `caesar verify pgcl/examples-heyvl/brp2.heyvl` |
| wp/wlp variants | `caesar verify pgcl/examples-heyvl/unif_gen1.heyvl` and `caesar verify pgcl/examples-heyvl/unif_gen1_wlp.heyvl` |
| Conditional expectations | `caesar verify tests/loopfree-prob/six-sided-die.heyvl` |
| Model checking via JANI and Storm | `artifact/run-model-checking-smoke.sh` |
| Expected runtime / ticks | `caesar verify tests/loop-rules/omega_invariants/countdown.heyvl` |
| Almost-sure termination | `caesar verify tests/loop-rules/ast2018/ast-flipflop_core.heyvl` |
| Positive almost-sure termination | `caesar verify tests/loop-rules/past2013/past.heyvl` |
| Optional-stopping lower bounds | `caesar verify tests/loop-rules/ost2019/aiming-low-example39.heyvl` |
| Program slicing | `caesar verify --slice-verify tests/slicing-benchmarks/navarro20/example4_3.heyvl` |
| Modular calls | `caesar verify pgcl/examples-heyvl/fcall.heyvl` |

Useful inspection commands:

```bash
caesar verify --help
caesar verify --print-theorem tests/case-studies/zeroconf.heyvl
caesar verify --print-smt tests/case-studies/zeroconf.heyvl
```

## All Benchmarks

The core benchmark set is listed exactly in `benchmarks.txt`. It covers:

* Rabin mutual exclusion: examples based on Hurd, McIver, and Morgan, _Probabilistic Guarded Commands Mechanized in HOL_ (QAPL 2004), and the Kushilevitz/Rabin protocol from _Randomized Mutual Exclusion Algorithms Revisited_ (PODC 1992).
* Uniform generation: wp/wlp variants based on Lumbroso, _Optimal Discrete Uniform Generation from Coin Flips, and Applications_ (arXiv:1304.1916).
* Bounded retransmission protocol: D'Argenio, Katoen, Ruys, and Tretmans, _The Bounded Retransmission Protocol Must Be on Time!_ (TACAS 1997).
* Expected-runtime benchmark suite: `2drwalk`, `bayesian_network`, `C4B_t303`, `condand`, `fcall`, `hyper`, `linear01`, `prdwalk`, `prspeed`, `rdspeed`, `rdwalk`, and `sprdwalk`, from the NCH/Absynth examples of Ngo, Carbonneaux, and Hoffmann, _Bounded Expectations: Resource Analysis for Probabilistic Programs_ (PLDI 2018).
* Chain/list examples: small infinite-state examples with user-defined domains.
* Caesar case studies: coupon collector, recursive geometric process, and Zeroconf, as reported in the Caesar OOPSLA 2023 evaluation.
* Conditional expectations: `die`, following the conditional wp/wlp setting of Olmedo et al., _Conditioning in Probabilistic Programming_ (TOPLAS 2018).
* AST/PAST/OST proof rules: examples from McIver et al., _A New Proof Rule for Almost-Sure Termination_ (POPL 2018); Chakarov and Sankaranarayanan, _Probabilistic Program Analysis with Martingales_ (CAV 2013); and Hark et al., _Aiming Low Is Harder_ (POPL 2020).
* Small wp/lower-bound examples: `geo1` and `omega`.
* Slicing benchmarks: 85 HeyVL files in `tests/slicing-benchmarks/`, covering slicing for errors and slicing for correctness on classical, probabilistic, conditioning, continuous, and Caesar case-study examples.

The benchmark classification follows Section 5.2 and Table 2 of the OOPSLA 2023 Caesar paper, _A Deductive Verification Infrastructure for Probabilistic Programs_ (extended version arXiv:2309.07781).

## Source Layout

* `src/`: Caesar's main implementation.
* `src/driver/`: command-line commands and verification driver.
* `src/vc/`: verification-condition generation.
* `src/smt/` and `z3rro/`: SMT encoding and Z3 interaction.
* `src/proof_rules/`: built-in proof rules.
* `src/slicing/`: slicing support.
* `tests/model-checking/`: compact executable HeyVL examples for Caesar's JANI/Storm backend.
* `tests/` and `pgcl/examples-heyvl/`: HeyVL benchmark files.
* `tests/slicing-benchmarks/`: slicing benchmark suite.
* `website/docs/`: offline Markdown documentation source.
* `website/build/`: offline compiled HTML documentation.

# CAV 2026 Artifact: Caesar

Artifact for the CAV 2026 paper **_Caesar: A Deductive Verifier for Probabilistic Programs_**.

Caesar is a deductive verifier for probabilistic programs written in HeyVL. It supports quantitative assertions over expectations, verification-condition generation, SMT-based proof obligations, loop proof rules, and probabilistic model checking via JANI and Storm. This artifact contains Caesar v4.0.0, Storm 1.12.0, the benchmark set, the source code, and a Docker image recipe.

The main Caesar website is <https://www.caesarverifier.org/> and the online documentation is at <https://www.caesarverifier.org/docs/>. The online documentation is the preferred way to read the docs because navigation, search, and links are most convenient there. For artifact review, the Docker image also contains the same documentation offline in Markdown source form and as compiled static HTML. The website may use Google Analytics, so anonymity cannot be guaranteed when using the online site.

## Table of Contents

- [CAV 2026 Artifact: Caesar](#cav-2026-artifact-caesar)
  - [Table of Contents](#table-of-contents)
  - [Badge Summary](#badge-summary)
  - [Getting Started](#getting-started)
  - [Running Tests And Benchmarks](#running-tests-and-benchmarks)
  - [Tests By Feature](#tests-by-feature)
  - [Benchmark Set](#benchmark-set)
  - [Using Caesar Beyond The Paper](#using-caesar-beyond-the-paper)
  - [Using The VS Code Extension](#using-the-vs-code-extension)
  - [Artifact Contents And Source Structure](#artifact-contents-and-source-structure)

## Badge Summary

This artifact is prepared for the CAV 2026 **Available**, **Functional**, and **Reusable** badges.

* **Available:** the artifact is archived with a DOI on Zenodo. The artifact is distributed under the MIT license, and the submitted package includes `LICENSE`.
* **Functional:** the submitted Docker image supports `linux/amd64` and `linux/arm64`, needs no network access once downloaded, and contains Caesar, Storm, smoke tests, representative feature checks, and the artifact-wide benchmark test runner.
* **Reusable:** the image contains Caesar's source code, benchmark inputs, Dockerfile, build scripts, Markdown documentation, compiled HTML documentation, and examples for running Caesar on further HeyVL files. The submitted zip also includes a prebuilt VS Code extension for interactive use.

## Getting Started

Requirements:

* Docker.
* 16 GB RAM.
* Enough disk space for the image and unpacked artifact.
* Intended architectures: `linux/amd64` and `linux/arm64`.
* No external network connectivity is needed to run the Docker image.

Load the submitted image:

```bash
docker image load -i image.tar.gz
```

Enter the artifact environment:

```bash
docker run -it caesar:cav26-aec
```

This opens a shell in `/root/caesar`. The `caesar` command is on `PATH`.
The `storm` binary is also on `PATH`.

Documentation locations inside the container:

* Markdown source: `/root/caesar/website/docs/`
* Compiled HTML: `/root/caesar/website/build/index.html`

The compiled HTML can be inspected from inside the container, copied out, or served with any static-file server. The online docs at <https://www.caesarverifier.org/docs/> are usually easier to use, but using the public website may reveal access metadata and may be subject to Google Analytics.

## Running Tests And Benchmarks

For a quick smoke test, run:

```bash
artifact/run-smoke.sh
```

Expected result: Caesar verifies `tests/case-studies/zeroconf.heyvl` and reports two verified procedures. This should take less than a minute on a typical laptop.

For model checking with Storm, run:

```bash
artifact/run-model-checking.sh
```

Expected result: Caesar runs checked-in examples through Storm: bounded-loop Markov chains, the Crowds anonymity protocol, Herman's self-stabilizing token-ring protocol, a noisy-OR Bayesian-network style model, and a BRP send-packet instance.

To execute the automated benchmark suite at once, run:

```bash
artifact/run-all-benchmarks.sh
```

This executes `python3 benchmarks.py`, which discovers HeyVL files under `tests/` and runs their `RUN` commands with the Caesar binary from the image. The wrapper writes the console log to `benchmark-results.txt`; the Python runner also writes per-file timings to `benchmark-results.csv`.

The HeyVL test files begin with comments such as `// RUN:`, `// XFAIL:`, or `// IGNORE:`. These are test-runner directives: `RUN` gives the command to execute for that file, `XFAIL` marks an expected failure, and `IGNORE` excludes a file from the automatic benchmark run.

Expected time: usually under 10 minutes on a MacBook Pro with M2 Pro; slower virtualized Docker setups may take longer.

## Tests By Feature

The following examples demonstrate the main features of Caesar presented in the paper. They are all included in the image under `/root/caesar`.

Figure 1 of the paper shows an excerpt of the bounded retransmission protocol send-packet example. The full version is included in the Docker image as `tests/case-studies/brp-send-packet.heyvl`.

| Feature | Representative command | What it demonstrates |
| --- | --- | --- |
| User-defined domains and axioms | `caesar verify tests/case-studies/zeroconf.heyvl` | Reasoning about Rabin's mutual exclusion protocol with auxiliary mathematical functions. |
| Park Induction on probabilistic loops | `caesar verify pgcl/examples-heyvl/rabin1.heyvl` | A loop proof using expectation-based Park induction. |
| k-induction | `caesar verify pgcl/examples-heyvl/brp2.heyvl` | A bounded-retransmission-protocol proof requiring k-induction. |
| wp/wlp variants | `caesar verify pgcl/examples-heyvl/unif_gen1.heyvl` and `caesar verify pgcl/examples-heyvl/unif_gen1_wlp.heyvl` | The same family of examples checked under different expectation calculi. |
| Conditional expectations | `caesar verify tests/loopfree-prob/six-sided-die.heyvl` | Conditional wp/wlp reasoning via observations. |
| Model checking via JANI and Storm | `caesar mc --run-storm path --storm-exact --storm-constants messages=5,threshold=1 tests/model-checking/crowds-anonymity.heyvl` | Translation of executable HeyVL to JANI and expected-reward computation with Storm. |
| Expected-runtime reasoning | `caesar verify tests/loop-rules/omega_invariants/countdown.heyvl` | Lower-bound expected-runtime reasoning with an omega invariant. |
| Almost-sure termination | `caesar verify tests/loop-rules/ast2018/ast-flipflop_core.heyvl` | The AST proof rule of McIver, Morgan, Kaminski, and Katoen. |
| Positive almost-sure termination | `caesar verify tests/loop-rules/past2013/past.heyvl` | A PAST proof based on ranking-supermartingale style conditions. |
| Optional-stopping lower bounds | `caesar verify tests/loop-rules/ost2019/aiming-low-example39.heyvl` | The optional-stopping-theorem proof pattern from _Aiming Low Is Harder_. |
| Program slicing | `caesar verify --slice-verify tests/slicing-benchmarks/navarro20/example4_3.heyvl` | Slicing for correctness on a benchmark from the slicing suite. |
| Procedures and modular calls | `caesar verify tests/case-studies/zeroconf.heyvl` | Procedure calls and modular verification obligations. |

Useful inspection commands:

```bash
caesar verify --help
caesar verify --print-theorem tests/case-studies/zeroconf.heyvl
caesar verify --print-smt tests/case-studies/zeroconf.heyvl
```

## Benchmark Set

The benchmark set in `caesar/tests/**/*.heyvl` contains the benchmarks from the OOPSLA 2023 and ESOP 2026 papers on Caesar and additional examples. The benchmark runner uses the comments at the beginning of the file to determine the command for each benchmark. The table below records the benchmark families and their source or purpose.

| Group | Representative entries | Source / purpose |
| --- | --- | --- |
| Rabin mutual exclusion | `rabin`, `rabin1`, `rabin2`, `rabin1_wlp`, `rabin2_wlp`, `rabin3_wlp` | Rabin's randomized mutual-exclusion protocol based on the formalization of Hurd, McIver, and Morgan, _Probabilistic Guarded Commands Mechanized in HOL_ (QAPL 2004); the protocol is from Kushilevitz and Rabin, _Randomized Mutual Exclusion Algorithms Revisited_ (PODC 1992). |
| Uniform generation | `unif_gen1_wp` ... `unif_gen4_wp`, `unif_gen1_wlp` ... `unif_gen4_wlp` | Uniform discrete number generation examples using wp/wlp encodings and latticed k-induction. The algorithm is based on Lumbroso, _Optimal Discrete Uniform Generation from Coin Flips, and Applications_ (arXiv:1304.1916). |
| Bounded retransmission protocol | `brp1`, `brp2`, `brp3` | Bounded retransmission protocol (BRP) examples, based on D'Argenio, Katoen, Ruys, and Tretmans, _The Bounded Retransmission Protocol Must Be on Time!_ (TACAS 1997). |
| Expected-runtime benchmark suite | `2drwalk`, `bayesian_network`, `C4B_t303`, `condand`, `fcall`, `hyper`, `linear01`, `prdwalk`, `prspeed`, `rdspeed`, `rdwalk`, `sprdwalk` | `ert` examples translated from the NCH/Absynth benchmark family used in Ngo, Carbonneaux, and Hoffmann, _Bounded Expectations: Resource Analysis for Probabilistic Programs_ (PLDI 2018), showing expected-runtime bounds. |
| Chain/list examples | `chain`, `ohfive` | Hand-written Caesar examples for upper bounds on expected values using Park induction, recursive functions, and, for `ohfive`, a nested loop using the List datatype. |
| Caesar case studies | `coupon`, `geo-recursive`, `zeroconf` | Hand-written case studies used in the Caesar OOPSLA 2023 evaluation: coupon collector, recursive geometric process, and Zeroconf. |
| Conditional expectations | `die` | Conditional wp/wlp example over a six-sided die from the OOPSLA 2023 benchmark set based on the conditioning semantics of Olmedo et al., _Conditioning in Probabilistic Programming_ (TOPLAS 2018). |
| Lower-bound and expected-runtime proof rules | `ost`, `omega` | `ost` is Example 39 from Hark, Kaminski, Giesl, and Katoen, _Aiming Low Is Harder_ (POPL 2020). `omega` is a countdown example using omega-invariants to show a lower bound on the expected-runtime. |
| Termination proof rules | `ast1`, `ast2`, `ast3`, `ast4`, `past` | Almost-sure termination (AST) examples from McIver, Morgan, Kaminski, and Katoen, _A New Proof Rule for Almost-Sure Termination_ (POPL 2018). `past` demonstrates the Chakarov and Sankaranarayanan positive AST rule example from _Probabilistic Program Analysis with Martingales_ (CAV 2013). |
| k-Induction | `geo1` | A small geometric-loop wp example using k-induction as a proof method; from the OOPSLA 2023 benchmarks. |
| Slicing benchmarks | `tests/slicing-benchmarks/` | HeyVL files for slicing for errors and slicing for correctness from the ESOP 2026 benchmarks. The suite includes classical slicing examples, probabilistic slicing examples, conditioning examples, continuous-program examples, Park-induction diagnostics, and existing benchmark variants. |

The commands used by the benchmark runner are the `// RUN:` directives at the top of the HeyVL files.


## Using Caesar Beyond The Paper

New problems can be encoded as HeyVL programs in `.heyvl` files.
Caesar checks them using the  `caesar verify` command, e.g.: Most examples in this artifact can be run directly from `/root/caesar`, e.g.:

```bash
caesar verify tests/case-studies/zeroconf.heyvl
```

It is also possible to modify existing benchmarks or try the different features like slicing or the model-checking backend via command-line arguments:

```bash
caesar verify --slice-verify tests/slicing-benchmarks/navarro20/example4_3.heyvl
caesar mc --run-storm path --storm-exact --storm-constants messages=5,threshold=1 tests/model-checking/crowds-anonymity.heyvl
```

Command-specific help is available with `caesar verify --help` and `caesar mc --help`.
To inspect the internal verification condition and SMT query, the options `--print-theorem` and `--print-smt` can be used.
For a short language and tool introduction, see the getting-started guide in `/root/caesar/website/docs/getting-started/README.md` and `/root/caesar/website/docs/getting-started/heyvl-guide.md`, or the online guide at <https://www.caesarverifier.org/docs/getting-started/>.

## Using The VS Code Extension

The artifact zip includes a prebuilt VS Code extension:

```bash
code --install-extension caesar-vscode-extension.vsix
```

Alternatively, use **Extensions: Install from VSIX...** in the VS Code command palette and select `caesar-vscode-extension.vsix`.

The extension provides HeyVL syntax highlighting, snippets, diagnostics, gutter status icons, inline verification condition calculations and the `Caesar: Verify` command. It invokes a Caesar binary, so configure the extension to use one of these:

* When using VS Code attached to the artifact container:
  * Set `caesar.server.installationOptions` to `userBinary`.
  * Set `caesar.server.binaryPath` to `/usr/local/bin/caesar`.
* When using VS Code on the host:
  * Install or build Caesar on the host.
  * Set `caesar.server.installationOptions` to `userBinary`.
  * Set `caesar.server.binaryPath` to the host path of the `caesar` binary.

The command-line artifact does not require VS Code; the extension is included for interactive inspection and reuse.

## Artifact Contents And Source Structure

The submitted zip file follows the CAV 2026 Docker artifact layout:

* `image.tar.gz`: Docker image archive for `caesar:cav26-aec`.
* `caesar-vscode-extension.vsix`: prebuilt VS Code extension for HeyVL editing and interactive Caesar runs.
* `README`: this artifact README.
* `LICENSE`: artifact license.

Inside the image, the artifact is organized around the Caesar repository and a small set of review scripts:

* Main checkout:
  * `caesar/`: Caesar v4.0.0 source checkout from <https://github.com/moves-rwth/caesar>.
* Implementation:
  * `caesar/src/`: Caesar's main implementation.
  * `caesar/src/driver/`: command-line commands and verification driver.
  * `caesar/src/vc/`: verification-condition generation.
  * `caesar/src/smt/` and `caesar/z3rro/`: SMT encoding and Z3 interaction.
  * `caesar/src/proof_rules/`: built-in proof rules.
  * `caesar/src/slicing/`: slicing support.
* Benchmark and test inputs:
  * `caesar/tests/` and `caesar/pgcl/examples-heyvl/`: HeyVL verification benchmarks and case studies.
  * `caesar/tests/case-studies/brp-send-packet.heyvl`: full version of the Figure 1 bounded retransmission protocol example.
  * `caesar/tests/slicing-benchmarks/`: slicing benchmark suite with classical, probabilistic, conditioning, continuous, and Caesar case-study examples.
  * `caesar/tests/model-checking/`: executable HeyVL examples for Caesar's JANI/Storm model-checking backend.
* Review scripts and Docker files:
  * `caesar/artifact/run-smoke.sh`: short CAV smoke test.
  * `caesar/artifact/run-model-checking.sh`: model-checking examples using Caesar's JANI backend and Storm.
  * `caesar/artifact/run-all-benchmarks.sh`: full benchmark test runner.
  * `caesar/docker/CAV26.dockerfile`: Docker image recipe.
* Documentation:
  * `caesar/website/docs/`: offline Markdown source for the Caesar documentation.
  * `caesar/website/build/`: offline compiled HTML documentation in the Docker image.

The artifact does not require external connectivity when the submitted Docker image is loaded. Rebuilding the Docker image from source does require network access to fetch Debian, Rust, and npm dependencies.

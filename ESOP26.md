# ESOP '26 Artifact Evaluation Guide

Welcome to the artifact for our ESOP '26 submission "Error Localization, Certificates, and Hints for Probabilistic Program Verification via Slicing".

Contained within the artifact:
 * Our tool *Caesar* which includes the slicing implementation *Brutus*.
    * A script to reproduce our benchmarks (Section 5 and Appendix B).
 * Our full source code is contained within the artifact as well.

## Contents

1. Getting Started
2. Step by Step: How Our Artifact Supports the Paper's Claims
    1. Running Our Benchmarks
    2. The Caesar/Brutus Tool
    3. Syntax of HeyVL
3. Command-Line Flags & Implementation Details
    1. Paper Sections and Command-line Flags
    2. Source Code Structure
4. Building This Docker Image

## 1. Getting Started

**Requirements.**
* We use [Docker](https://www.docker.com/), and provide an image for both x86 and ARM architectures.
* 16 GB of RAM, enough disk space for the artifact.
* Our benchmark set should terminate in under 10 minutes.

**Downloading the artifact.**
If you downloaded the artifact from Zenodo, run `docker image load -i caesar.tar.gz`.

Alternatively, [via Github packages](https://github.com/moves-rwth/caesar/pkgs/container/caesar):
```bash
docker pull ghcr.io/moves-rwth/caesar:esop26-aec
```

**Entering the artifact environment.**
Simply run the `caesar` image with Docker.
This will open a `bash` shell in the `/root/caesar` directory with the `caesar` command available.

```bash
docker run -it ghcr.io/moves-rwth/caesar:esop26-aec
```
The image is based on Debian Bullseye (slim), so the `apt` package manager is available.
The editors `vim` and `nano` are installed already.

**Running the benchmarks.**
The benchmarks are in the `/root/caesar/slicing-benchmarks` directory.
To reproduce our benchmarks (Table 2), execute
```bash
cd /root/caesar/slicing-benchmarks
fish all-benchmarks.fish
```
The script will run all benchmarks in sequence for all figures.
See Section 2.1 for more details.

**Documentation.**

* We provide much more detailed usage and syntax instructions in our documentation. It is [available online](https://www.caesarverifier.org), and the source code can be found in `/root/caesar/website/docs` (Markdown files).
    * The website uses Google Analytics, so use an Adblocker to prevent tracking.
    * **For slicing specifically, we have [online documentation](https://www.caesarverifier.org/docs/caesar/slicing) (offline: `website/docs/caesar/slicing.md`).**
* Caesar has Rustdoc documentation, but we do not include the generated files or the Rust compiler in this artifact.


## 2. Step by Step: How Our Artifact Supports the Paper's Claims

Section 5 and Appendix B present our benchmark results.

In this document,
 * **Section 2.1.** explains how to run our benchmarks (Figure 14, Table 5, Table 6, Figure 23, and Figure 24).
 * **Section 2.2.** explains how to use our tool Caesar/Brutus.

## 2.1. Running Our Benchmarks

To reproduce our benchmarks (Figure 14, Table 5, Table 6, Figure 23, and Figure 24), execute
```bash
cd /root/caesar/slicing-benchmarks
fish all-benchmarks.fish
```

The script will run the list of benchmarks specified under `/root/caesar/slicing-benchmarks/` in the following files:
 1. `error-preserving.txt` (Figure 14, Table 5),
 2. `verification-preserving.txt` (Table 6) and
 3. `verification-witnessing.txt` (Table 6), and
 4. `verifying.txt` (Figure 23 and Figure 24).
After completion, the results will be written into respective CSV files:
 1. `result-error-preserving.csv`,
 2. `result-verification-preserving.csv`,
 3. `result-verification-witnessing.csv`,
 4. `result-verifying.csv`.

We've attached our own results for reference in the `/root/caesar/slicing-benchmarks/paper-results/` directory.

Note that the `verifying.txt` benchmarks are a subset of the combined benchmark sets `verification-preserving.txt` and `verification-witnessing.txt`, where the `barros_programX` and `gehr18_2` and `gehr18_3` benchmarks are excluded (as they are very similar and would skew the diagram).

## 2.2. The Caesar/Brutus Tool

Our tool is available as the `caesar` command.
The source code is in the entry directory (`/root/caesar`).
In particular, the `src` and `z3rro` directories are relevant.
Both are documented using Rust doc comments.

**Running Caesar directly.**
It can be executed with `caesar verify [filename]` where the file contains a HeyVL program.

Regarding slicing:
 * Slicing for erroring programs is enabled by default (for error-preserving slicing).
 * Slicing for verifying programs is disabled by default. It can be enabled with the `--slice-verify` command-line option (for verification-preserving and verification-witnessing slicing).
    * By default, Caesar uses strategy `core`. This can be changed with the option `--slice-verify-via METHOD` where `METHOD` can be one of `core`, `mus`, `sus`, or `exists-forall`.
    * Slicing probabilistic sampling statements must be enabled via the command-line flag `--slice-sampling`.
    * Slicing reward statements must be enabled via the command-line flag `--slice-ticks`.

For example, try
```
caesar verify --slice-verify --slice-verify-via mus /root/caesar/slicing-benchmarks/navarro20/example4_5.heyvl
```
where the output should be similar to
```
navarro20/example4_5.heyvl::example45: Verified.
    program slice:
        🤷 statement in line 23 is not necessary    (/root/caesar/slicing-benchmarks/navarro20/example4_5.heyvl:23:37)
```

**HeyVL Syntax.**
Caesar accepts a modified version of our syntax from the paper.
We refer to our documentation section on the language: [It is online](https://www.caesarverifier.org/docs/heyvl/) or in the source code directory `website/docs/heyvl/`.

The `--timeout [SECONDS]` and `--mem [MEGABYTES]` command-line options are useful to set runtime and memory limits.

**VSCode Extension.**
The Caesar VSCode extension provides syntax highlighting and diagnostics for HeyVL files.
See our [online documentation for installation instructions](https://www.caesarverifier.org/docs/getting-started/installation/#option-a-download-caesar-verifier-for-vscode-recommended).

# 3. Command-Line Flags & Implementation Details

Read this section if you want to inspect implementation details manually.
Run `caesar verify --help` to get an overview of all Caesar's command-line flags.

## 3.1. Paper Sections and Command-line Flags

Below, we list paper sections and how to inspect their corresponding implementation in Caesar.

- Section 2 on HeyVL
	- Caesar's reasoning is based on expectations. One may inspect the intermediate generated expectations via
		- the command-line flag `--print-theorem`.
		- the VSCode command `Caesar: Explain HeyVL Core Verification Condition Generation`.
- Section 4.2 on Specification Statements
	- Caesar gives diagnostics for (co)procedure calls corresponding to the section's explanations.
- Section 4.3 on Park Induction
	- Caesar gives diagnostics for loops with the `@invariant(...)` annotation corresponding to the section's explanations.
- Section 5
	- One may inspect the generated SMT-LIB query via the command-line flag `--print-smt`.
	- Caesar's VSCode extension is available in the VSCode and Open VSX Registry.
		- See [online documentation](https://www.caesarverifier.org/docs/getting-started/installation#option-a-download-caesar-verifier-for-vscode-recommended).
		- Adjust command-line flags in VSCode settings `Caesar > Server: args`. Afterwards, restart via command `Caesar: Restart Server`.
- Section 5, Program Transformation for Slicing
	- Caesar implements the program transformation presented. The command-line flag `--print-core` shows the HeyVL code after all desugarings have been applied. In addition to the slicing program transformations, this includes the one for (co)procedure calls and e.g. the `@invariant(...)` annotation. The generated variables are called `slice_toggle_INDEX` where `INDEX` is a counter.
	- Slicing probabilistic sampling statements must be enabled via the command-line flag `--slice-sampling`.
	- Slicing reward statements must be enabled via the command-line flag `--slice-ticks`.
- Section 5, Searching for Erroring Slices
	- Caesar searches for the smallest erroring slices by default (strategy `opt`). The command-line flag `--slice-error-first` returns the first slice found (strategy `first`).
- Section 5, Searching for Verifying Slices
	- One needs to enable slicing for verifying slices via the command-line flag `--slice-verify`.
	- By default, Caesar uses unsatisfiable cores (strategy `core`). This can be changed with the option `--slice-verify-via` METHOD where METHOD can be one of `core`, `mus`, `sus`, or `exists-forall`.
- Section 5/Appendix B, Benchmarks
	- Locations of benchmark files are listed in the files `/root/caesar/slicing-benchmarks/error-preserving.txt` (Table 5), `/root/caesar/slicing-benchmarks/verification-preserving.txt` and `/root/caesar/slicing-benchmarks/verification-witnessing.txt` (Table 6).
	- The paper's Appendix B contains more detailed explanations for selected examples.

## 3.2. Source Code Structure

The source code is in the entry directory (`/root/caesar`).
In particular, the `src` and `z3rro` directories contain the main source code.

* The `src` directory contains Caesar's main source code.
    * The `src/slicing` directory contains the slicing implementation (Brutus).
        * `src/slicing/selection.rs` contains code to select and annotate with diagnostics.
        * `src/slicing/transform.rs` contains the program transformation for slicing.
        * `src/slicing/solver.rs` and `src/slicing/util.rs` contain the search strategies for finding slices.
        * `src/slicing/transform_test.rs` contains some tests that prove correctness of the program transformation for slicing.
* The `z3rro` directory contains our SMT-LIB generation and interaction with the Z3 SMT solver.

## 4. Building This Docker Image

To build the multi-platform Docker image, run:
```bash
docker buildx build \
  --platform linux/amd64,linux/arm64 \
  -t caesar \
  -f docker/ESOP26.dockerfile \
  --output type=oci,dest=caesar.oci.tar \
  .

gzip caesar.oci.tar
```

The resulting `caesar.oci.tar.gz` file should contain the multi-platform Docker image.

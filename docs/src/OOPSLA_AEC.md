# OOPSLA '23 Artifact Evaluation Guide

Welcome to the artifact for our OOPSLA '23 submission _"A Deductive Verification Infrastructure for Probabilistic Programs"_.

Contained within the artifact:
 * Our tool *Caesar*, which parses HeyVL programs and tries to verify them. Caesar constitutes our main implementation contribution and is the focus of this artifact.
    * A script to reproduce our benchmarks (Table 2).
 * We also include our prototypical tool *pgcl2heyvl*, which takes pGCL programs with annotations and produces a HeyVL file that encodes the required proof obligations.
 * Our full source code is contained within the artifact as well.

## Contents

1. Getting Started
2. Piece by Piece: How Our Artifact Supports the Paper's Claims
    1. Running Our Benchmarks
    2. The Caesar Tool and Its Source Code
    3. pgcl2heyvl: Generating HeyVL Files From pGCL
3. A Guide to Custom Examples
4. Appendix: Accepted pGCL Syntax by the pglc2heyvl Tool

## 1. Getting Started

**Requirements.**
* We use [Docker](https://www.docker.com/), and provide images for both x86 and ARM architectures.
* 16 GB of RAM, enough disk space for the artifact.
* Our benchmark set should terminate in under 10 minutes.
* Note: We provide an x86 Docker image. On ARM machines, Docker will run it in a virtual machine and will print a warning. In these setups, we have observed a slowdown of about 10x.

**Downloading the artifact.**
Either download from Zenodo (**TODO**) and then run `docker image load -i caesar.tar.gz`.

Alternatively, [via Github packages](https://github.com/Philipp15b/caesar/pkgs/container/caesar):
```
docker pull ghcr.io/philipp15b/caesar:oopsla23-aec --platform linux/amd64
```

**Entering the artifact environment.**
Simply run the `caesar` image with Docker.
This will open a `bash` shell in the `/root/caesar` directory with the `caesar` and `pgcl2heyvl` commands available.

```bash
docker run -it ghcr.io/philipp15b/caesar:oopsla23-aec
```
The image is based on on Debian Bullseye (slim), so the `apt` package manager is available.
The editors `vim` and `nano` are installed already.

**Running the benchmarks.**
To reproduce our benchmarks (Table 2), execute
```bash
fish run-benchmarks.fish
```
The script will run the list of benchmarks specified in `benchmarks.txt` in sequence (usually in < 10min).
After completion, the results will be printed as an ASCII table to the terminal as well to the CSV file `benchmark-results.csv`.

**Documentation.**

* We provide more detailed usage and syntax instructions in our documentation. It is [available online](https://www.caesarverifier.org) and the source code can be found in `docs/src` (Markdown files).
* Caesar has Rustdoc documentation, but we do not include the generated files or the Rust compiler in this artifact.

## 2. Piece by Piece: How Our Artifact Supports the Paper's Claims

*Section 5.2* of our paper states our key claims with respect to this artifact.

In this document,
 * **Section 2.1.** explains how to run our benchmarks (Table 2).
 * **Section 2.3.** explains how to automatically generate HeyVL files using our prototypical frontend pgcl2heyvl.

### 2.1. Running Our Benchmarks

To reproduce our benchmarks (Table 2), execute
```bash
fish run-benchmarks.fish
```
The script will run the list of benchmarks specified in `benchmarks.txt` in sequence.
After completion (usually in < 10min), the results will be printed as an ASCII table to the terminal as well to the CSV file `benchmark-results.csv`.

Note: To allow reproducing results on slower machines and virtualized environments, we increased the timeout for each benchmark from 10s to 60s.

### 2.2. The Caesar Tool and Its Source Code

Our tool is available as the `caesar` command.
The source code is in the entry directory (`/root/caesar`).
In particular, the `src` and `z3rro` directories are relevant.
Both are documented using Rust doc comments.

**Running Caesar directly.**
It can be executed with `caesar [filename]` where the file contains a HeyVL program.
Our benchmarks can be found in the following directories:
* `pgcl/examples-heyvl`: This directory contains the 85% of our benchmarks which were automatically generated using pgcl2heyvl.
* `tests`: This directory contains remaining 15% of the benchmarks which are hand-written HeyVL files (cf. Section 5.2 in our paper).

The `--timeout [SECONDS]` and `--mem [MEGABYTES]` command-line options are useful to set runtime and memory limits.

**HeyVL Syntax.**
Caesar accepts a modified version of our syntax from the paper.
We refer to our documentation section on the language: [It is online](https://philipp15b.github.io/caesar/heyvl/index.html), and contained in the artifact in `docs/src/heyvl`.
Example HeyVL files in the `pgcl/examples` and `tests/` directories.

**VSCode extension for syntax highlighting.**
We have a VSCode extension for HeyVL syntax highlighting.
See `vscode-ext/README.md` for installation instructions.
You might need to do this outside of your Docker container, so run `docker cp CONTAINER:/root/caesar/vscode-ext $PWD` to copy the directory out of the container and then run the installation.

We recommend using this extension with a [VSCode Remote connection to the Docker container](https://code.visualstudio.com/remote/advancedcontainers/develop-remote-host) when editing HeyVL files for convenience.

### 2.3. pgcl2heyvl: Generating HeyVL Files From pGCL

This pGCL frontend is available as the `pgcl2heyvl` command.
Its source code is provided in the `pgcl/pgcl2heyvl` directory as a [Poetry](https://python-poetry.org/) package.

**Automatically generated benchmarks.**
In our paper, we claim that 85% of our benchmarks are automatically generated from pGCL code.
These pGCL examples are located in the `pgcl/examples` directory.

The corresponding generated HeyVL files are located in `pgcl/examples-heyvl`.
We already generated all these HeyVL files with pgcl2heyvl.

In order to reproduce the process of automatically generating the HeyVL files, run
```bash
rm pgcl/examples-heyvl/*.heyvl # delete existing files
fish pgcl/examples-heyvl/generate.fish # generate files
```
See Section 2.2. for how to run the individual HeyVL files with Caesar.

**Details.**
pgcl2heyvl parses pGCL programs in the syntax accepted by the [probably](https://philipp15b.github.io/probably/) Python package.
See the last section of this file for the grammar of pGCL programs.

At the top of every file must be a comment of the style
```
// ARGS: --encoding ... --pre ... --post ...
```
according to the CLI documentation of the pgcl2heyvl tool (run `pgcl2heyvl --help`).


# 3. A Guide To Custom Examples

We will look at our `geo1` example to see how you can create your own examples for pgcl2heyvl and Caesar.

## 3.1. From pGCL to HeyVL

There is a pGCL file for `geo1` in `pgcl/examples/geo1.pgcl`:
```
// ARGS: --encoding "encode-k-induction" --calculus "wp" --post c --pre "c+1" --k 2

nat c;
nat f;

while(f=1){
   {f := 0}[0.5]{c := c+1}
}
```

pgcl2heyvl can be used to create a corresponding HeyVL file that uses the annotations in the first line to prove that `wp[geo1](c) <= c+1` holds using `k`-induction with `k=2`.
```
pgcl2heyvl pgcl/examples/geo1.pgcl > mygeo.heyvl
```
This will create a `mygeo.heyvl` file.

**Things to Try:**
 * Set the `pre` to `c+2`. This is still a valid upper bound (and the HeyVL file should verify.)
 * Set the `pre` to `c`. This is *not* a valid upper bound (and Caesar should give a counter-example later).

**Note:** 
pgcl2heyvl has a slighly different syntax for programs than Caesar accepts.
It also does not accept domain declarations (including user-defined functions and axioms).
We are working on a more convenient implementation.

## 3.2. Verifying HeyVL Files With Caesar

Simply run `caesar` with your new file:
```
caesar mygeo.heyvl
```
and it prints that the main generated `coproc` either verifies or not (depending on your modifications).

You can of course create HeyVL files directly.
To encode loops, use the encodings detailed in the appendix of our paper.

# 4. Appendix: Accepted Syntax by the pgcl2heyvl Tool

An excerpt from the [Lark](https://github.com/lark-parser/lark) grammar for pGCL programs used in the probably library:
```
declaration: "bool" var                  -> bool
            | "nat" var bounds?           -> nat
            | "const" var ":=" expression -> const

bounds: "[" expression "," expression "]"

instruction: "skip"                                      -> skip
           | "while" "(" expression ")" block            -> while
           | "if" "(" expression ")" block "else"? block -> if
           | var ":=" rvalue                             -> assign
           | block "[" expression "]" block              -> choice
           | "tick" "(" expression ")"                   -> tick

rvalue: "unif" "(" expression "," expression ")" -> uniform
      | expression

literal: "true"  -> true
       | "false" -> false
       | INT     -> nat
       | FLOAT   -> float
       | "∞"     -> infinity
       | "\infty" -> infinity
```

Expressions in programs and expectations can be built from the following operators, grouped by precedence:

1. `||`, `&`
2. `<=`, `<`, `=`
3. `+`, `-`
4. `*`, `:`
5. `/`
6. `not `, `( ... )`, `[ ... ]`, `literal`, `var`

Whitespace is generally ignored.

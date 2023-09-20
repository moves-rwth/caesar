# Quick Start

## 0. Installation (Either Docker or Locally Compiled)

You can build Caesar using Docker or compile it locally.

### 0.1. Installation via Docker

First, install [Docker](https://www.docker.com/). 

#### 0.1.1. Building the Docker image
1. Enter the project root directory
2. `docker build -t caesar -f docker/Dockerfile .`
3. You now have a Docker image with the name `caesar` available.

#### 0.1.2. Loading the Docker image
If the Docker image was already provided, you can load it into your Docker installation using `docker load -i caesar.tar.gz`.

#### 0.1.3. Running the Docker image
* The command `docker run -it caesar /bin/bash` will open a shell inside the container where you can use Caesar.
* The command `docker run -it caesar -v $PWD/results:/root/caesar/results/ /bin/bash` will open a shell and mount the `results` directory into the container.

### 0.2. Installation By Local Compilation

#### 0.2.1. Installing Rust

Caesar is written in the [Rust programming language](https://www.rust-lang.org/).
You'll need [cargo](https://doc.rust-lang.org/cargo/), Rust's default package manager, to build the project.

One very easy way to install Rust is by using [rustup](https://rustup.rs/).

#### 0.2.2. Installing Z3

We use Rust bindings to the [Z3 theorem prover](https://github.com/Z3Prover/z3).
By default, Caesar will compile Z3 itself (using the `static-link-z3` option of [z3.rs](https://github.com/prove-rs/z3.rs)).
This will require [cmake](https://cmake.org/) and `libclang`.
On Debian/Ubuntu, you can run `apt-get install cmake llvm-dev libclang-dev clang` to install the required dependencies.

You can compile Caesar without the `static-link-z3` feature (enabled by default) to link against the system-installed Z3.

#### 0.2.3. Python (for the pGCL frontend)

This is only required if you want to use the pGCL frontend.
It is not necessary if you just want to write HeyVL code.
Refer to the [pGCL frontend documentation](./frontends/pgcl.md) for instructions.

#### 0.2.4. Compiling Caesar Itself

Clone the GitHub repository:
```
git clone https://github.com/moves-rwth/caesar.git
cd caesar
```

To build caesar, run
```
cargo build --release
```
The result will be at `target/release/caesar`.
Omit the `--release` for faster compilation in debug mode.
Then, the executable can be found at `target/debug/caesar`.

The command-line API and more compilation options are documented in the [Caesar chapter](./caesar.md).

## 1. Run Some Benchmarks

Enter the following two commands.
They should terminate in under a minute.

```
cd pgcl/examples-heyvl
caesar unif_gen1.heyvl rabin1.heyvl rabin2.heyvl brp1.heyvl geo1.heyvl
```

You can also [run all available benchmarks](./caesar.md#benchmarks).

## 2. Write Some HeyVL Code

Be inspired by the existing examples at [`pgcl/examples-heyvl`](https://github.com/moves-rwth/caesar/tree/master/pgcl/examples-heyvl).

Read the [HeyVL language reference](./heyvl/README.md).

## 3. Write Some pGCL Code And Compile It To HeyVL

Refer to the [documentation of the pGCL frontend](./frontends/pgcl.md).

## 4. Ask Questions and Report Bugs!

Please [open issues](https://github.com/moves-rwth/caesar/issues) or [write emails](mailto:phisch@cs.rwth-aachen.de) if you encountered any issues.

If you struggled with _anything_, chances are that others will struggle as well.
So please complain and we'll improve Caesar.
This is all complicated stuff and we want to make it as nice to use as possible.
Do not hesitate to complain about minor things!
Don't like the colors?
Typos in the documentation?
You don't like the syntax?
Think there may be a bug?
Ugly code?
This is research software and we're here to find out how to make it perfect.

If you're curious how the code works (or doesn't) and how to modify Caesar, refer to the [development guide](./devguide.md).

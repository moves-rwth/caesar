---
sidebar_position: 6
---

# The Caesar Tool

The `caesar` binary contains all of Caesar's functionality: verifying HeyVL files, running the [LSP server](./vscode-and-lsp.md), and [translation support for model checking](../model-checking.md).

**Print help:**
The command-line help information is much more detailed than this document.
Run `caesar --help` for available subcommands and `caesar --help verify` for details on the [`verify` subcommand](#subcommand-caesar-verify).

**Compile** the `caesar` binary with `cargo build --release`.
The executable can be found at `target/release/caesar`.
In the following, we just write `caesar` for the executable.
Omit `--release` for the a binary with less optimizations; the result will be in `target/debug/caesar`.
More information in our [installation guide](../getting-started/installation.mdx).

**Print tracing messages:**
Caesar uses the [`tracing` library](https://github.com/tokio-rs/tracing) to print (debugging) information during its operation.
Set the `RUST_LOG` environment variable to specify a filter, e.g. `export RUST_LOG="caesar=debug"` or `export RUST_LOG="caesar::smt=trace"`.

## Subcommand `caesar verify`

The `caesar verify` subcommand takes a HeyVL program as input and tries to determine whether it _verifies_.

**Verify HeyVL files:**
`caesar verify file1.heyvl file2.heyvl ...`
Adding `--raw` indicates that input files consist only of a sequence [HeyVL statements](../heyvl/statements.md) and that no declarations such as procedures are expected.

**Timeouts and memory limits:**
Set a timeout of 60 seconds using `--timeout 60`.
Set a memory limit of 16000 megabytes with `--mem 16000`.

**Slicing:**
[Caesar's slicing](./slicing.md) is controlled by the following flags:
* With the `--no-slice-error` flag, Caesar will not do slicing to obtain better error messages (error slicing enabled by default).
* With the `--slice-verify` flag, Caesar will do slicing for verification (this is not enabled by default).

**Print intermediate data:**
* With the `--print-parsed` flag, Caesar pretty-prints the HeyVL code after parsing.
* With the `--print-core` flag, Caesar prints the HeyVL code after parsing, type-checking, and desugaring.
* With the `--print-theorem` flag, Caesar prints the theorem that is encoded into SMT.
* With the `--print-smt` flag, Caesar prints the SMT-LIB query for each verification task. You can also use `--smt-dir DIR` with a directory `DIR` to have Caesar write the SMT-LIB queries to files in `DIR`.
  * If [`raco read`](https://docs.racket-lang.org/raco/read.html) is installed, Caesar will auto-format the SMT-LIB code with it. This is very useful as Z3's default formatting is really confusing sometimes.

## More Topics

```mdx-code-block
import DocCardList from '@theme/DocCardList';

<DocCardList />
```

---
sidebar_position: 1
---

# VSCode Extension & LSP Support

## _Caesar Verifier_ VSCode Extension

We maintain an extension for Visual Studio Code: [_Caesar Verifier_ on the VSCode Extension Marketplace](https://marketplace.visualstudio.com/items?itemName=rwth-moves.caesar).
You can also find it in the _Extensions_ menu in VSCode by the name _Caesar Verifier_.

### Features

 * Syntax highlighting and language configuration for HeyVL.
 * Snippets for HeyVL.
 * Verify HeyVL files on file save or on command.
 * Verification errors and successes are shown in the gutter via icons.
 * Diagnostics such as errors or warnings are shown in the code and in the "Problems" menu in VSCode.
 * Inline explanations of computed verification conditions.
 * Automatic installation and updating of Caesar.

### Installation

You have three options:
 * The easiest way to install our VSCode extension is to search for _Caesar Verifier_ in the _Extensions_ menu in VSCode.
 * Alternatively, you can [download the extension from the VSCode Extension Marketplace](https://marketplace.visualstudio.com/items?itemName=rwth-moves.caesar). The extension is also [published on the Open VSX Registry](https://open-vsx.org/extension/rwth-moves/caesar).
 * To run a local development version of the extension, you can install it via the _Developers: Install Extension from Location_ command in VSCode. Refer to [Caesar's Development Guide](../devguide.md) for details on how to compile it.

After installing the extension in VSCode, a getting started page will open from where you can install the Caesar binaries (open manually with `Caesar: Open Getting Started` command).

## LSP Support (Other Clients)

**This section is only relevant for those users who want to develop their own LSP client for Caesar.**

Caesar supports the [language server protocol](https://microsoft.github.io/language-server-protocol/) (LSP) for features such as error diagnostics and [slicing results](./slicing.md).
Caesar's VSCode extension is is based on LSP.

:::note

Our LSP support is aimed at our VSCode extension only.
Because we make use of custom commands, the extension's main functionality is only available from our extension.

:::

When started with the `--language-server` option, Caesar will start an LSP server listening on standard input and standard output.
Error output is written to standard error.
All other options that are passed to the Caesar binary will be used as options for all future verification requests.

The server will respond to `custom/verify` requests with diagnostics and `custom/verifyUpdate` notifications.
Refer to the extension's source code in the [`vscode-ext/` directory](https://github.com/moves-rwth/caesar/tree/main/vscode-ext) for details.

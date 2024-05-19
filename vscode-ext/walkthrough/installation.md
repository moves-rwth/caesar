# <img src="../images/icon.png" width=20> Installing Caesar

All of [Caesar's releases are on Github](https://github.com/moves-rwth/caesar/releases).

## Automatic Installation (Recommended)

The easiest way to install Caesar is to [Automatically Install Caesar](command:caesar.checkUpdate).

We provide binaries for MacOS (ARM and x86-64), Windows (x86-64), and Debian/Linux (x86-64).

You will also receive notifications for updates (see the `Auto Check` setting).

## Manual Installation

If the above does not work for you, we have alternative installation methods in [Caesar's installation guide](https://www.caesarverifier.org/docs/getting-started/installation).
After those steps:

* **Providing Your Own Binary.** You can compile Caesar for yourself and set the setting `Installation Options` to `binary` and provide a `Binary Path` to the compiled Caesar executable.
* **From Source.** With all required dependencies installed, you can set the setting `Installation Options` to `source-code` and provide a `Source Path` with the Caesar repository. Caesar will be compiled using `cargo`.

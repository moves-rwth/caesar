# Caesar's Integration Tests

Here are Caesar's integration tests.
They are automatically run by `cargo test`.
For options on how to run these tests, execute `cargo test --test integration -- --help`.
E.g. you can do `cargo test --test integration -- --verbose`.

The `integration.rs` runner will collect all files ending in `.heyvl` in this directory and execute them as [lit](https://github.com/dylanmckay/lit) tests.
The runner will search for directives like `RUN: ` and `CHECK: ` in the file.
Consider this example file:

```
// RUN: @caesar --raw @file
// CHECK: refute

down assert 3;
```

The runner will execute the command specified after `RUN: `, in this case `@caesar --raw @file`.
`@caesar` is replaced automatically by the path to the `caesar` executable and `@file` is replaced by the path to the current file.
The text specified after `CHECK: ` must occur in caesar's output.

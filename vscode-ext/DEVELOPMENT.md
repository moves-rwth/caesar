# VS Code extension development

Use Node.js 24 and Yarn 1.22, matching CI.
Install dependencies from the repository root:

```sh
cd vscode-ext
yarn install --frozen-lockfile
```

## Debugging

Open the repository root in VS Code, select **Run VSCode Extension (Bundled)**, and press F5.
The launch task bundles the extension and watches for changes.
Open a `.heyvl` file in the Extension Development Host to activate it.
Set breakpoints in `vscode-ext/src` and restart the debug session to load rebuilt code after edits.

## Checks and packaging

Run these commands in `vscode-ext`:

| Command | Purpose |
| --- | --- |
| `yarn verify` | Type-check and lint. |
| `yarn test` | Verify, bundle, and run tests in a downloaded VS Code instance. |
| `yarn package` | Verify, build the production bundle, and create a `.vsix`. |

The extension supports VS Code 1.87 and its Node.js 18 runtime.

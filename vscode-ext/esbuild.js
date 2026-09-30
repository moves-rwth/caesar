const esbuild = require("esbuild");
const fs = require("node:fs");
const path = require("node:path");

const production = process.argv.includes("--production");
const watch = process.argv.includes("--watch");

const buildOptions = {
    entryPoints: ["src/extension.ts"],
    bundle: true,
    platform: "node",
    target: "node18",
    outfile: "dist/extension.js",
    external: ["vscode"],
    minify: production,
    sourcemap: true,
    logLevel: "info"
};

async function run() {
    fs.mkdirSync(path.join(__dirname, "dist"), { recursive: true });
    fs.copyFileSync(require.resolve("vscode-oniguruma/release/onig.wasm"), path.join(__dirname, "dist/onig.wasm"));
    if (watch) {
        const context = await esbuild.context(buildOptions);
        await context.watch();
        return;
    }

    await esbuild.build(buildOptions);
}

run().catch(() => process.exit(1));

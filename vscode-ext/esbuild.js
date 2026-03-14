const esbuild = require("esbuild");

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
    if (watch) {
        const context = await esbuild.context(buildOptions);
        await context.watch();
        return;
    }

    await esbuild.build(buildOptions);
}

run().catch(() => process.exit(1));

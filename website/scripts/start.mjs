// Keep production builds from overwriting the running dev server's generated modules.
// Set this before importing Docusaurus, which reads it during module initialization.
process.env.DOCUSAURUS_GENERATED_FILES_DIR_NAME ??= '.docusaurus-dev';

process.argv.splice(2, 0, 'start');
await import('@docusaurus/core/bin/docusaurus.mjs');

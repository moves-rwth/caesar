const fs = require('node:fs');
const path = require('node:path');
const {pathToFileURL} = require('node:url');

module.exports = function heyvlExamples(context) {
  const catalogPath = path.join(context.siteDir, 'src/heyvl-examples/catalog.mjs');
  return {
    name: 'heyvl-examples',
    async loadContent() {
      const catalogUrl = pathToFileURL(catalogPath).href;
      const catalog = await import(`${catalogUrl}?mtime=${fs.statSync(catalogPath).mtimeMs}`);
      const {validateCatalog} = await import(pathToFileURL(path.join(__dirname, 'validate.mjs')).href);
      validateCatalog(catalog, context.siteDir);
    },
    getPathsToWatch() {
      return [
        catalogPath,
        path.join(context.siteDir, 'docs/getting-started/zoo/*.mdx'),
        path.join(context.siteDir, '../tests/**/*.heyvl'),
      ];
    },
    configureWebpack(_config, isServer) {
      return {
        module: {
          rules: [{
            test: /\.heyvl$/i,
            oneOf: [
              {resourceQuery: /^\?raw$/, type: 'asset/source'},
              {
                resourceQuery: /^\?download$/,
                type: 'asset/resource',
                generator: {
                  filename: 'assets/examples/[contenthash:8]/[name][ext]',
                  emit: !isServer,
                },
              },
            ],
          }],
        },
      };
    },
  };
};

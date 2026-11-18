import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import * as catalog from '../src/heyvl-examples/catalog.mjs';
import {validateCatalog} from '../plugins/heyvl-examples/validate.mjs';

const siteDir = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const repoDir = path.resolve(siteDir, '..');
validateCatalog(catalog, siteDir);
const variants = catalog.examples.flatMap((entry) => entry.variants);
console.log(`Validated ${catalog.examples.length} examples and ${variants.length} source variants.`);

// An optional binary verifies the documented commands, including their expected outcomes.
const binary = process.argv[2] ? path.resolve(process.argv[2]) : undefined;
if (binary) {
  let failures = 0;
  for (const variant of variants) {
    const result = spawnSync(binary, ['verify', variant.sourcePath, ...variant.args], {
      cwd: repoDir,
      encoding: 'utf8',
      timeout: 60000,
    });
    const output = `${result.stdout ?? ''}\n${result.stderr ?? ''}`;
    const matches = variant.outcome === 'proof'
      ? result.status === 0 && /: Verified\b/.test(output)
      : result.status === 1 && output.includes('Counter-example to property found');
    if (result.error || !matches) {
      failures++;
      console.error(`Unexpected ${variant.outcome} result: ${variant.sourcePath}\n${result.error ?? output}`);
    }
  }
  if (failures) process.exitCode = 1;
  else console.log(`All ${variants.length} documented commands produced their expected result.`);
}

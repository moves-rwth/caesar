import fs from 'node:fs';
import path from 'node:path';

const slug = /^[a-z0-9]+(?:-[a-z0-9]+)*$/;

export function validateCatalog({examples, categories, groups, topics, techniques, papers}, siteDir) {
  const repoDir = path.resolve(siteDir, '..');
  const detailDir = path.join(siteDir, 'docs/getting-started/zoo');
  const errors = [];
  const entryIds = new Set();
  const detailSlugs = new Set();

  function checkTags(values, label) {
    const ids = new Set();
    for (const tag of values) {
      if (!slug.test(tag.id) || !tag.label || ids.has(tag.id)) {
        errors.push(`Invalid or duplicate ${label}: ${tag.id}`);
      }
      ids.add(tag.id);
    }
    return ids;
  }

  const topicIds = checkTags(topics, 'topic');
  const techniqueIds = checkTags(techniques, 'technique');
  const categoryIds = checkTags(categories, 'category');
  const groupIds = checkTags(groups, 'group');
  const paperIds = checkTags(papers, 'paper');
  for (const paper of papers) {
    if (!paper.title?.trim()) errors.push(`${paper.id}: paper requires a title`);
    if (!paper.url?.startsWith('https://')) errors.push(`${paper.id}: paper requires an HTTPS reference`);
  }

  for (const entry of examples) {
    if (!slug.test(entry.id) || entryIds.has(entry.id)) errors.push(`Invalid or duplicate example ID: ${entry.id}`);
    entryIds.add(entry.id);
    if (!categoryIds.has(entry.category)) errors.push(`${entry.id}: unknown or missing category`);
    if (!groupIds.has(entry.group)) errors.push(`${entry.id}: unknown or missing group`);
    if (entry.papers?.some((id) => !paperIds.has(id))) errors.push(`${entry.id}: unknown paper reference`);
    if (!entry.title || !entry.summary) errors.push(`${entry.id}: title and summary are required`);
    if (!entry.topics?.length || entry.topics.some((id) => !topicIds.has(id))) errors.push(`${entry.id}: unknown or missing topic`);
    if (!entry.variants?.length) errors.push(`${entry.id}: at least one variant is required`);

    if (entry.detailSlug) {
      if (!slug.test(entry.detailSlug) || detailSlugs.has(entry.detailSlug)) errors.push(`${entry.id}: invalid or duplicate explanation slug`);
      detailSlugs.add(entry.detailSlug);
      const detailPath = path.join(detailDir, `${entry.detailSlug}.mdx`);
      if (!fs.existsSync(detailPath)) {
        errors.push(`${entry.id}: missing explanation page ${entry.detailSlug}.mdx`);
      } else {
        const page = fs.readFileSync(detailPath, 'utf8');
        const frontmatter = page.match(/^---\r?\n([\s\S]*?)\r?\n---(?:\r?\n|$)/)?.[1];
        const title = frontmatter?.match(/^title:[ \t]*(.+?)[ \t]*$/m)?.[1];
        if (title !== entry.title) errors.push(`${entry.id}: explanation title must match catalog title ${JSON.stringify(entry.title)}`);
        if (!new RegExp(`exampleId=["']${entry.id}["']`).test(page)) errors.push(`${entry.id}: explanation page must reference its catalog entry`);
        for (const variant of entry.variants) {
          if (!page.includes(`${variant.sourcePath}?raw`) || !page.includes(`${variant.sourcePath}?download`)) {
            errors.push(`${entry.id}/${variant.id}: explanation must provide the cataloged source and download`);
          }
        }
      }
    }

    const variantIds = new Set();
    for (const variant of entry.variants ?? []) {
      const name = `${entry.id}/${variant.id}`;
      if (!slug.test(variant.id) || variantIds.has(variant.id)) errors.push(`${name}: invalid or duplicate variant ID`);
      variantIds.add(variant.id);
      if (!variant.label) errors.push(`${name}: missing label`);
      if (variant.topics !== undefined && (!Array.isArray(variant.topics) || variant.topics.some((id) => !topicIds.has(id)))) errors.push(`${name}: unknown or invalid topic`);
      if (!variant.techniques?.length || variant.techniques.some((id) => !techniqueIds.has(id))) errors.push(`${name}: unknown or missing technique`);
      if (!['proof', 'refutation'].includes(variant.outcome)) errors.push(`${name}: unknown outcome`);
      if (!Array.isArray(variant.args) || variant.args.some((arg) => typeof arg !== 'string')) errors.push(`${name}: command arguments must be strings`);
      const sourcePath = path.resolve(repoDir, variant.sourcePath);
      if (!variant.sourcePath.startsWith('tests/') || !sourcePath.startsWith(`${path.join(repoDir, 'tests')}${path.sep}`) || !sourcePath.endsWith('.heyvl') || !fs.existsSync(sourcePath)) {
        errors.push(`${name}: missing or invalid HeyVL test ${variant.sourcePath}`);
      } else {
        const source = fs.readFileSync(sourcePath, 'utf8');
        if (!/^\/\/\s*RUN:/m.test(source) || /^\/\/\s*IGNORE:/m.test(source)) errors.push(`${name}: source must be an active integration test`);
        if (variant.outcome === 'refutation' && !source.includes('Counter-example to property found')) errors.push(`${name}: test must assert a property refutation`);
      }
    }
  }

  if (fs.existsSync(detailDir)) {
    for (const filename of fs.readdirSync(detailDir)) {
      if (filename.endsWith('.mdx') && !detailSlugs.has(filename.slice(0, -4))) errors.push(`Explanation page missing from catalog: ${filename}`);
    }
  }
  if (errors.length) throw new Error(`Invalid example catalog:\n${errors.map((error) => `- ${error}`).join('\n')}`);
}

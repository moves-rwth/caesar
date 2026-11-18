export const EMPTY_FILTERS = Object.freeze({q: '', category: '', topics: Object.freeze([]), techniques: Object.freeze([])});

function knownFacet(value, items) {
  return !items || items.some((item) => item.id === value) ? value : '';
}

export function readFilters(search, facets = {}) {
  const params = new URLSearchParams(search);
  const selectedTopics = params.getAll('topic');
  const legacyOutcome = params.get('outcome');
  if (['proof', 'refutation'].includes(legacyOutcome)) selectedTopics.push(legacyOutcome);
  return {
    q: params.get('q') || '',
    category: knownFacet(params.get('category') || '', facets.categories),
    topics: [...new Set(selectedTopics)].filter((value) => value && knownFacet(value, facets.topics)),
    techniques: [...new Set(params.getAll('technique'))].filter((value) => value && knownFacet(value, facets.techniques)),
  };
}

export function writeFilters(filters, existingSearch = '') {
  const params = new URLSearchParams(existingSearch);
  for (const key of ['q', 'category', 'topic', 'technique', 'outcome']) params.delete(key);
  if (filters.q) params.set('q', filters.q);
  if (filters.category) params.set('category', filters.category);
  for (const topic of new Set(filters.topics)) params.append('topic', topic);
  for (const technique of new Set(filters.techniques)) params.append('technique', technique);
  const query = params.toString();
  return query ? `?${query}` : '';
}

function facetText(ids, items = []) {
  const facets = new Map(items.map((item) => [item.id, item]));
  return ids.flatMap((id) => [id, facets.get(id)?.label || '', facets.get(id)?.title || '']).join(' ');
}

export function filterExamples(entries, filters = EMPTY_FILTERS, facets = {}) {
  const queryTerms = (filters.q || '').trim().toLocaleLowerCase('en').split(/\s+/).filter(Boolean);
  return entries.flatMap((entry) => {
    if (filters.category && entry.category !== filters.category) return [];
    const entryText = `${entry.title} ${entry.summary} ${facetText(entry.topics, facets.topics)} ${facetText([entry.category], facets.categories)} ${facetText(entry.papers || [], facets.papers)}`;
    const variants = entry.variants.filter((variant) => {
      if (filters.techniques.length && !filters.techniques.some((technique) => variant.techniques.includes(technique))) return false;
      const variantTopics = [...entry.topics, ...(variant.topics || []), variant.outcome];
      if (filters.topics.length && !filters.topics.some((topic) => variantTopics.includes(topic))) return false;
      const searchableText = `${entryText} ${variant.label} ${variant.sourcePath} ${facetText(variant.techniques, facets.techniques)} ${facetText(variant.topics || [], facets.topics)} ${variant.outcome}`.toLocaleLowerCase('en');
      return queryTerms.every((term) => searchableText.includes(term));
    });
    return variants.length ? [{...entry, variants}] : [];
  });
}

export function githubSourceUrl(sourcePath) {
  return `https://github.com/moves-rwth/caesar/blob/main/${sourcePath.split('/').map(encodeURIComponent).join('/')}`;
}

function shellWord(value) {
  return /^[\w./:=+-]+$/.test(value) ? value : `'${value.replaceAll("'", "'\\''")}'`;
}

export function exampleCommand(variant) {
  const filename = variant.sourcePath.split('/').at(-1);
  return ['caesar', 'verify', filename, ...variant.args].map(shellWord).join(' ');
}

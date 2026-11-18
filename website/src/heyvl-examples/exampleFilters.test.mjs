import assert from 'node:assert/strict';
import test from 'node:test';
import {EMPTY_FILTERS, exampleCommand, filterExamples, githubSourceUrl, readFilters, writeFilters} from './exampleFilters.mjs';

const facets = {
  categories: [{id: 'boolean', label: 'Boolean'}, {id: 'probabilistic', label: 'Probabilistic'}, {id: 'quantitative', label: 'Quantitative'}],
  topics: [{id: 'probability', label: 'Probability'}, {id: 'algorithms', label: 'Algorithms'}, {id: 'proof', label: 'Proof'}, {id: 'refutation', label: 'Refutation'}],
  techniques: [{id: 'induction', label: 'k-induction'}, {id: 'unroll', label: 'Bounded unrolling'}, {id: 'recursion', label: 'Recursion'}],
  papers: [{id: 'example-paper', label: 'Example et al. (2018)', title: 'A Method for Reasoning about Coin Flips', url: 'https://example.com/paper'}],
};

const entries = [
  {
    id: 'geometric', title: 'Geometric loop', summary: 'Bounds on the expected number of flips showing tails.', category: 'probabilistic', topics: ['probability'], papers: ['example-paper'],
    variants: [
      {id: 'upper', label: 'Two-step upper bound', sourcePath: 'tests/geo-upper.heyvl', techniques: ['induction'], outcome: 'proof', args: []},
      {id: 'refuted', label: 'Twelve-step counterexample', sourcePath: 'tests/geo-refuted.heyvl', techniques: ['unroll'], outcome: 'refutation', args: ['--slice-error-first']},
    ],
  },
  {
    id: 'binary-tree', title: 'Binary search trees', summary: 'Search and insert values.', category: 'boolean', topics: ['algorithms'],
    variants: [{id: 'recursive', label: 'Recursive contracts', sourcePath: 'tests/tree.heyvl', techniques: ['recursion'], outcome: 'proof', args: ['--max-fuel', '8']}],
  },
];

const filter = (overrides) => filterExamples(entries, {...EMPTY_FILTERS, ...overrides}, facets);

function variantIds(result) {
  return result.flatMap((entry) => entry.variants.map((variant) => variant.id));
}

test('filtering preserves the editorial catalog order and does not mutate entries', () => {
  const result = filter({});
  assert.deepEqual(result.map((entry) => entry.id), ['geometric', 'binary-tree']);
  assert.deepEqual(entries.map((entry) => entry.id), ['geometric', 'binary-tree']);
  assert.equal(result[0].variants.length, 2);
  assert.notEqual(result[0], entries[0]);
});

test('filtered subsets retain the authored order regardless of title or explanation', () => {
  const catalog = [
    {...entries[0], id: 'zebra-source', title: 'Zebra source'},
    {...entries[0], id: 'zebra-guide', title: 'Zebra guide', detailSlug: 'zebra-guide'},
    {...entries[0], id: 'alpha-source', title: 'Alpha source'},
    {...entries[0], id: 'alpha-guide', title: 'Alpha guide', detailSlug: 'alpha-guide'},
  ];
  const result = filterExamples(catalog, EMPTY_FILTERS, facets);
  assert.deepEqual(result.map((entry) => entry.id), ['zebra-source', 'zebra-guide', 'alpha-source', 'alpha-guide']);
  const filtered = filterExamples(catalog, {...EMPTY_FILTERS, q: 'zebra'}, facets);
  assert.deepEqual(filtered.map((entry) => entry.id), ['zebra-source', 'zebra-guide']);
});

test('selected topics form a union, including outcomes derived per variant', () => {
  assert.deepEqual(variantIds(filter({topics: ['probability', 'algorithms']})), ['upper', 'refuted', 'recursive']);
  assert.deepEqual(variantIds(filter({topics: ['refutation', 'algorithms']})), ['refuted', 'recursive']);
  assert.deepEqual(variantIds(filter({topics: ['proof', 'refutation']})), ['upper', 'refuted', 'recursive']);
  assert.deepEqual(entries[0].topics, ['probability']);
});

test('selected techniques form a union and combine with the selected topic group', () => {
  assert.deepEqual(variantIds(filter({techniques: ['induction', 'recursion']})), ['upper', 'recursive']);
  assert.deepEqual(variantIds(filter({techniques: ['induction', 'unroll'], topics: ['refutation']})), ['refuted']);
});

test('technique and outcome topic must match the same variant', () => {
  assert.deepEqual(filter({techniques: ['induction'], topics: ['refutation']}), []);
  assert.deepEqual(variantIds(filter({techniques: ['unroll'], topics: ['refutation']})), ['refuted']);
  assert.equal(entries[0].variants.length, 2);
});

test('variant properties and proof techniques must match the same variant', () => {
  const terminationFacets = {
    ...facets,
    topics: [...facets.topics, {id: 'ast', label: 'Almost-sure termination'}, {id: 'past', label: 'Positive almost-sure termination'}],
    techniques: [{id: 'ast-rule', label: '@ast rule'}, {id: 'past-rule', label: '@past rule'}],
  };
  const countdown = {
    id: 'countdown', title: 'Countdown', summary: 'A decreasing counter.', category: 'probabilistic', topics: ['probability'],
    variants: [
      {id: 'first', label: 'First argument', sourcePath: 'tests/countdown-a.heyvl', techniques: ['ast-rule'], topics: ['ast'], outcome: 'proof', args: []},
      {id: 'second', label: 'Second argument', sourcePath: 'tests/countdown-b.heyvl', techniques: ['past-rule'], topics: ['ast', 'past'], outcome: 'proof', args: []},
    ],
  };
  const find = (overrides) => filterExamples([countdown], {...EMPTY_FILTERS, ...overrides}, terminationFacets);

  assert.deepEqual(find({techniques: ['ast-rule'], topics: ['past']}), []);
  assert.deepEqual(variantIds(find({techniques: ['past-rule'], topics: ['past']})), ['second']);
  assert.deepEqual(variantIds(find({topics: ['ast']})), ['first', 'second']);
  assert.deepEqual(variantIds(find({q: 'positive almost-sure'})), ['second']);
  assert.deepEqual(variantIds(find({q: 'past'})), ['second']);
  assert.deepEqual(find({q: 'positive', techniques: ['ast-rule']}), []);
  assert.deepEqual(find({q: 'first positive'}), []);
  assert.deepEqual(countdown.topics, ['probability']);
  assert.equal(countdown.variants.length, 2);
});

test('query words cannot match two different variants', () => {
  assert.deepEqual(filter({q: 'two-step counterexample'}), []);
  assert.deepEqual(filter({q: 'two-step', topics: ['refutation']}), []);
  assert.deepEqual(filter({q: 'counterexample', techniques: ['induction']}), []);
});

test('category, topic, technique, and query groups combine by intersection', () => {
  const result = filter({q: 'COUNTER bounded', category: 'probabilistic', topics: ['probability', 'refutation'], techniques: ['unroll']});
  assert.deepEqual(variantIds(result), ['refuted']);
  assert.deepEqual(filter({q: 'counter', category: 'boolean'}), []);
  assert.deepEqual(filter({category: 'quantitative'}), []);
});

test('search includes titles, topics, category labels, techniques, and source filenames', () => {
  assert.equal(filter({q: 'binary values boolean'})[0].id, 'binary-tree');
  assert.equal(filter({q: 'probability k-induction'})[0].variants[0].id, 'upper');
  assert.equal(filter({q: 'geo-refuted.heyvl'})[0].variants[0].id, 'refuted');
});

test('paper authors, titles, and years are searchable entry metadata', () => {
  const result = filter({q: 'Example 2018', techniques: ['unroll']});
  assert.deepEqual(variantIds(result), ['refuted']);
  assert.deepEqual(variantIds(filter({q: 'reasoning coin flips', techniques: ['unroll']})), ['refuted']);
  assert.deepEqual(filter({q: '2019'}), []);
});

test('empty searches show all entries and unmatched searches return no results', () => {
  assert.equal(filter({q: '  \t  '}).length, 2);
  assert.deepEqual(filter({q: 'does-not-exist'}), []);
  assert.deepEqual(filterExamples([], EMPTY_FILTERS, facets), []);
});

test('URL round trips preserve repeated selections, Unicode, and unrelated parameters', () => {
  const filters = {q: 'counter ≤ 1 ', category: 'probabilistic', topics: ['probability', 'refutation'], techniques: ['unroll', 'induction']};
  const search = writeFilters(filters, '?utm_source=docs&q=old&q=duplicate');
  assert.deepEqual(readFilters(search, facets), filters);
  assert.equal(new URLSearchParams(search).get('utm_source'), 'docs');
  assert.equal(new URLSearchParams(search).getAll('q').length, 1);
  assert.deepEqual(new URLSearchParams(search).getAll('topic'), ['probability', 'refutation']);
  assert.deepEqual(new URLSearchParams(search).getAll('technique'), ['unroll', 'induction']);
  assert.equal(writeFilters(EMPTY_FILTERS, search), '?utm_source=docs');
  assert.equal(writeFilters(EMPTY_FILTERS), '');
});

test('legacy outcome and single-technique links migrate to checkbox filters', () => {
  const filters = readFilters('?topic=probability&outcome=refutation&technique=unroll', facets);
  assert.deepEqual(filters, {...EMPTY_FILTERS, topics: ['probability', 'refutation'], techniques: ['unroll']});
  const updated = new URLSearchParams(writeFilters(filters, '?outcome=refutation'));
  assert.equal(updated.has('outcome'), false);
  assert.deepEqual(updated.getAll('topic'), ['probability', 'refutation']);
  assert.deepEqual(readFilters('?topic=refutation&outcome=refutation&technique=unroll&technique=unroll', facets), {...EMPTY_FILTERS, topics: ['refutation'], techniques: ['unroll']});
});

test('restoring earlier URLs restores corresponding categories and checkbox choices', () => {
  const earlier = writeFilters({...EMPTY_FILTERS, category: 'boolean', topics: ['proof'], techniques: ['recursion']});
  const later = writeFilters({...EMPTY_FILTERS, topics: ['refutation'], techniques: ['unroll', 'induction']});
  assert.deepEqual(variantIds(filterExamples(entries, readFilters(later, facets), facets)), ['refuted']);
  assert.deepEqual(variantIds(filterExamples(entries, readFilters(earlier, facets), facets)), ['recursive']);
  assert.deepEqual(readFilters('', facets), EMPTY_FILTERS);
});

test('unknown and repeated filter values restore as valid deduplicated controls', () => {
  assert.deepEqual(readFilters('?q=tree&category=unknown&topic=missing&technique=old&outcome=timeout', facets), {...EMPTY_FILTERS, q: 'tree'});
  assert.deepEqual(readFilters('?topic=proof&topic=proof&technique=recursion&technique=recursion', facets), {...EMPTY_FILTERS, topics: ['proof'], techniques: ['recursion']});
});

test('download commands preserve required arguments and shell quoting', () => {
  assert.equal(exampleCommand(entries[1].variants[0]), 'caesar verify tree.heyvl --max-fuel 8');
  assert.equal(exampleCommand(entries[0].variants[1]), 'caesar verify geo-refuted.heyvl --slice-error-first');
  assert.equal(exampleCommand({sourcePath: 'tests/a b.heyvl', args: ['--filter', "a'b"]}), "caesar verify 'a b.heyvl' --filter 'a'\\''b'");
  assert.equal(githubSourceUrl('tests/a b.heyvl'), 'https://github.com/moves-rwth/caesar/blob/main/tests/a%20b.heyvl');
});

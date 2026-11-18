import React, {useEffect, useState} from 'react';
import clsx from 'clsx';
import Link from '@docusaurus/Link';
import useIsBrowser from '@docusaurus/useIsBrowser';
import InlineMathText from './InlineMathText';
import {examples, categories, groups, topics, techniques, papers} from './catalog.mjs';
import {EMPTY_FILTERS, filterExamples, githubSourceUrl, readFilters, writeFilters} from './exampleFilters.mjs';
import styles from './ExampleGallery.module.css';

const galleryPath = '/docs/getting-started/zoo';
const facets = {categories, topics, techniques, papers};
const categoryLabels = new Map(categories.map(({id, label}) => [id, label]));
const topicLabels = new Map(topics.map(({id, label}) => [id, label]));
const techniqueLabels = new Map(techniques.map(({id, label}) => [id, label]));

function ExampleEntry({example}: {example: (typeof examples)[number]}) {
  const walkthrough = Boolean(example.detailSlug);
  const linked = walkthrough || example.variants.length === 1;

  return (
    <article className={clsx('card', styles.entry, styles[example.category], walkthrough ? styles.walkthrough : styles.source, linked && styles.linked)} aria-labelledby={`example-${example.id}-title`}>
      <div className="card__body">
        <h3 id={`example-${example.id}-title`} className={styles.title}>
          {example.title}
        </h3>
        <p className={styles.summary}><InlineMathText>{example.summary}</InlineMathText></p>
        <div className={styles.metadata}>
          <span className={styles.category}>{categoryLabels.get(example.category)}</span>
          <ul className={styles.topics} aria-label={`${example.title} topics`}>
            {[...new Set([...example.topics, ...example.variants.flatMap((variant) => variant.topics || [])])].map((topic) => <li key={topic}>{topicLabels.get(topic) || topic}</li>)}
          </ul>
          <ul className={`${styles.topics} ${styles.techniques}`} aria-label={`${example.title} techniques`}>
            {[...new Set(example.variants.flatMap((variant) => variant.techniques))].map((technique) => <li key={technique}>{techniqueLabels.get(technique) || technique}</li>)}
          </ul>
        </div>
      </div>
      <div className="card__footer">
        {walkthrough ? (
          <Link className="button button--primary button--sm" to={`${galleryPath}/${example.detailSlug}`} aria-label={`Read about ${example.title}`}>Read example <span aria-hidden="true">→</span></Link>
        ) : (
          <ul className={styles.sourceLinks} aria-label={`${example.title} source files`}>
            {example.variants.map((variant) => (
              <li key={variant.id}>
                <a className={styles.sourceLink} href={githubSourceUrl(variant.sourcePath)} aria-label={`${variant.sourcePath.split('/').at(-1)}: ${variant.label}, on GitHub`}>
                  <span>{variant.sourcePath.split('/').at(-1)}</span>
                  <span aria-hidden="true">↗</span>
                </a>
              </li>
            ))}
          </ul>
        )}
      </div>
    </article>
  );
}

export default function ExampleGallery() {
  const isBrowser = useIsBrowser();
  const [filters, setFilters] = useState(() => readFilters(isBrowser ? window.location.search : '', facets));

  useEffect(() => {
    if (!isBrowser) return;
    const pathname = window.location.pathname;
    const restoreFilters = () => {
      if (window.location.pathname === pathname) {
        setFilters(readFilters(window.location.search, facets));
      }
    };
    restoreFilters();
    window.addEventListener('popstate', restoreFilters);
    return () => window.removeEventListener('popstate', restoreFilters);
  }, [isBrowser]);

  const matchingExamples = filterExamples(examples, filters, facets);
  const matchingGroups = groups.map((group) => ({
    ...group,
    entries: matchingExamples.filter((example) => example.group === group.id),
  })).filter((group) => group.entries.length);
  const hasFilters = Boolean(filters.q || filters.category || filters.topics.length || filters.techniques.length);

  function replaceFilters(nextFilters: typeof filters) {
    setFilters(nextFilters);
    const {pathname, search, hash} = window.location;
    const url = `${pathname}${writeFilters(nextFilters, search)}${hash}`;
    // Filter edits stay within this page and preserve the router's history state.
    window.history.replaceState(window.history.state, '', url);
  }

  function updateFilter(key: 'q' | 'category', value: string) {
    replaceFilters({...filters, [key]: value});
  }

  function toggleFilter(key: 'topics' | 'techniques', value: string) {
    const values = filters[key];
    const selected = values.includes(value) ? values.filter((item) => item !== value) : [...values, value];
    replaceFilters({...filters, [key]: selected});
  }

  function resetFilters() {
    replaceFilters(EMPTY_FILTERS);
  }

  return (
    <div className={`${styles.gallery} docs-wide`}>
      {matchingGroups.length > 0 && (
        <nav className={styles.groupNavigation} aria-label="Example groups">
          <span className={styles.groupNavigationLabel}>Browse by group</span>
          <ul className={styles.groupLinks}>
            {matchingGroups.map((group) => (
              <li key={group.id}><a href={`#example-group-${group.id}`}>{group.label}</a></li>
            ))}
          </ul>
        </nav>
      )}
      <form role="search" aria-label="Find HeyVL examples" className={styles.filters} onSubmit={(event) => event.preventDefault()}>
        <div className={styles.searchField}>
          <label htmlFor="example-query">Search examples</label>
          <input
            id="example-query"
            type="search"
            placeholder="Find a program, property, or technique…"
            value={filters.q}
            onChange={(event) => updateFilter('q', event.target.value)}
          />
        </div>
        <div className={styles.categoryFilters} role="group" aria-label="Category">
          <button type="button" className={styles.categoryFilter} aria-pressed={!filters.category} onClick={() => updateFilter('category', '')}>All examples</button>
          {categories.map(({id, label}) => (
            <button key={id} type="button" className={`${styles.categoryFilter} ${styles[id]}`} aria-pressed={filters.category === id} onClick={() => updateFilter('category', id)}>
              <span className={styles.categoryDot} aria-hidden="true" />{label}
            </button>
          ))}
        </div>
        <div className={styles.filterToolbar}>
          <div className={styles.filterPanels}>
          {([
            {key: 'topics', label: 'Topics', items: topics},
            {key: 'techniques', label: 'Techniques', items: techniques},
          ] as const).map(({key, label, items}) => (
            <details key={key} className={styles.filterPanel}>
              <summary>
                <span className={styles.panelSummary}>
                  <span>{label}</span>
                  <span className={styles.selectionCount}>{filters[key].length ? `${filters[key].length} selected` : 'All'}</span>
                </span>
              </summary>
              <div className={styles.filterPopover}>
                <fieldset className={styles.checkboxGroup} aria-label={label}>
                  {items.map(({id, label: itemLabel}) => (
                    <label key={id} className={styles.checkboxLabel}>
                      <input type="checkbox" checked={filters[key].includes(id)} onChange={() => toggleFilter(key, id)} />
                      <span>{itemLabel}</span>
                    </label>
                  ))}
                </fieldset>
                <p className={styles.filterHint}>Matches any selected {key === 'topics' ? 'topic' : 'technique'}.</p>
              </div>
            </details>
          ))}
          </div>
          <div className={styles.filterFooter}>
          <p role="status" aria-live="polite" aria-atomic="true" className={styles.resultCount}>
            {matchingExamples.length} of {examples.length} examples
          </p>
          <button type="button" className={styles.reset} disabled={!hasFilters} onClick={resetFilters}>Reset filters</button>
          </div>
        </div>
      </form>

      {matchingExamples.length === 0 ? (
        <div className={styles.empty}>
          <h2>No matching examples</h2>
          <p>Try another search or reset the filters to see all examples.</p>
          <button type="button" className="button button--secondary" onClick={resetFilters}>Show all examples</button>
        </div>
      ) : (
        <div className={styles.groups}>
          {matchingGroups.map((group) => (
            <section key={group.id} aria-labelledby={`example-group-${group.id}`}>
              <h2 id={`example-group-${group.id}`} className={styles.groupHeading}>{group.label}</h2>
              <div className={styles.cards}>
                {group.entries.map((example) => (
                  <ExampleEntry key={example.id} example={example} />
                ))}
              </div>
            </section>
          ))}
        </div>
      )}
    </div>
  );
}

import React, {useState} from 'react';
import CodeBlock from '@theme/CodeBlock';
import {getExample} from './catalog.mjs';
import {exampleCommand} from './exampleFilters.mjs';
import styles from './ExampleSources.module.css';
import codeStyles from '../css/verification-code.module.css';

type Source = {
  variantId: string;
  code: string;
  downloadUrl: string;
  title?: string;
  start?: string;
  end?: string;
  highlight?: string;
};

type Props = {exampleId: string; sources: Source[]};

function selectCode(source: Source) {
  const full = source.code.replace(/^\/\/\s*(?:RUN|XFAIL|IGNORE):[^\n]*(?:\n|$)/gm, '').trim();
  const from = source.start === undefined ? 0 : full.indexOf(source.start);
  const to = source.end === undefined ? full.length : full.indexOf(source.end, from + (source.start?.length ?? 0));
  if (from < 0 || to < from) throw new Error(`Source preview markers not found: ${source.title ?? source.variantId}`);
  const lines = full.slice(from, to).trimEnd().split('\n');
  const excerpt = lines.join('\n');
  const before = full.slice(0, from).split('\n').length - 1;
  const remainder = full.slice(to).trimEnd();
  const after = remainder ? remainder.split('\n').length : 0;
  if (source.highlight) {
    const ranges = source.highlight.split(',').flatMap(range => range.split('-').map(Number));
    if (ranges.some(line => !Number.isInteger(line) || line < 1 || line > lines.length)) {
      throw new Error(`Invalid highlight range: ${source.title ?? source.variantId}`);
    }
  }
  const fullHighlight = source.highlight?.split(',').map(range => range.split('-').map(line => Number(line) + before).join('-')).join(',');
  return {full, excerpt, before, after, fullHighlight};
}

function SourcePreview({exampleId, source}: {exampleId: string; source: Source}) {
  const example = getExample(exampleId);
  const variant = example.variants.find(candidate => candidate.id === source.variantId);
  if (!variant) throw new Error(`Unknown variant ${source.variantId} for example ${exampleId}`);
  const [expanded, setExpanded] = useState(false);
  const [showCommand, setShowCommand] = useState(false);
  const filename = variant.sourcePath.split('/').at(-1);
  const {full, excerpt, before, after, fullHighlight} = selectCode(source);
  const title = source.title ?? variant.label;
  const expected = variant.outcome === 'proof' ? 'Verified' : 'Counter-example to property found';
  const highlight = expanded ? fullHighlight : source.highlight;
  const command = exampleCommand(variant);

  return <section className={styles.preview} aria-label={title}>
    <header className={styles.previewHeader}>
      <strong>{title}</strong>
      <div className={styles.actions}>
        <span className={styles.outcome} data-outcome={variant.outcome}>Expected: <code>{expected}</code></span>
      </div>
    </header>
    <div className={styles.codePanel}>
      {before > 0 && <button type="button" className={styles.omission} onClick={() => setExpanded(!expanded)} aria-expanded={expanded} aria-label={expanded ? 'Collapse complete source' : `Show complete source, including ${before} preceding lines`} title={expanded ? 'Collapse surrounding code' : `${before} preceding lines omitted; show complete source`}>{expanded ? '−' : '…'}</button>}
      <CodeBlock className={codeStyles.code} language="heyvl" showLineNumbers={expanded ? 1 : before + 1} metastring={highlight ? `{${highlight}}` : undefined}>{expanded ? full : excerpt}</CodeBlock>
      {after > 0 && <button type="button" className={styles.omission} onClick={() => setExpanded(!expanded)} aria-expanded={expanded} aria-label={expanded ? 'Collapse complete source' : `Show complete source, including ${after} following lines`} title={expanded ? 'Collapse surrounding code' : `${after} following lines omitted; show complete source`}>{expanded ? '−' : '…'}</button>}
    </div>
    <footer className={styles.previewFooter}>
      <div className={styles.actions}>
        <a href={source.downloadUrl} download={filename} aria-label={`Download ${filename}`}>Download .heyvl</a>
        {(before > 0 || after > 0) && <button type="button" aria-expanded={expanded} onClick={() => setExpanded(!expanded)}>{expanded ? 'Collapse to excerpt' : 'Expand full source'}</button>}
        <button type="button" aria-expanded={showCommand} onClick={() => setShowCommand(!showCommand)}>{showCommand ? 'Hide run command' : 'Show run command'}</button>
      </div>
      {showCommand && <div className={styles.command}><CodeBlock language="bash">{command}</CodeBlock></div>}
    </footer>
  </section>;
}

export default function ExampleSources({exampleId, sources}: Props) {
  if (!sources.length) throw new Error(`No sources provided for example: ${exampleId}`);
  if (new Set(sources.map(source => source.variantId)).size !== sources.length) {
    throw new Error(`Duplicate source variant for example: ${exampleId}`);
  }
  return <div className={styles.sources}>
    {sources.map(source => <SourcePreview key={source.variantId} exampleId={exampleId} source={source} />)}
  </div>;
}

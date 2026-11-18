import React from 'react';
import CodeBlock from '@theme/CodeBlock';
import codeStyles from '../css/verification-code.module.css';

type Props = {source: string; start: string; end?: string; title: string; highlight?: string};

/** Select an excerpt from the imported test, so explanations follow source changes. */
export default function ExampleSourceExcerpt({source, start, end, title, highlight}: Props) {
  const from = source.indexOf(start);
  const to = end === undefined ? source.length : source.indexOf(end, from + start.length);
  if (from < 0 || to < 0) throw new Error(`Source excerpt markers not found: ${title}`);
  const code = source.slice(from, to).trimEnd().replaceAll('\t', '    ');
  return <CodeBlock className={codeStyles.code} language="heyvl" title={title} metastring={highlight ? `{${highlight}}` : undefined}>{code}</CodeBlock>;
}

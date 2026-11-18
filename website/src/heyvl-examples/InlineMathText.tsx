import React from 'react';
import katex from 'katex';

/** Render the catalog's $…$ inline math in both static HTML and filtered cards. */
export default function InlineMathText({children}: {children: string}) {
  return <>{children.split(/(\$[^$]+\$)/g).map((part, index) =>
    part.startsWith('$') && part.endsWith('$')
      ? <span key={index} dangerouslySetInnerHTML={{__html: katex.renderToString(part.slice(1, -1), {throwOnError: true, trust: false})}} />
      : part,
  )}</>;
}

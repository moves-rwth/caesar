import React from 'react';
import Link from '@docusaurus/Link';
import * as Tooltip from '@radix-ui/react-tooltip';
import styles from './Citation.module.css';

export type CitationSource = {
  href: string;
  title: string;
  authors?: string;
  year?: string | number;
  /** Short author name or source identifier, e.g. "Kaminski et al." or "RFC 3927". */
  label?: string;
  locator?: string;
  venue?: string;
};

type Props = CitationSource & {
  variant?: 'inline' | 'full';
  /** Explain why the source is relevant when rendering a full reference. */
  children?: React.ReactNode;
};

function Details({source}: {source: CitationSource}) {
  const {title, authors, year, locator, venue} = source;
  return <>
    {(authors || year) && <span className={styles.authors}>
      {authors}{authors && year ? ' ' : ''}{year ? `(${year})` : ''}.
    </span>}
    {' '}<cite>{title}</cite>.
    {locator && <> {locator}.</>}
    {venue && <> <span className={styles.venue}>{venue}.</span></>}
  </>;
}

/** Render a source inline or in full; add list markup at the call site when needed. */
export default function Citation({variant = 'inline', children, ...source}: Props) {
  const {href, title, authors, year, label, locator} = source;

  if (variant === 'full') {
    const attribution = [label ?? authors, year ? `(${year})` : undefined].filter(Boolean).join(' ');
    const fullLocator = locator?.replace(/^§§\s*/, 'Sections ').replace(/^§\s*/, 'Section ');
    return <div className={styles.reference} data-citation="full">
      <div>
        {attribution && <><span title={authors}>{attribution}</span>. </>}
        <cite className={styles.referenceTitle}><Link href={href}>{title}</Link></cite>.
        {source.venue && <> {source.venue}.</>}
      </div>
      {(children || fullLocator) && <div className={styles.note}>
        {children}
        {fullLocator && <> <span className={styles.locator}>(<Link href={href}>
          {fullLocator}<span aria-hidden="true"> {href.startsWith('http') ? '↗' : '→'}</span>
        </Link>)</span></>}
      </div>}
    </div>;
  }

  const shortLabel = `${label ?? authors ?? title}${year ? ` ${year}` : ''}${locator ? `, ${locator}` : ''}`;
  return <Tooltip.Root>
    <Tooltip.Trigger asChild>
      <Link className={styles.citation} href={href} data-citation="inline">[{shortLabel}]</Link>
    </Tooltip.Trigger>
    <Tooltip.Portal>
      <Tooltip.Content className={`card padding--sm ${styles.preview}`} side="bottom" align="start" sideOffset={6} collisionPadding={12} data-citation-preview>
        <div><Details source={source} /></div>
      </Tooltip.Content>
    </Tooltip.Portal>
  </Tooltip.Root>;
}

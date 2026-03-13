import React, { type ReactNode } from 'react';
import styles from './ProofRuleQuickCard.module.css';

export type QuickRuleLink = {
  href: string;
  label: string;
};

export type QuickRuleRow = {
  id: string;
  semantics: ReactNode;
  calculi: QuickRuleLink[];
  rules: QuickRuleLink[];
};

type QuickCardBaseProps = {
  mode: 'Verification' | 'Refutation';
  kind: ReactNode;
  boundHint?: 'lower bounds' | 'upper bounds';
  approx: 'Under' | 'Over';
};

type QuickCardProps = QuickCardBaseProps & {
  rows: QuickRuleRow[];
  semanticsAnchor?: string;
};

export type QuickGuideCard = QuickCardBaseProps & {
  rows: QuickRuleRow[];
};

type QuickGuideProps = {
  cards: QuickGuideCard[];
  kicker?: string;
  hint?: string;
  semanticsAnchor?: string;
};

function renderCodeLinks(items: QuickRuleLink[]): ReactNode[] {
  return items.map((item, index) => (
    <span key={`${item.href}:${item.label}:${index}`}>
      {index > 0 ? ', ' : null}
      <a href={item.href}><code>{item.label}</code></a>
    </span>
  ));
}

function renderRuleRows(rows: QuickRuleRow[], semanticsAnchor: string): ReactNode[] {
  return rows.flatMap((row) => [
    <div key={`${row.id}:prefix`} className={styles.quickRulePrefix}>
      <strong><a href={semanticsAnchor}>{row.semantics}</a></strong> ({renderCodeLinks(row.calculi)})
    </div>,
    <div key={`${row.id}:rules`} className={styles.quickRuleBody}>
      {renderCodeLinks(row.rules)}
    </div>,
  ]);
}

function QuickCard({ mode, kind, boundHint, approx, rows, semanticsAnchor = '#original-semantics' }: QuickCardProps) {
  const modeClass = mode === 'Verification' ? styles.quickCardVerify : styles.quickCardRefute;
  const tagClass = approx === 'Under' ? styles.quickTagUnder : styles.quickTagOver;
  const lowerClass = approx === 'Under' ? styles.quickCardLowerUnder : styles.quickCardLowerOver;
  const lowerArrow = approx === 'Under' ? '↓' : '↑';

  return (
    <article className={styles.quickCard}>
      <div className={`${styles.quickCardTop} ${modeClass}`}>
        <div className={styles.quickCardMain}>
          {mode} · <a href="../heyvl/procs">{kind}</a>
          {boundHint && <span className={styles.quickCardHint}>({boundHint})</span>}
        </div>
      </div>
      <div className={`${styles.quickCardLower} ${lowerClass} ${modeClass}`}>
        <span className={styles.quickCardLowerArrow} aria-hidden="true">{lowerArrow}</span>
        <div className={styles.quickCardLowerContent}>
          <div className={styles.quickCardAction}>
            Approximation:{' '}
            <a href="#kinds-of-approximations" className={styles.quickTagLink}>
              <span className={tagClass}>{approx}</span>
            </a>
          </div>
          <div className={styles.quickCardRules}>
            {renderRuleRows(rows, semanticsAnchor)}
          </div>
        </div>
      </div>
    </article>
  );
}

export function QuickGuide({
  cards,
  kicker = 'Quick Guide',
  hint = 'Pick approximation by goal and procedure kind.',
  semanticsAnchor = '#original-semantics',
}: QuickGuideProps) {
  return (
    <div className={styles.quickGuide}>
      <div className={styles.quickGuideHead}>
        <span className={styles.quickGuideKicker}>{kicker}</span>
        <span className={styles.quickGuideHint}>{hint}</span>
      </div>
      <div className={styles.quickGuideGrid}>
        {cards.map((card, index) => (
          <QuickCard
            key={`${card.mode}:${card.approx}:${index}`}
            mode={card.mode}
            kind={card.kind}
            boundHint={card.boundHint}
            approx={card.approx}
            rows={card.rows}
            semanticsAnchor={semanticsAnchor}
          />
        ))}
      </div>
    </div>
  );
}

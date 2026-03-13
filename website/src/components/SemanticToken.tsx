import React, { type ReactNode } from 'react';
import styles from './SemanticToken.module.css';

type SemanticVariant = 'lfp' | 'gfp' | 'proc' | 'coproc' | 'exact' | 'over' | 'under' | 'unknown';

function SemanticToken({ variant, children }: { variant: SemanticVariant; children: ReactNode }) {
  return <span className={`${styles.token} ${styles[variant]}`}>{children}</span>;
}

export const TokLFP = () => <SemanticToken variant="lfp">LFP</SemanticToken>;
export const TokGFP = () => <SemanticToken variant="gfp">GFP</SemanticToken>;
export const TokProc = () => <SemanticToken variant="proc">proc</SemanticToken>;
export const TokCoproc = () => <SemanticToken variant="coproc">coproc</SemanticToken>;
export const TokExact = () => <SemanticToken variant="exact">Exact</SemanticToken>;
export const TokOver = () => <SemanticToken variant="over">Over</SemanticToken>;
export const TokUnder = () => <SemanticToken variant="under">Under</SemanticToken>;
export const TokUnknown = () => <SemanticToken variant="unknown">Unknown</SemanticToken>;

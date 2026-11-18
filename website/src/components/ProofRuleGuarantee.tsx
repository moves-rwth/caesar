import React from 'react';
import Link from '@docusaurus/Link';
import { PROOF_RULES } from '../data/proofRules';
import { TokExact, TokOver, TokUnder } from './SemanticToken';
import styles from './ProofRuleGuarantee.module.css';

type Rule = Exclude<keyof typeof PROOF_RULES, 'calls'>;

const soundnessPage = '/docs/proof-rules/approximations';
const approximationGuide = soundnessPage + '#kinds-of-approximations';
const compatibleBody = { label: 'Compatible approximation', href: '#soundness' };
const bodyRequirements = {
  induction: compatibleBody,
  unroll: compatibleBody,
  omega: compatibleBody,
  ast: { label: <TokExact />, href: '#soundness' },
  ost: { label: <TokExact />, href: '#soundness' },
};

const lower = <>Lower bounds <code>proc</code></>;
const upper = <>Upper bounds <code>coproc</code></>;

export default function ProofRuleGuarantee({ rule }: { rule: Rule }) {
  const { cases } = PROOF_RULES[rule];
  const body = bodyRequirements[rule];
  const showRefutation = cases.some(({ refutation }) => refutation);

  return (
    <aside aria-label="Proof rule soundness" className={styles.summary} data-proof-rule-guarantee={rule}>
      <div className={styles.layout}>
        <div className={styles.matrix}>
          <table className={styles.table}>
            <thead>
              <tr>
                <th scope="col" aria-label="Calculus" />
                <th scope="col" aria-label="Approximation">
                  <Link
                    className={styles.headingLink}
                    to={approximationGuide}
                    title="Approximation"
                    aria-label="Approximation"
                  >
                    Approx.
                  </Link>
                </th>
                <th scope="col" className={styles.verify}>
                  <span aria-hidden="true">✓</span>{' '}
                  <Link className={styles.headingLink} to={soundnessPage + '#sound-verifications'}>
                    Verify
                  </Link>
                </th>
                {showRefutation && (
                  <th scope="col" className={styles.refuteHeading}>
                    <span aria-hidden="true">×</span>{' '}
                    <Link className={styles.headingLink} to={soundnessPage + '#sound-refutations'}>
                      Refute
                    </Link>
                  </th>
                )}
              </tr>
            </thead>
            <tbody>
              {cases.map(({ fixedPoint, calculi, approximation, refutation }) => {
                const under = approximation === 'Under';
                return (
                  <tr key={fixedPoint + ':' + approximation}>
                    <td className={styles.calculi}>
                      <Link to={soundnessPage + '#calculus-annotations'}>
                        {calculi.map((calculus, index) => (
                          <React.Fragment key={calculus}>
                            {index > 0 && ', '}<code>{calculus}</code>
                          </React.Fragment>
                        ))}
                      </Link>
                    </td>
                    <td>
                      <Link to={approximationGuide}>
                        {under ? <TokUnder /> : <TokOver />}
                      </Link>
                    </td>
                    <td className={styles.verify}>{under ? lower : upper}</td>
                    {showRefutation && <td>{refutation && (under ? upper : lower)}</td>}
                  </tr>
                );
              })}
            </tbody>
          </table>
        </div>
        <div className={styles.body}>
          <strong>Body</strong> <Link to={body.href}>{body.label}</Link>
        </div>
      </div>
    </aside>
  );
}

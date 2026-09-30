import React, {useState} from 'react';
import Link from '@docusaurus/Link';
import CodeBlock from '@theme/CodeBlock';
import Heading from '@theme/Heading';
import geometricRuntime from '@site/static/examples/geometric-runtime.heyvl?raw';
import styles from './styles.module.css';

const explanations = [
  {
    id: 'program',
    title: 'Program',
    lines: '{6,8-11}',
    content: (
      <p>
        Each iteration samples a fair coin with <code>flip(0.5)</code> and records one unit of cost with <code>reward 1</code>.
        The loop ends when <code>done</code> becomes true.
      </p>
    ),
  },
  {
    id: 'specification',
    title: 'Specification',
    lines: '{1-4}',
    content: (
      <p>
        A <code>coproc</code> checks an upper bound.
        Here, <code>pre 2</code> bounds the expected total cost by 2, and <code>post 0</code> adds no cost after the loop.
        The <code>@ert</code> annotation selects expected-runtime reasoning.
      </p>
    ),
  },
  {
    id: 'invariant',
    title: 'Invariant',
    lines: '{7}',
    content: (
      <>
        <p>
          The user supplies <code>[!done] * 2</code> as a bound on the remaining expected cost: 2 before success and 0 afterward.
          One iteration preserves this bound:
        </p>
        <p className={styles.equation}>1 + ½ · 0 + ½ · 2 = 2</p>
      </>
    ),
  },
  {
    id: 'verification',
    title: 'Verification',
    lines: '{1-4,7}',
    content: (
      <p>
        Caesar checks that the supplied invariant establishes the specification.
        The expected number of iterations is at most 2.
        Individual executions can take more than two iterations.
      </p>
    ),
  },
];

export default function HomepageExample() {
  const [selected, setSelected] = useState('program');
  const active = explanations.find(({id}) => id === selected);

  return (
    <section className={styles.example} aria-labelledby="example">
      <div className="container">
        <div className={styles.heading}>
          <Heading as="h2" id="example">Example: Expected Runtime of the Geometric Loop</Heading>
          <p>
            The number of iterations follows a geometric distribution: each iteration terminates the loop with probability ½, but the loop can run for arbitrarily many iterations.
            There are infinitely many possible execution paths.
            Caesar checks a supplied loop invariant to bound the expected number of iterations without enumerating these paths.
          </p>
        </div>
        <div className={styles.controls} role="group" aria-label="Highlight example lines">
          {explanations.map(({id, title}, index) => (
            <button type="button" key={id} aria-pressed={selected === id} aria-controls="geometric-code" onClick={() => setSelected(id)}>
              <span aria-hidden="true">{index + 1}</span>
              {title}
            </button>
          ))}
        </div>
        <div className={styles.layout}>
          <div className={styles.codeColumn}>
            <div id="geometric-code" className={styles.code} role="region" aria-label="Geometric loop in HeyVL">
              <CodeBlock language="heyvl" title="geometric-runtime.heyvl" showLineNumbers metastring={active.lines}>
                {geometricRuntime}
              </CodeBlock>
            </div>
            <div className={styles.result}>
              <span className={styles.check} aria-hidden="true">✓</span>
              <div><strong>Verified example</strong><br />The expected number of iterations is at most 2.</div>
            </div>
            <div className={styles.links}>
              <Link to="/docs/getting-started/first-proof">Example walkthrough →</Link>
              <a href="/examples/geometric-runtime.heyvl" download>Download HeyVL file ↓</a>
            </div>
          </div>
          <div>
            {explanations.map(({id, title, content}, index) => (
              <div className={`${styles.explanation} ${selected === id ? styles.selected : ''}`} key={id}>
                <h3>
                  <button className={styles.explanationButton} type="button" aria-pressed={selected === id} aria-controls="geometric-code" onClick={() => setSelected(id)}>
                    <span className={styles.number} aria-hidden="true">{index + 1}</span>{title}
                  </button>
                </h3>
                {content}
              </div>
            ))}
          </div>
        </div>
      </div>
    </section>
  );
}

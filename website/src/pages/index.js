import React from 'react';
import Head from '@docusaurus/Head';
import Link from '@docusaurus/Link';
import {usePluginData} from '@docusaurus/useGlobalData';
import Layout from '@theme/Layout';
import CodeBlock from '@theme/CodeBlock';
import HomepageFeatures from '@site/src/components/HomepageFeatures';
import geometricRuntime from '@site/static/examples/geometric-runtime.heyvl?raw';
import codeStyles from '@site/src/css/verification-code.module.css';
import styles from './index.module.css';

const geometricLoop = geometricRuntime.match(/\{\n([\s\S]*)\n\}/)[1]
  .split('\n')
  .filter((line) => !line.trimStart().startsWith('@') && !line.trimStart().startsWith('reward '))
  .map((line) => line.replace(/^ {4}/, ''))
  .join('\n');

function HomepageHeader({latestRelease}) {
  return (
    <header className={styles.hero}>
      <div className={`container ${styles.heroGrid}`}>
        <div>
          <div className={styles.brand}>
            <img src="/img/laurel.svg" alt="" width="36" height="56" />
            <span>Caesar</span>
          </div>
          <h1>A Verifier for Probabilistic Programs</h1>
          <div className={styles.introduction}>
            <p>
              Caesar proves bounds on probabilities, expected runtimes, and resource usage.
            </p>
            <p>
              Write a model in Caesar’s programming language, <Link to="/docs/heyvl">HeyVL</Link>, and add proof annotations.
              Caesar verifies the stated bounds symbolically.
            </p>
          </div>
          <ul className={styles.capabilities} aria-label="Caesar capabilities">
            <li><Link to="/docs/stdlib/numbers">Infinite state spaces</Link></li>
            <li><Link to="/docs/proof-rules">Unbounded loops</Link></li>
            <li><Link to="/docs/heyvl/procs#calling-procedures">Recursion</Link></li>
            <li><Link to="/docs/heyvl/statements#nondeterministic-choices">Nondeterminism</Link></li>
            <li><Link to="/docs/proof-rules/approximations">Sound proofs and refutations</Link></li>
          </ul>
          <div className={styles.actions}>
            <Link className="button button--primary" to="/docs/getting-started/installation">Install Caesar</Link>
            <Link className="button button--outline button--primary" to="#example">See an example</Link>
          </div>
          <Link className={styles.release} to={latestRelease.url}>
            <span className={styles.releaseDot} aria-hidden="true" />
            {latestRelease.label === 'Latest release' ? 'Latest release' : `Latest release: ${latestRelease.label}`}
            <span aria-hidden="true"> ↗</span>
          </Link>
        </div>
        <aside className={styles.program} aria-labelledby="program-title">
          <h2 id="program-title">A Probabilistic Program</h2>
          <p>Each iteration ends the loop with probability ½.</p>
          <CodeBlock language="heyvl">{geometricLoop}</CodeBlock>
          <div className={styles.proofStep}>
            <span aria-hidden="true">↓</span>
            <span>Caesar checks the supplied loop invariant.</span>
          </div>
          <div className={styles.guarantee}>
            <span className={styles.check} aria-hidden="true">✓</span>
            <div>
              <strong className={styles.guaranteeFormula} aria-hidden="true">𝔼[iterations] ≤ 2</strong>
              <p className={styles.guaranteeDescription}>The expected number of iterations is at most 2.</p>
              <Link to="#example">See the specification and proof →</Link>
            </div>
          </div>
        </aside>
      </div>
    </header>
  );
}

export default function Home() {
  const {latestPost, latestRelease} = usePluginData('homepage-metadata');
  const title = 'Caesar — Verification infrastructure for probabilistic programs';
  return (
    <Layout description="Caesar is a verification infrastructure for probabilistic programs, combining HeyVL, reusable proof rules, and SMT-based verification to prove quantitative bounds.">
      <Head>
        <title>{title}</title>
        <meta property="og:title" content={title} />
      </Head>
      <div className={`${styles.homepage} ${codeStyles.code}`}>
        <HomepageHeader latestRelease={latestRelease} />
        <main>
          <HomepageFeatures latestPost={latestPost} />
        </main>
      </div>
    </Layout>
  );
}

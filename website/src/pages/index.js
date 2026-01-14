import React from 'react';
import clsx from 'clsx';
import Link from '@docusaurus/Link';
import useDocusaurusContext from '@docusaurus/useDocusaurusContext';
import Layout from '@theme/Layout';
import HomepageFeatures from '@site/src/components/HomepageFeatures';

import styles from './index.module.css';

function HomepageHeader() {
  const { siteConfig } = useDocusaurusContext();
  return (
    <header className={clsx('hero hero--dark', styles.heroBanner)}>
      <div className="container">
        <div className={`row ${styles.heroBannerRow}`}>
          <div className="col col--7">
            <h1 className={clsx('hero__title', styles.heroTitle)}>
              <img src="/img/laurel.svg" className={styles.heroLogo} alt="" />
              <span>{siteConfig.title}</span>
              <img src="/img/laurel.svg" className={styles.heroLogo} style={{ transform: 'scale(-1, 1)' }} alt="" />
            </h1>
            <p className="hero__subtitle">
              <span style={{"display": "inline-block"}}>A Deductive Verifier&nbsp;</span>
              <span style={{"display": "inline-block"}}>for Probabilistic Programs</span>
            </p>
            <div className={styles.quickButtons}>
              <Link
                className="button button--primary"
                to="/docs/getting-started">
                Get Started →
              </Link>
              <Link
                className="button button--primary"
                to="https://marketplace.visualstudio.com/items?itemName=rwth-moves.caesar">
                VSCode Extension
              </Link>
              <Link
                className="button button--primary"
                to="/docs/">
                Docs
              </Link>
            </div>
          </div>
          <div className={`col col--5 ${styles.heroImageWrapper}`}>
            <Link to="/docs/" className={`margin--md shadow--md`} >
              <img src="img/architecture-oopsla23.svg" alt="Architecture diagram for Caesar" />
            </Link>
          </div>
        </div>
      </div>
    </header>
  );
}

export default function Home() {
  const { siteConfig } = useDocusaurusContext();
  return (
    <Layout
      title={`Caesar Verifier`}
      description={`${siteConfig.tagline}`}>
      <HomepageHeader />
      <main>
        <HomepageFeatures />
      </main>
    </Layout>
  );
}

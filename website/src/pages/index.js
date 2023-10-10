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
            <h1 className="hero__title">
              <img src="/img/laurel.svg" className={styles.heroLogo} />
              {siteConfig.title}
              <img src="/img/laurel.svg" className={styles.heroLogo} style={{ transform: 'scale(-1, 1)' }} />
            </h1>
            <p className="hero__subtitle">{siteConfig.tagline}</p>
            <Link
              className="button button--primary button--lg"
              to="/docs/getting-started">
              Get Started →
            </Link>
            <span> </span>
            <Link
              className="button button--primary button--lg"
              to="/docs/">
              Docs
            </Link>
          </div>
          <div className="col col--5">
            <Link to="/docs/">
              <img src="img/architecture-oopsla23.svg" className={`padding--md shadow--md ${styles.heroImage}`} />
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
      title={`Caesar Verification Infrastructure`}
      description={`${siteConfig.tagline}`}>
      <HomepageHeader />
      <main>
        <HomepageFeatures />
      </main>
    </Layout>
  );
}

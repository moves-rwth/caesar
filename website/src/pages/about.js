import React from 'react';
import Layout from '@theme/Layout';
import MDXContent from '@theme/MDXContent';
import TOC from '@theme/TOC';
import TOCCollapsible from '@theme/TOCCollapsible';
import AboutContent, {toc} from './_about.mdx';
import styles from './about.module.css';

export default function About() {
  return (
    <Layout title="About Caesar" description="About Caesar" wrapperClassName={styles.about}>
      <main className={`container padding-top--md padding-bottom--lg ${styles.layout}`}>
        <article className={styles.article}>
          <TOCCollapsible className={`theme-doc-toc-mobile ${styles.mobileContents}`} toc={toc} />
          <div className="theme-doc-markdown markdown">
            <MDXContent>
              <AboutContent />
            </MDXContent>
          </div>
        </article>
        <nav className={styles.desktopContents} aria-label="On this page">
          <TOC toc={toc} className="theme-doc-toc-desktop" />
        </nav>
      </main>
    </Layout>
  );
}

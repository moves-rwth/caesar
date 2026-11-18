import React from 'react';
import BlogSidebar from '@theme/BlogSidebar';
import Layout from '@theme/Layout';
import type {Props} from '@theme/BlogLayout';
import styles from './styles.module.css';

export default function BlogLayout({sidebar, toc, children, ...layoutProps}: Props) {
  const hasSidebar = Boolean(sidebar?.items.length);

  return (
    <Layout {...layoutProps}>
      <div className={styles.layout}>
        {hasSidebar && (
          <div className={styles.sidebar}>
            <BlogSidebar sidebar={sidebar} />
          </div>
        )}
        <div className={`container padding-top--md padding-bottom--lg ${styles.content}`}>
          <div className="row">
            <main className={`col col--9 ${styles.posts}`}>{children}</main>
            {toc && <div className="col col--3">{toc}</div>}
          </div>
        </div>
      </div>
    </Layout>
  );
}

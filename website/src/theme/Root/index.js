import React from 'react';
import Head from '@docusaurus/Head';
import plexSans from '@site/static/fonts/ibm-plex/IBMPlexSans-SemiBold.woff2';
import sourceCode from '@site/static/fonts/source-code-pro/SourceCodePro-Regular.otf.woff2';

export default function Root({children}) {
  return (
    <>
      <Head>
        <link rel="preload" href={plexSans} as="font" type="font/woff2" crossOrigin="anonymous" />
        <link rel="preload" href={sourceCode} as="font" type="font/woff2" crossOrigin="anonymous" />
      </Head>
      {children}
    </>
  );
}

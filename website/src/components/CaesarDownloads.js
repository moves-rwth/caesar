import React from 'react';
import Link from '@docusaurus/Link';
import useBaseUrl from '@docusaurus/useBaseUrl';
import styles from './CaesarDownloads.module.css';

function DownloadLinks({asset, label, formats}) {
  const baseUrl = useBaseUrl(`/img/${asset}`);

  return <span className={styles.downloadLinks}>
    {formats.map((format) => (
      <a key={format} href={`${baseUrl}.${format}`} download aria-label={`Download ${label} as ${format.toUpperCase()}`}>
        {format.toUpperCase()}
      </a>
    ))}
  </span>;
}

export default function CaesarDownloads() {
  const logoUrl = useBaseUrl('/img/caesar-logo.svg');
  const qrUrl = useBaseUrl('/img/caesar-qr.svg');

  return (
    <div className={styles.assets}>
      <div className={styles.asset}>
        <h4>Caesar Logo</h4>
        <div className={styles.assetPreview}>
          <img className={styles.logo} src={logoUrl} alt="Caesar name and laurel" width="168" height="60" />
        </div>
        <dl className={styles.logoDownloads}>
          <div>
            <dt>With Name</dt>
            <dd><DownloadLinks asset="caesar-logo" label="Caesar logo with name" formats={['svg', 'png']} /></dd>
          </div>
          <div>
            <dt>Laurel</dt>
            <dd><DownloadLinks asset="laurel" label="Caesar laurel" formats={['svg', 'png']} /></dd>
          </div>
        </dl>
      </div>
      <div className={styles.asset}>
        <h4>Website QR Code</h4>
        <div className={styles.assetPreview}>
          <img className={styles.qr} src={qrUrl} alt="Green QR code with the Caesar laurel at its center" width="128" height="128" />
        </div>
        <div className={styles.assetLinks}>
          <Link href="https://www.caesarverifier.org/">caesarverifier.org</Link>
          <DownloadLinks asset="caesar-qr" label="Caesar QR code" formats={['svg', 'png', 'pdf']} />
        </div>
      </div>
    </div>
  );
}

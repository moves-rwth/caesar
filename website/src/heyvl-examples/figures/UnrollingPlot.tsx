import React, {useId} from 'react';
import styles from './Figure.module.css';

// Caesar's k unfoldings include the final guard check before returning the counter.
const approximations = [10, 11, 12].map(depth => ({
  depth,
  value: 1 - depth / 2 ** (depth - 1),
}));
const x = (depth: number) => 60 + (depth - 10) * 104;
const y = (value: number) => 130 - (value - 0.98) / 0.02 * 104;

export default function UnrollingPlot({children}: {children: React.ReactNode}) {
  const id = useId();
  return (
    <div className={styles.context} style={{'--diagram-width': '288px'} as React.CSSProperties}>
      <div className={styles.layout}>
        <div className={styles.prose}>{children}</div>
        <svg className={styles.plot} viewBox="0 0 360 184" width="360" height="184"
          role="img" aria-labelledby={`${id}-title ${id}-description`}>
          <title id={`${id}-title`}>Finite unrolling refutes the geometric loop's bound of 0.99</title>
          <desc id={`${id}-description`}>
            Starting with count zero and running true, the lower approximation is 251/256 after ten unfoldings, 1013/1024 after eleven, and 509/512 after twelve.
            The twelfth approximation is the first to exceed 0.99.
            The vertical axis is zoomed to the interval from 0.98 to one.
          </desc>
          <path d="M 60 26 V 130 H 276" className={styles.plotAxis} />
          <path d={`M 60 ${y(0.99)} H 282`} className={styles.plotThreshold} />
          <text x="291" y={y(0.99)} className={styles.plotBound}>0.99</text>
          {[0.98, 1].map(value => (
            <g key={value}>
              <path d={`M 56 ${y(value)} H 60`} className={styles.plotAxis} />
              <text x="48" y={y(value)} textAnchor="end">{value.toFixed(2)}</text>
            </g>
          ))}
          <text x="60" y="10" textAnchor="start">Lower approximation</text>
          <polyline points={approximations.map(point => `${x(point.depth)},${y(point.value)}`).join(' ')} className={styles.plotCurve} />
          {approximations.map(point => (
            <g key={point.depth}>
              <circle cx={x(point.depth)} cy={y(point.value)} r="2.25" className={styles.plotPoint} />
              <path d={`M ${x(point.depth)} 130 V 134`} className={styles.plotAxis} />
              <text x={x(point.depth)} y="145">{point.depth}</text>
            </g>
          ))}
          <path d={`M 271 ${y(509 / 512) - 3} L 284 46`} className={styles.plotAxis} />
          <text x="277" y="34" textAnchor="start">509/512</text>
          <text x="164" y="168">Unfoldings</text>
        </svg>
      </div>
    </div>
  );
}

import React, {useId} from 'react';
import styles from './Figure.module.css';

const lastTime = 4.5;
const x = (seconds: number) => 54 + seconds * 55;
const y = (probability: number) => 126 - probability * 90;

function survivalPath(cacheDelay: number, retryProbability: number) {
  const segments = [`M ${x(0)} ${y(1)}`];
  for (let attempts = 1; cacheDelay + attempts <= lastTime; attempts += 1) {
    segments.push(`H ${x(cacheDelay + attempts)} V ${y(retryProbability ** attempts)}`);
  }
  return [...segments, `H ${x(lastTime)}`].join(' ');
}

export default function RetryLatencyPlot({children}: {children: React.ReactNode}) {
  const id = useId();
  return (
    <div className={styles.context} style={{'--diagram-width': '288px'} as React.CSSProperties}>
      <div className={styles.layout}>
        <div className={styles.prose}>{children}</div>
        <svg className={styles.plot} viewBox="0 0 320 184" width="320" height="184"
          role="img" aria-labelledby={`${id}-title`} aria-describedby={`${id}-description`}>
          <title id={`${id}-title`}>Probability of still waiting with and without a cache</title>
          <desc id={`${id}-description`}>
            The uncached probability drops by a factor of two after each whole second.
            The cached probability drops by a factor of three at 1.5 seconds and once per second thereafter.
            At one second the uncached probability is one half and the cached probability is one.
            At 2.5 seconds the probabilities are one quarter without a cache and one ninth with a cache.
          </desc>
          <text x="8" y="13" textAnchor="start">Chance of still waiting</text>
          <path d={`M ${x(0)} ${y(1)} V ${y(0)} H ${x(lastTime)}`} className={styles.plotAxis} />
          {[0, 0.5, 1].map(probability => (
            <g key={probability}>
              <path d={`M ${x(0) - 4} ${y(probability)} H ${x(0)}`} className={styles.plotAxis} />
              <text x={x(0) - 7} y={y(probability)} textAnchor="end">{probability * 100}%</text>
            </g>
          ))}
          {[0, 1, 2, 3, 4].map(seconds => (
            <g key={seconds}>
              <path d={`M ${x(seconds)} ${y(0)} v 4`} className={styles.plotAxis} />
              <text x={x(seconds)} y="140">{seconds}</text>
            </g>
          ))}
          <text x="178" y="158">Elapsed time (s)</text>
          <path d={survivalPath(0.5, 1 / 3)} className={styles.plotCurve} />
          <path d={survivalPath(0, 1 / 2)} className={styles.retryBaseline} />
          <path d="M 54 175 H 78" className={styles.retryBaseline} />
          <text x="84" y="175" textAnchor="start">Without cache</text>
          <path d="M 203 175 H 227" className={styles.plotCurve} />
          <text x="233" y="175" textAnchor="start">With cache</text>
        </svg>
      </div>
    </div>
  );
}

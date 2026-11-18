import React, {useId} from 'react';
import styles from './Figure.module.css';

const boundaries = Array.from({length: 9}, (_, index) => index * 10 / 8);
const x = (distance: number) => 16 + distance * 28.8;
const finishThreshold = 3;

export default function TortoiseHareJump({children}: {children: React.ReactNode}) {
  const id = useId();
  return (
    <div className={styles.context} style={{'--diagram-width': '288px'} as React.CSSProperties}>
      <div className={styles.layout}>
        <div className={styles.prose}>{children}</div>
        <svg className={styles.plot} viewBox="0 0 320 110" width="320" height="110"
          role="img" aria-labelledby={`${id}-title`} aria-describedby={`${id}-description`}>
          <title id={`${id}-title`}>The hare's jump intervals and the finish threshold</title>
          <desc id={`${id}-description`}>
            The hare starts at zero and the tortoise advances from two to three.
            If the hare moves, its possible jump distances from zero to ten are divided into eight equal intervals.
            The highlighted interval from 2.5 to 3.75 contains both jumps that leave the race running and jumps longer than three that end it.
          </desc>
          <text x="160" y="13">Jump distance if the hare moves</text>
          <text x={x(finishThreshold)} y="32">Tortoise at 3</text>
          <rect x={x(2.5)} y="49" width={x(3.75) - x(2.5)} height="16" className={styles.jumpInterval} />
          <path d={`M ${x(0)} 57 H ${x(10)}`} className={styles.plotAxis} />
          {boundaries.map(distance => (
            <path key={distance} d={`M ${x(distance)} 51 V 63`} className={styles.plotAxis} />
          ))}
          <path d={`M ${x(finishThreshold)} 41 V 69`} className={styles.jumpThreshold} />
          {[0, 2.5, 3.75, 10].map(distance => (
            <text key={distance} x={x(distance)} y="76">{distance}</text>
          ))}
          <text x={x(1.5)} y="100">Continue</text>
          <text x={x(6.5)} y="100">Finish</text>
        </svg>
      </div>
    </div>
  );
}

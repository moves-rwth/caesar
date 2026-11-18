import React from 'react';
import styles from './FastDiceRollerPrefix.module.css';

const outcomeCount = 5;
const iterations = [
  {flip: 2, size: 4},
  {flip: 3, size: 8},
  {flip: 4, size: 6},
];

export default function FastDiceRollerPrefix() {
  return (
    <figure className={styles.figure}>
      <figcaption className={styles.caption}>
        <span>Fast Dice Roller with <code>n = {outcomeCount}</code></span>
        <span className={styles.legend}>
          <span><span className={styles.returned} aria-hidden="true" />Returned</span>
          <span><span className={styles.continuing} aria-hidden="true" />Continues</span>
        </span>
      </figcaption>
      <ol className={styles.iterations} role="list">
        {iterations.map(({flip, size}) => {
          const returns = size >= outcomeCount;
          const description = returns
            ? 'Values 0 through 4 return. The remaining values continue.'
            : 'All values continue.';

          return (
            <li key={flip}>
              <strong className={styles.heading}>After flip {flip}</strong>
              <ol aria-label={`Values after flip ${flip}. ${description}`} className={styles.strip} role="list">
                {Array.from({length: size}, (_, value) => {
                  const returned = returns && value < outcomeCount;
                  const recycled = returns && !returned;

                  return (
                    <li key={value} className={returned ? styles.returned : styles.continuing}>
                      {recycled ? `${value}→${value - outcomeCount}` : value}
                    </li>
                  );
                })}
              </ol>
            </li>
          );
        })}
      </ol>
    </figure>
  );
}

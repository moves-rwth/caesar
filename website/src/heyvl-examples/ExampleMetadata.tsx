import React from 'react';
import {categories, getExample, topics, techniques} from './catalog.mjs';
import styles from './ExampleMetadata.module.css';

const categoryLabels = new Map(categories.map(({id, label}) => [id, label]));
const topicLabels = new Map(topics.map(({id, label}) => [id, label]));
const techniqueLabels = new Map(techniques.map(({id, label}) => [id, label]));

export default function ExampleMetadata({exampleId}: {exampleId: string}) {
  const example = getExample(exampleId);
  const exampleTopics = [...new Set([...example.topics, ...example.variants.flatMap((variant) => variant.topics || [])])];
  const exampleTechniques = [...new Set(example.variants.flatMap((variant) => variant.techniques))];

  return (
    <div className={`${styles.metadata} ${styles[example.category]}`} role="group" aria-label="Example metadata">
      <span className={styles.category}>{categoryLabels.get(example.category)}</span>
      <ul className={`${styles.values} ${styles.topics}`} aria-label={`${example.title} topics`}>
        {exampleTopics.map((topic) => <li key={topic}>{topicLabels.get(topic) || topic}</li>)}
      </ul>
      <ul className={`${styles.values} ${styles.techniques}`} aria-label={`${example.title} techniques`}>
        {exampleTechniques.map((technique) => <li key={technique}><code>{techniqueLabels.get(technique) || technique}</code></li>)}
      </ul>
    </div>
  );
}

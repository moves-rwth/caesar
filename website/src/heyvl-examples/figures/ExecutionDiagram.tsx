import React, {useId} from 'react';
import styles from './Figure.module.css';

type Kind = 'escaping-spline' | 'countdown' | 'packet-retries' | 'geometric-loop' | 'zeroconf';
type State = {x: number; y: number; label: string; radius?: number; terminal?: boolean; textOnly?: boolean};
type Edge = {path: string; label: string; x: number; y: number};
type Diagram = {
  width: number;
  height: number;
  radius?: number;
  fontSize?: number;
  initial: {path: string; state: number};
  title: string;
  description: string;
  states: State[];
  edges: Edge[];
  notes?: {x: number; y: number; label: string}[];
};

const diagrams: Record<Kind, Diagram> = {
  // Adapted from Bohnenkamp et al. (2003), Figure 1, with detection ending this address choice.
  zeroconf: {
    width: 500, height: 252,
    initial: {path: 'M 1 70 H 37', state: 0},
    title: 'One Zeroconf address choice with three probes',
    description:
      'An incoming arrow marks the address choice. ' +
      'With probability 1−c the address is free, and with probability c probing starts with three probes remaining. ' +
      'Each probe detects the collision with probability 1−q; otherwise, one fewer probe remains. ' +
      'Free and detected return true, while three unsuccessful attempts leave the collision undetected and return false.',
    states: [
      {x: 44, y: 70, label: '', radius: 7},
      {x: 146, y: 70, label: '3'},
      {x: 248, y: 70, label: '2'},
      {x: 350, y: 70, label: '1'},
      {x: 44, y: 18, label: '', radius: 7, terminal: true},
      {x: 220, y: 200, label: '', radius: 7, terminal: true},
      {x: 455, y: 70, label: '', radius: 7, terminal: true},
    ],
    edges: [
      {path: 'M 44 63 V 29', label: '1 − c', x: 85, y: 46},
      {path: 'M 51 70 H 125', label: 'c', x: 88, y: 50},
      {path: 'M 167 70 H 227', label: 'q', x: 197, y: 50},
      {path: 'M 269 70 H 329', label: 'q', x: 299, y: 50},
      {path: 'M 371 70 H 444', label: 'q', x: 407, y: 50},
      {path: 'M 146 91 L 214 191', label: '1 − q', x: 120, y: 142},
      {path: 'M 248 91 L 223 189', label: '1 − q', x: 279, y: 141},
      {path: 'M 338 87 Q 306 200 231 200', label: '1 − q', x: 345, y: 183},
    ],
    notes: [
      {x: 44, y: 109, label: 'choose'},
      {x: 84, y: 18, label: 'free'},
      {x: 220, y: 230, label: 'detected'},
      {x: 455, y: 109, label: 'missed'},
      {x: 248, y: 14, label: 'probes left'},
      {x: 422, y: 14, label: 'M = 3'},
    ],
  },
  'geometric-loop': {
    width: 460, height: 179,
    initial: {path: 'M 128 2 V 29', state: 0},
    title: 'Geometric loop starting with count zero and running true',
    description:
      'An incoming arrow marks count zero with running true. ' +
      'Each fair coin flip either advances along the upper row and increments count on tails, or moves to the stopped state at the same count on heads. ' +
      'The chain continues to arbitrarily large counts.',
    states: [
      {x: 128, y: 50, label: '0'},
      {x: 240, y: 50, label: '1'},
      {x: 352, y: 50, label: '2'},
      {x: 128, y: 139, label: '0', terminal: true},
      {x: 240, y: 139, label: '1', terminal: true},
      {x: 352, y: 139, label: '2', terminal: true},
    ],
    edges: [
      {path: 'M 149 50 H 219', label: '½', x: 184, y: 31},
      {path: 'M 261 50 H 331', label: '½', x: 296, y: 31},
      {path: 'M 373 50 H 420', label: '½', x: 402, y: 31},
      {path: 'M 128 71 V 114', label: '½', x: 151, y: 94},
      {path: 'M 240 71 V 114', label: '½', x: 263, y: 94},
      {path: 'M 352 71 V 114', label: '½', x: 375, y: 94},
    ],
    notes: [
      {x: 240, y: 10, label: 'count'},
      {x: 42, y: 50, label: 'running'},
      {x: 42, y: 139, label: 'stopped'},
      {x: 435, y: 50, label: '…'},
      {x: 435, y: 139, label: '…'},
    ],
  },
  // The spline layout follows McIver et al. (2018), Section 5.4, Figure 4.
  'escaping-spline': {
    width: 460, height: 210,
    initial: {path: 'M 140 2 V 37', state: 1},
    title: 'Escaping spline',
    description:
      'An incoming arrow marks the initial position one. ' +
      'From each positive position x, one iteration jumps to zero with probability 1/(x+1), or advances to x+1 with probability x/(x+1), and zero ends the execution.',
    states: [
      {x: 34, y: 58, label: '0', terminal: true},
      {x: 140, y: 58, label: '1'},
      {x: 246, y: 58, label: '2'},
      {x: 352, y: 58, label: '3'},
    ],
    edges: [
      {path: 'M 161 58 Q 193 24 225 58', label: '½', x: 193, y: 19},
      {path: 'M 267 58 Q 299 24 331 58', label: '⅔', x: 299, y: 19},
      {path: 'M 373 58 Q 399 30 421 49', label: '¾', x: 402, y: 19},
      {path: 'M 119 58 H 60', label: '½', x: 88, y: 43},
      {path: 'M 232 74 C 185 135 107 135 48 79', label: '⅓', x: 145, y: 140},
      {path: 'M 340 76 C 260 190 104 190 48 79', label: '¼', x: 210, y: 187},
    ],
    notes: [{x: 432, y: 58, label: '…'}],
  },
  countdown: {
    width: 112, height: 168, radius: 11, fontSize: 17,
    initial: {path: 'M 32 1 V 13', state: 0},
    title: 'Countdown from three',
    description:
      'An incoming arrow marks the initial counter value three. ' +
      'The chain runs downward to zero, with probability one half of decreasing and probability one half of taking the self-loop at each positive counter value.',
    states: [
      {x: 32, y: 24, label: '3'},
      {x: 32, y: 64, label: '2'},
      {x: 32, y: 104, label: '1'},
      {x: 32, y: 144, label: '0', terminal: true},
    ],
    edges: [
      {path: 'M 32 35 V 53', label: '½', x: 15, y: 44},
      {path: 'M 32 75 V 93', label: '½', x: 15, y: 84},
      {path: 'M 32 115 V 129', label: '½', x: 15, y: 122},
      {path: 'M 41 17 C 89 -1 89 49 41 31', label: '½', x: 96, y: 24},
      {path: 'M 41 57 C 89 39 89 89 41 71', label: '½', x: 96, y: 64},
      {path: 'M 41 97 C 89 79 89 129 41 111', label: '½', x: 96, y: 104},
    ],
  },
  'packet-retries': {
    width: 460, height: 188,
    initial: {path: 'M 1 54 H 19', state: 0},
    title: 'Packet retries with three allowed attempts',
    description:
      'An incoming arrow marks the initial state with zero failures. ' +
      'The sender receives an acknowledgement with probability p or adds one failure with probability 1−p, and the third failure exhausts the attempt limit.',
    states: [
      {x: 40, y: 54, label: '0'},
      {x: 155, y: 54, label: '1'},
      {x: 270, y: 54, label: '2'},
      {x: 414, y: 54, label: 'give up', textOnly: true},
      {x: 210, y: 168, label: 'success', textOnly: true},
    ],
    edges: [
      {path: 'M 61 54 H 134', label: '1 − p', x: 98, y: 34},
      {path: 'M 176 54 H 249', label: '1 − p', x: 212, y: 34},
      {path: 'M 291 54 H 364', label: '1 − p', x: 328, y: 34},
      {path: 'M 40 75 Q 40 168 151 168', label: 'p', x: 28, y: 132},
      {path: 'M 164 73 L 198 151', label: 'p', x: 162, y: 111},
      {path: 'M 261 73 L 222 151', label: 'p', x: 269, y: 111},
    ],
    notes: [{x: 40, y: 12, label: 'failed'}, {x: 414, y: 87, label: 'MAX = 3'}],
  },
};

export default function ExecutionDiagram({kind, children}: {kind: Kind; children: React.ReactNode}) {
  const id = useId();
  const diagram = diagrams[kind];
  const arrow = `${id}-arrow`;
  const radius = diagram.radius ?? 21;
  const width = Math.min(diagram.width, 288);
  const markerSize = 5 * diagram.width / width;
  return (
    <div className={styles.context} style={{'--diagram-width': `${width}px`} as React.CSSProperties}>
      <div className={`${styles.layout} ${diagram.width < diagram.height ? styles.portrait : ''}`}>
        <div className={styles.prose}>{children}</div>
        <svg viewBox={`0 0 ${diagram.width} ${diagram.height}`} width={diagram.width} height={diagram.height}
          style={{fontSize: diagram.fontSize}}
          role="img" aria-labelledby={`${id}-title ${id}-description`}>
          <title id={`${id}-title`}>{diagram.title}</title>
          <desc id={`${id}-description`}>{diagram.description}</desc>
          <defs>
            <marker id={arrow} viewBox="0 0 8 8" refX="7" refY="4" markerWidth={markerSize} markerHeight={markerSize} markerUnits="userSpaceOnUse" orient="auto">
              <path d="M 0 0 L 8 4 L 0 8" className={styles.arrow} />
            </marker>
          </defs>
          <path d={diagram.initial.path} className={styles.edge} markerEnd={`url(#${arrow})`}
            data-initial-state={diagram.states[diagram.initial.state].label} />
          {diagram.edges.map((edge, index) => (
            <path key={index} d={edge.path} className={styles.edge} markerEnd={`url(#${arrow})`} />
          ))}
          {diagram.states.map(({x, y, label, terminal, textOnly, radius: stateRadius = radius}, index) => (
            <g key={index}>
              {!textOnly && <>
                {terminal && <circle cx={x} cy={y} r={stateRadius + 4} className={styles.state} />}
                <circle cx={x} cy={y} r={stateRadius} className={styles.state} />
              </>}
              <text x={x} y={y}>{label}</text>
            </g>
          ))}
          {diagram.edges.map((edge, index) => (
            <text key={index} x={edge.x} y={edge.y} className={styles.probability}>{edge.label}</text>
          ))}
          {diagram.notes?.map((note, index) => (
            <text key={index} x={note.x} y={note.y} className={styles.note}>{note.label}</text>
          ))}
        </svg>
      </div>
    </div>
  );
}

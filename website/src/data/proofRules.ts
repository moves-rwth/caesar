const least = { id: 'lfp', calculi: ['@wp', '@ert'] } as const;
const greatest = { id: 'gfp', calculi: ['@wlp', '@uwlp'] } as const;

export const FIXED_POINTS = [least, greatest] as const;

type FixedPoint = (typeof FIXED_POINTS)[number];
type Calculus = FixedPoint['calculi'][number];
type Approximation = 'Under' | 'Over';

type BoundCase = {
  fixedPoint: FixedPoint['id'];
  calculi: readonly Calculus[];
  approximation: Approximation;
  refutation?: true;
};

type Rule = {
  title: string;
  href: string;
  annotations: readonly string[];
  cases: readonly BoundCase[];
};

const unfoldingCases: readonly BoundCase[] = [
  { fixedPoint: least.id, calculi: least.calculi, approximation: 'Under', refutation: true },
  { fixedPoint: greatest.id, calculi: greatest.calculi, approximation: 'Over', refutation: true },
];

const inductionCases: readonly BoundCase[] = [
  { fixedPoint: least.id, calculi: least.calculi, approximation: 'Over' },
  { fixedPoint: greatest.id, calculi: greatest.calculi, approximation: 'Under' },
];

type RuleId = 'induction' | 'unroll' | 'omega' | 'ast' | 'ost' | 'calls';

export const PROOF_RULES: Record<RuleId, Rule> = {
  induction: {
    title: 'Induction and k-Induction',
    href: '/docs/proof-rules/induction',
    annotations: ['@invariant', '@k_induction'],
    cases: inductionCases,
  },
  unroll: {
    title: 'Loop Unrolling',
    href: '/docs/proof-rules/unrolling',
    annotations: ['@unroll'],
    cases: unfoldingCases,
  },
  omega: {
    title: 'ω-Invariants',
    href: '/docs/proof-rules/omega-invariants',
    annotations: ['@omega_invariant'],
    cases: unfoldingCases,
  },
  ast: {
    title: 'Almost-Sure Termination',
    href: '/docs/proof-rules/ast#new-proof-rule',
    annotations: ['@ast'],
    cases: [{ fixedPoint: least.id, calculi: ['@wp'], approximation: 'Under' }],
  },
  ost: {
    title: 'Optional Stopping Theorem',
    href: '/docs/proof-rules/ost',
    annotations: ['@ost'],
    cases: [{ fixedPoint: least.id, calculi: least.calculi, approximation: 'Under' }],
  },
  calls: {
    title: 'Procedure Calls',
    href: '/docs/heyvl/procs#calling-procedures',
    annotations: [],
    cases: inductionCases.map((entry) => ({ ...entry, refutation: true })),
  },
};

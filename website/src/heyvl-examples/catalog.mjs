/**
 * The catalog describes the examples whose source code lives in the test suite.
 * Variant IDs are local to an example, and techniques and outcomes describe each variant.
 */
export const categories = [
  {id: 'boolean', label: 'Boolean'},
  {id: 'probabilistic', label: 'Probabilistic'},
];

export const groups = [
  {id: 'random-walks', label: 'Random Walks and Countdowns'},
  {id: 'sampling', label: 'Sampling and Probabilistic Models'},
  {id: 'rewards', label: 'Rewards and Resource Consumption'},
  {id: 'protocols', label: 'Protocols'},
  {id: 'data-structures', label: 'Data Structures'},
];

export const topics = [
  {id: 'ast', label: 'Almost-sure termination'},
  {id: 'past', label: 'Positive almost-sure termination'},
  {id: 'axioms', label: 'Axioms'},
  {id: 'conditioning', label: 'Conditioning'},
  {id: 'continuous', label: 'Continuous distributions'},
  {id: 'expectation', label: 'Expected values'},
  {id: 'moments', label: 'Higher moments'},
  {id: 'runtime', label: 'Expected runtime'},
  {id: 'lists', label: 'Lists'},
  {id: 'probability', label: 'Probability bounds'},
  {id: 'sampling', label: 'Sampling algorithms'},
  {id: 'protocols', label: 'Protocols'},
  {id: 'refutation', label: 'Refutation'},
  {id: 'termination', label: 'Termination'},
  {id: 'trees', label: 'Trees'},
  {id: 'functions', label: 'User-defined functions'},
];

export const techniques = [
  {id: 'ast', label: '@ast'},
  {id: 'invariants', label: '@invariant'},
  {id: 'k-induction', label: '@k_induction'},
  {id: 'loop-free', label: 'Loop-free reasoning'},
  {id: 'omega-invariants', label: '@omega_invariant'},
  {id: 'optional-stopping', label: '@ost'},
  {id: 'past', label: '@past'},
  {id: 'recursion', label: 'Recursion'},
  {id: 'unrolling', label: '@unroll'},
];

export const papers = [
  {id: 'bjorner-2019', label: 'Bjørner et al. 2019', title: 'Programming Z3', url: 'https://z3prover.github.io/papers/programmingz3.html'},
  {id: 'bohnenkamp-2003', label: 'Bohnenkamp et al. 2003', title: 'Cost-Optimization of the IPv4 Zeroconf Protocol', url: 'https://doi.org/10.1109/DSN.2003.1209963'},
  {id: 'dargenio-2001', label: 'D’Argenio et al. 2001', title: 'Reachability Analysis of Probabilistic Systems by Successive Refinements', url: 'https://doi.org/10.1007/3-540-44804-7_3'},
  {id: 'helmink-1994', label: 'Helmink et al. 1994', title: 'Proof-Checking a Data Link Protocol', url: 'https://doi.org/10.1007/3-540-58085-9_75'},
  {id: 'kaminski-2016', label: 'Kaminski et al. 2016', title: 'Weakest Precondition Reasoning for Expected Run-Times of Probabilistic Programs', url: 'https://users.dcc.uchile.cl/~folmedo/pubs/2016.ESOP.pdf'},
  {id: 'kaminski-2018', label: 'Kaminski et al. 2018', title: 'Weakest Precondition Reasoning for Expected Runtimes of Randomized Algorithms', url: 'https://doi.org/10.1145/3208102'},
  {id: 'kushilevitz-rabin-1992', label: 'Kushilevitz and Rabin 1992', title: 'Randomized Mutual Exclusion Algorithms Revisited', url: 'https://doi.org/10.1145/135419.135468'},
  {id: 'kwiatkowska-2006', label: 'Kwiatkowska et al. 2006', title: 'Performance Analysis of Probabilistic Timed Automata Using Digital Clocks', url: 'https://www.prismmodelchecker.org/papers/fmsd06.pdf'},
  {id: 'schroer-2023', label: 'Schröer et al. 2023', title: 'A Deductive Verification Infrastructure for Probabilistic Programs', url: 'https://arxiv.org/abs/2309.07781'},
  {id: 'schroer-cav-2026', label: 'Schröer et al. 2026', title: 'Caesar: A Deductive Verifier for Probabilistic Programs', url: 'https://doi.org/10.1007/978-3-032-32537-2_27'},
  {id: 'schroer-2026', label: 'Schröer and Katoen 2026', title: 'Highly Incremental: A Simple Programmatic Approach for Many Objectives', url: 'https://arxiv.org/abs/2603.02405'},
  {id: 'batz-2025', label: 'Batz et al. 2025', title: 'Foundations for Deductive Verification of Continuous Probabilistic Programs: From Lebesgue to Riemann and Back', url: 'https://doi.org/10.1145/3720429'},
  {id: 'morris-1978', label: 'Morris 1978', title: 'Counting Large Numbers of Events in Small Registers', url: 'https://doi.org/10.1145/359619.359627'},
  {id: 'vitter-1985', label: 'Vitter 1985', title: 'Random Sampling with a Reservoir', url: 'https://doi.org/10.1145/3147.3165'},
  {id: 'lumbroso-2013', label: 'Lumbroso 2013', title: 'Optimal Discrete Uniform Generation from Coin Flips, and Applications', url: 'https://arxiv.org/abs/1304.1916'},
  {id: 'batz-2021', label: 'Batz et al. 2021', title: 'Latticed k-Induction with an Application to Probabilistic Programs', url: 'https://arxiv.org/abs/2105.14100'},
  {id: 'mciver-2018', label: 'McIver et al. 2018', title: 'A New Proof Rule for Almost-Sure Termination', url: 'https://arxiv.org/abs/1711.03588'},
  {id: 'hurd-2004', label: 'Hurd et al. 2004', title: 'Probabilistic Guarded Commands Mechanized in HOL', url: 'https://doi.org/10.1016/j.entcs.2004.01.021'},
  {id: 'hark-2020', label: 'Hark et al. 2020', title: 'Aiming Low Is Harder: Induction for Lower Bounds in Probabilistic Program Verification', url: 'https://arxiv.org/abs/1904.01117'},
  {id: 'paz-2014', label: 'Paz and Yechiali 2014', title: 'An M/M/1 Queue in Random Environment with Disasters', url: 'https://doi.org/10.1142/S021759591450016X'},
  {id: 'olmedo-2018', label: 'Olmedo et al. 2018', title: 'Conditioning in Probabilistic Programming', url: 'https://doi.org/10.1145/3156018'},
  {id: 'van-jaarsveld-2025', label: 'van Jaarsveld 2025', title: 'Practical Probabilistic Program Verification using Caesar', url: 'https://purl.utwente.nl/essays/106318'},
];

function variant(id, label, sourcePath, techniques, args = [], outcome = 'proof', topics = []) {
  return {id, label, sourcePath, techniques, args, outcome, topics};
}

const computation = ['--function-encoding', 'fuel-param-computation'];
const fuel = ['--function-encoding', 'fuel-param'];
const eMatching = ['--quantifier-instantiation', 'e-matching'];

// Within each group, examples appear in this order.
export const examples = [
  {
    id: 'geometric-loop',
    group: 'random-walks',
    papers: ["batz-2021", "hark-2020"],
    category: 'probabilistic',
    title: 'Geometric Loop',
    summary:
      "Count tails until a fair coin first shows heads. " +
      "Prove that the expected number of tails is one, and refute a proposed upper bound of $0.99$.",
    topics: ['expectation'],
    detailSlug: 'geometric-loop',
    variants: [
      variant('invariant', 'Expected number of tails: upper bound by Park induction', 'tests/loop-rules/induction/geometric.heyvl', ['invariants']),
      variant('k-induction', 'Expected number of tails: upper bound by 2-induction', 'tests/loop-rules/k_induction/geo1.heyvl', ['k-induction']),
      variant('optional-stopping', 'Expected number of tails: lower bound by optional stopping', 'tests/loop-rules/ost2019/annotated.heyvl', ['optional-stopping']),
      variant('refutation', 'Refuting the upper bound of 0.99 tails', 'tests/loop-rules/bmc/refute-geo2_bmc.heyvl', ['unrolling'], ['--slice-error-first'], 'refutation'),
      variant('recursive', 'Expected number of tails: recursive specification', 'tests/case-studies/geo-recursive.heyvl', ['recursion']),
    ],
  },
  {
    id: 'coupon-collector',
    group: 'sampling',
    papers: ['kaminski-2016', 'kaminski-2018', 'schroer-2023'],
    category: 'probabilistic',
    title: 'Coupon Collector',
    summary:
      "Draw independently from $N$ equally likely coupons until the collection is complete. " +
      "Caesar bounds the expected number of draws by $N \\cdot H_N$, where $H_N$ is the $N$-th harmonic number.",
    topics: ['runtime', 'expectation', 'functions'],
    detailSlug: 'coupon-collector',
    variants: [
      variant('main', 'Expected draws: simplified sampling', 'tests/case-studies/coupon-collector.heyvl', ['invariants'], [...fuel, ...eMatching]),
      variant('uniform', 'Expected draws: explicit uniform sampling', 'tests/case-studies/coupon-collector-uniform.heyvl', ['invariants'], [...fuel, ...eMatching]),
    ],
  },
  {
    id: 'reservoir-sampling',
    group: 'sampling',
    papers: ['vitter-1985'],
    category: 'probabilistic',
    title: 'Reservoir Sampling',
    summary:
      "Keep one uniformly chosen item from a stream without storing the whole stream. " +
      "Caesar proves matching probability bounds and termination, establishing a selection probability of $1/n$ for every position.",
    topics: ['sampling', 'probability', 'termination'],
    detailSlug: 'reservoir-sampling',
    variants: [variant('main', 'Uniform selection: upper and lower bounds and termination', 'tests/case-studies/reservoir-sampling.heyvl', ['invariants', 'ast'], [], 'proof', ['ast'])],
  },
  {
    id: 'fast-dice-roller',
    group: 'sampling',
    papers: ['lumbroso-2013', 'mciver-2018'],
    category: 'probabilistic',
    title: 'Fast Dice Roller',
    summary:
      "Compare rejection sampling with Fast Dice Roller, which reuses the randomness in rejected values. " +
      "The fast sampler's proof uses one invariant for matching bounds on each result.",
    topics: ['sampling', 'probability', 'functions', 'termination'],
    detailSlug: 'fast-dice-roller',
    variants: [
      variant('slow', 'Slow Dice Roller: probability bounds and expected bit cost', 'tests/case-studies/slow-dice-roller.heyvl', ['invariants', 'ast'], ['--timeout', '30', '--max-fuel', '4', ...eMatching, '--werr'], 'proof', ['ast', 'expectation']),
      variant('power-of-two', 'Binary sampler: matching probability bounds and termination', 'tests/case-studies/power-of-two-sampling.heyvl', ['invariants', 'ast'], ['--timeout', '20', '--max-fuel', '4', ...eMatching, '--werr'], 'proof', ['ast']),
      variant('main', 'Arbitrary ranges: matching probability bounds and termination', 'tests/case-studies/fast-dice-roller.heyvl', ['invariants', 'ast'], ['--timeout', '30', '--max-fuel', '4', ...eMatching, '--werr'], 'proof', ['ast']),
    ],
  },
  {
    id: 'morris-counting',
    group: 'sampling',
    papers: ['morris-1978'],
    category: 'probabilistic',
    title: 'Morris Approximate Counting',
    summary:
      "Count events by incrementing a small counter with a probability that decreases as it grows. " +
      "Caesar verifies that the expected estimate $2^c - 1$ is at most the number of events.",
    topics: ['expectation', 'axioms', 'functions'],
    detailSlug: 'morris-counting',
    variants: [variant('main', 'Upper bound on the expected count estimate', 'tests/case-studies/morris-counting.heyvl', ['invariants'])],
  },
  {
    id: 'retry-moments',
    group: 'rewards',
    papers: ['schroer-2026'],
    category: 'probabilistic',
    title: 'Retry Latency and Higher Moments',
    summary:
      "Compare database retries with a caching alternative that has the same mean latency. " +
      "Caesar bounds their second moments using incremental rewards, supporting a comparison of latency variance.",
    topics: ['runtime', 'expectation', 'moments'],
    detailSlug: 'retry-moments',
    variants: [variant('main', 'Upper bounds on mean latency and second moments', 'tests/case-studies/retry-moments.heyvl', ['invariants'])],
  },
  {
    id: 'runtime-composition',
    group: 'rewards',
    papers: ['kaminski-2016'],
    category: 'probabilistic',
    title: 'Finite Expected Runtime Does Not Compose',
    summary:
      "A randomized generator and a deterministic countdown each have finite expected runtime for every fixed input. " +
      "Their composition terminates almost surely but has infinite expected runtime.",
    topics: ['runtime', 'expectation', 'termination'],
    detailSlug: 'runtime-composition',
    variants: [variant('main', 'Finite component runtimes and arbitrary lower bounds on composed runtime', 'tests/case-studies/ert-composition.heyvl', ['invariants', 'omega-invariants'], ['--werr', '--quantifier-instantiation', 'mbqi', '--timeout', '10'])],
  },
  {
    id: 'tortoise-hare',
    group: 'sampling',
    papers: ['batz-2025'],
    category: 'probabilistic',
    title: 'Continuous Tortoise–Hare Race',
    summary:
      "A hare chooses continuous random jumps while a tortoise advances one step per round. " +
      "Caesar checks an upper bound on the expected final round count through a Riemann approximation of continuous sampling.",
    topics: ['continuous', 'expectation'],
    detailSlug: 'tortoise-hare',
    variants: [variant('main', 'Upper bound through eight Riemann intervals', 'tests/case-studies/tortoise-hare.heyvl', ['invariants'])],
  },
  {
    id: 'conditioning',
    group: 'sampling',
    papers: ['paz-2014', 'olmedo-2018'],
    category: 'probabilistic',
    title: 'Conditioning on Queue Completion',
    summary:
      "A queue receives new jobs while a server processes existing ones and may fail. " +
      "Conditioned on emptying before failure, Caesar bounds the expected number of rounds by $5n/3$ for every initial queue size $n$, without bounding the queue's growth.",
    topics: ['conditioning', 'expectation', 'probability', 'termination'],
    detailSlug: 'conditioning',
    variants: [variant('main', 'Conditional expected rounds and observation probability', 'tests/case-studies/conditioning.heyvl', ['invariants'], ['--max-fuel', '4', ...eMatching])],
  },
  {
    id: 'die-sampling',
    group: 'sampling',
    papers: ['schroer-2023'],
    category: 'probabilistic',
    title: 'Die Sampling with Conditioning',
    summary:
      "Simulate a six-sided die with three fair coin flips, conditioning on a result at most six. " +
      "Caesar verifies that the expected die result under this condition is at most $2.625 / 0.75 = 3.5$.",
    topics: ['conditioning', 'probability', 'expectation'],
    variants: [variant('main', 'Conditional expected die result', 'tests/loopfree-prob/six-sided-die.heyvl', ['loop-free'])],
  },
  {
    id: 'noisy-or',
    group: 'sampling',
    category: 'probabilistic',
    title: 'Noisy-OR Bayesian Network',
    summary:
      "Sample a Boolean Bayesian network whose nodes combine causes by disjunction. " +
      "Caesar verifies lower bounds on the probabilities that the output is true or false.",
    topics: ['probability'],
    variants: [variant('main', 'Output-probability bounds', 'tests/loopfree-prob/noisy_or.heyvl', ['loop-free'])],
  },
  {
    id: 'one-sided-random-walks',
    group: 'random-walks',
    papers: ['mciver-2018', 'schroer-2023'],
    category: 'probabilistic',
    title: 'One-Sided Random Walks',
    summary:
      "Move toward a target with random pauses or steps of one or two. " +
      "Compare almost-sure termination, finite expected numbers of coin flips, and numerical bounds on those expectations.",
    topics: ['termination', 'runtime', 'probability'],
    detailSlug: 'one-sided-random-walks',
    variants: [
      variant('ast', 'Countdown: almost-sure termination', 'tests/loop-rules/ast2018/negative_binomial.heyvl', ['ast'], [], 'proof', ['ast']),
      variant('past', 'Countdown: finite expected number of coin flips', 'tests/loop-rules/past2013/annotated.heyvl', ['past'], [], 'proof', ['ast', 'past']),
      variant('expected-cost', 'Counting up: expected number of coin flips', 'tests/loop-rules/induction/sprdwalk.heyvl', ['invariants'], [], 'proof', ['ast', 'past']),
      variant('two-step', 'One- or two-step countdown: expected number of coin flips', 'tests/loop-rules/induction/linear01.heyvl', ['invariants'], [], 'proof', ['ast', 'past']),
    ],
  },
  {
    id: 'two-sided-random-walks',
    group: 'random-walks',
    papers: ["mciver-2018"],
    category: 'probabilistic',
    title: 'Two-Sided Random Walks',
    summary:
      "Move toward or away from a target, with positive drift, adversarial choice, or parity-dependent steps. " +
      "Caesar bounds the expected number of flips for positive drift and proves almost-sure termination for the adversarial and parity-dependent walks.",
    topics: ['termination', 'runtime', 'probability'],
    detailSlug: 'two-sided-random-walks',
    variants: [
      variant('positive-drift', 'Positive drift: expected number of coin flips', 'tests/loop-rules/induction/rdwalk.heyvl', ['invariants']),
      variant('main', 'Almost-sure termination under adversarial choice', 'tests/loop-rules/ast2018/demonically_fair.heyvl', ['ast'], [], 'proof', ['ast']),
      variant('parity', 'Parity-dependent steps: almost-sure termination', 'tests/loop-rules/ast2018/ast-flipflop.heyvl', ['ast'], [], 'proof', ['ast']),
    ],
  },
  {
    id: 'escaping-spline',
    group: 'random-walks',
    papers: ["mciver-2018"],
    category: 'probabilistic',
    title: 'Escaping Spline',
    summary:
      "Move to zero with probability $1/(x+1)$, otherwise increase the current state. " +
      "Caesar verifies almost-sure termination even though the probability of reaching zero in one iteration decreases as the state grows.",
    topics: ['termination', 'probability'],
    detailSlug: 'escaping-spline',
    variants: [variant('main', 'Almost-sure termination', 'tests/loop-rules/ast2018/escaping_spline.heyvl', ['ast'], [], 'proof', ['ast'])],
  },
  {
    id: 'zeroconf',
    group: 'protocols',
    papers: ['bohnenkamp-2003', 'kwiatkowska-2006', 'schroer-2023'],
    category: 'probabilistic',
    title: 'Zeroconf Address Allocation',
    summary:
      "Probe one candidate network address for a conflict. " +
      "Caesar verifies an upper bound on the probability of avoiding an undetected collision using recursive specifications.",
    topics: ['protocols', 'probability', 'axioms', 'functions'],
    detailSlug: 'zeroconf',
    variants: [variant('main', 'Upper bound on avoiding an undetected collision', 'tests/case-studies/zeroconf.heyvl', ['recursion'], eMatching)],
  },
  {
    id: 'bounded-retransmission',
    group: 'protocols',
    papers: ['helmink-1994', 'dargenio-2001', 'van-jaarsveld-2025', 'schroer-2023', 'schroer-cav-2026'],
    category: 'probabilistic',
    title: 'Bounded Retransmission Protocol',
    summary:
      "Send packets over a lossy channel, retrying each packet up to a fixed limit. " +
      "Caesar bounds success and failure probabilities and the expected numbers of attempts, failed attempts, and sent packets.",
    topics: ['protocols', 'probability', 'expectation', 'runtime', 'axioms', 'functions'],
    detailSlug: 'bounded-retransmission',
    variants: [
      variant('combined', 'Complete message: failure probability and failed attempts', 'tests/case-studies/brp/combined.heyvl', ['invariants'], eMatching),
      variant('success', 'Lower bound on success probability', 'tests/case-studies/brp/success.heyvl', ['invariants'], eMatching),
      variant('termination', 'Transmission and packet attempts: finite and geometric bounds', 'tests/case-studies/brp/termination.heyvl', ['invariants']),
      variant('failed', 'Single-packet failures and abstract packet costs', 'tests/case-studies/brp/failed.heyvl', ['invariants']),
      variant('sent', 'Expected number of sent packets', 'tests/case-studies/brp/sent.heyvl', ['invariants']),
    ],
  },
  {
    id: 'rabin-mutual-exclusion',
    group: 'protocols',
    papers: ['kushilevitz-rabin-1992', 'hurd-2004', 'schroer-2023'],
    category: 'probabilistic',
    title: 'Rabin’s Mutual-Exclusion Algorithm',
    summary:
      "Contenders repeatedly flip coins to decide whether to withdraw, aiming to leave one survivor. " +
      "For multiple contenders, Caesar proves that the probability of ending with no survivors is at most $1/3$.",
    topics: ['protocols', 'probability', 'functions'],
    detailSlug: 'rabin-mutual-exclusion',
    variants: [
      variant('nested', 'Upper bound on the probability of no survivors', 'tests/loop-rules/induction/rabin_hurd2004.heyvl', ['invariants'], eMatching),
    ],
  },
  {
    id: 'selection-sort',
    group: 'data-structures',
    category: 'boolean',
    title: 'Selection Sort',
    summary:
      "Sort an integer list by repeatedly selecting the smallest remaining element. " +
      "Caesar uses Boolean loop invariants to prove that the result is nondecreasing and has the original length on termination.",
    topics: ['lists'],
    detailSlug: 'selection-sort',
    variants: [variant('main', 'Sortedness and length through loop invariants', 'tests/boolean/algorithms/selection_sort.heyvl', ['invariants'])],
  },
  {
    id: 'symbolic-lists',
    group: 'data-structures',
    category: 'boolean',
    title: 'Symbolic List Operations',
    summary:
      "Update, append to, and read the last element of a symbolic linked list. " +
      "Caesar uses recursive specifications to prove that the operations return the specified lengths and elements on termination.",
    topics: ['lists', 'axioms', 'functions'],
    variants: [variant('main', 'Updating and extending lists', 'tests/boolean/algorithms/list_operations.heyvl', ['recursion'])],
  },
  {
    id: 'left-padding',
    group: 'data-structures',
    category: 'boolean',
    title: 'Left Padding',
    summary:
      "Prepend a chosen value until a list reaches the requested width. " +
      "Caesar verifies the output length, padding values, and preservation of the original list as a suffix.",
    topics: ['lists', 'axioms', 'functions'],
    variants: [variant('main', 'Length, padding, and the original suffix', 'tests/boolean/algorithms/left_pad.heyvl', ['recursion'])],
  },
  {
    id: 'lossy-list',
    group: 'data-structures',
    category: 'probabilistic',
    title: 'Lossy List Traversal',
    summary:
      "Traverse a list while each step has a chance of a memory fault. " +
      "For a list of length $n$, Caesar verifies a success probability of at least $2^{-n}$.",
    topics: ['lists', 'probability', 'axioms', 'functions'],
    variants: [variant('main', 'Success probability for any list length', 'tests/loop-rules/induction/chain/lossy_list.heyvl', ['invariants'], eMatching)],
  },
  {
    id: 'binary-search-trees',
    group: 'data-structures',
    papers: ['bjorner-2019'],
    category: 'boolean',
    title: 'Binary Search Trees',
    summary:
      "Look up and insert values, and find the minimum and maximum in a binary search tree. " +
      "Under the domain axioms, Caesar proves that queries return the specified values and insertion preserves tree ordering on termination.",
    topics: ['trees', 'axioms', 'functions'],
    detailSlug: 'binary-search-trees',
    variants: [variant('main', 'Membership, extrema, and insertion', 'tests/boolean/algorithms/binary_search_trees.heyvl', ['recursion'], computation)],
  },
];

export function getExample(id) {
  const example = examples.find((entry) => entry.id === id);
  if (!example) throw new Error(`Unknown example: ${id}`);
  return example;
}

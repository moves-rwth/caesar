import React from 'react';
import Link from '@docusaurus/Link';
import HomepageExample from '@site/src/components/HomepageExample';
import styles from './styles.module.css';

function ProbabilisticPrograms() {
  return (
    <section className={styles.motivation} aria-labelledby="programs-title">
      <div className={`container ${styles.sectionHeading}`}>
        <h2 id="programs-title">Probabilistic Programs</h2>
        <p>
          Probabilistic programs make random choices that affect their results and control flow.
          They model randomized algorithms and protocols, such as communication over an unreliable channel.
          Verification can establish bounds on the probability of transmission failure, the expected number of retries, or the resources consumed.
        </p>
      </div>
    </section>
  );
}

function Motivation() {
  return (
    <section className={styles.motivation} aria-labelledby="motivation-title">
      <div className={`container ${styles.sectionHeading}`}>
        <h2 id="motivation-title">Reasoning About Unbounded Executions</h2>
        <div>
          <p>
            The loop above has no finite worst-case iteration bound, although its expected number of iterations is at most 2.
            Proving this requires reasoning about the whole distribution of execution lengths, including arbitrarily long runs.
          </p>
          <p>
            Termination itself has several meanings.
            A program can terminate with probability 1 and still have infinite expected runtime, as in a <Link to="https://arxiv.org/pdf/1711.03588#page=2">symmetric random walk that stops at zero</Link>.
            Thus, <Link to="/docs/proof-rules/ast"><em>almost-sure termination</em></Link> and <Link to="/docs/proof-rules/past">finite expected runtime</Link> require different proof arguments.
          </p>
          <p>
            Caesar checks these arguments using invariants, martingale-based rules, and symbolic verification.
            Bounds can depend on program inputs, so a single proof can cover all input values satisfying its assumptions.
          </p>
        </div>
      </div>
    </section>
  );
}

function Infrastructure() {
  return (
    <section className={styles.section} aria-labelledby="infrastructure-title">
      <div className="container">
        <div className={styles.sectionHeading}>
          <h2 id="infrastructure-title">Verification Infrastructure</h2>
          <div>
            <p>
              Caesar’s intermediate verification language, HeyVL, expresses probabilistic programs together with quantitative specifications and proof rules.
              New proof rules can be encoded in HeyVL without changing the verifier.
            </p>
            <Link className={`button button--outline button--primary ${styles.paperOverview}`} to="https://link.springer.com/content/pdf/10.1007/978-3-032-32537-2_27.pdf?pdf=inline%20link">Read the CAV 2026 tool paper ↗</Link>
          </div>
        </div>
        <figure className={styles.architecture}>
          <div className={styles.architectureBody}>
            <div className={styles.inputs}>
              <div className={styles.inputGroup}>
                <h3>Programs</h3>
                <ul>
                  <li><Link to="/docs/stdlib/distributions">Sampling from discrete distributions</Link></li>
                  <li><Link to="/docs/proof-rules">Unbounded <code>while</code> loops</Link></li>
                  <li><Link to="/docs/heyvl/procs#calling-procedures">Procedure calls and recursion</Link></li>
                  <li><Link to="/docs/heyvl/statements#nondeterministic-choices"><em>Angelic</em> and <em>demonic</em> nondeterminism</Link></li>
                  <li><Link to="/docs/stdlib">Booleans, integers, reals, and lists</Link></li>
                </ul>
              </div>
              <div className={styles.inputGroup}>
                <h3>Specifications</h3>
                <ul>
                  <li><Link to="/docs/heyvl/procs">Lower and upper bounds on expected values</Link></li>
                  <li><Link to="/docs/heyvl/procs">Probability bounds</Link></li>
                  <li><Link to="/docs/heyvl/statements#reward-and-weigh">Expected runtime and resource consumption</Link></li>
                  <li><Link to="/docs/proof-rules/ast">Almost-sure termination</Link></li>
                  <li><Link to="/blog/2026/03/04/highly-incremental#example-with-caesar-second-moment-of-runtime">Higher moments</Link></li>
                  <li><Link to="/blog/2026/03/04/highly-incremental#programmatic-reward-transformations">Tail probabilities</Link></li>
                </ul>
              </div>
              <div className={styles.inputGroup}>
                <h3>Proof Rules</h3>
                <ul>
                  <li><Link to="/docs/proof-rules/induction">Induction and <i>k</i>-induction</Link></li>
                  <li><Link to="/docs/proof-rules/unrolling">Loop unrolling</Link> and <Link to="/docs/proof-rules/omega-invariants">ω-invariants</Link></li>
                  <li><Link to="/docs/proof-rules/ost">Optional stopping</Link></li>
                  <li><Link to="/docs/proof-rules/ast">Almost-sure termination</Link></li>
                  <li><Link to="/docs/proof-rules/past">Positive almost-sure termination</Link></li>
                </ul>
              </div>
            </div>
            <div className={styles.merge} aria-hidden="true"><span /><span /><span /></div>
            <div className={styles.heyvl}>
              <div>
                <Link to="/docs/heyvl">HeyVL</Link>
                <span>Quantitative intermediate verification language</span>
              </div>
              <p>
                <em>Quantitative verification statements</em>, such as <code>assert</code> and <code>assume</code>, encode proof rules as programs.
                HeyVL supports user-defined <Link to="/docs/heyvl/domains#definitional-functions">functions</Link> and <Link to="/docs/heyvl/domains#defining-types-with-domains">types</Link>.
              </p>
            </div>
            <div className={styles.fork} aria-hidden="true" />
            <div className={styles.backends}>
              <div className={styles.logicBackend}>
                <h3><Link to="/docs/heyvl/expressions">HeyLo</Link></h3>
                <span className={styles.backendLabel}>Deductive verification</span>
                <p className={styles.backendScope}>Infinite state spaces and symbolic inputs</p>
                <p className={styles.backendDescription}>
                  Proof annotations let Caesar establish bounds without enumerating program states.
                  It generates <em>verification conditions</em> in HeyLo, its <em>real-valued assertion logic</em>.
                  HeyLo formulas map program states to non-negative reals or infinity.
                </p>
                <p className={styles.backendDescription}>
                  Caesar simplifies verification conditions and eliminates quantitative quantifiers where possible before sending them to <Link to="https://github.com/Z3Prover/z3">Z3</Link>.{' '}
                  It can also reason about <Link to="/docs/caesar/debugging#function-encodings-and-limited-functions">recursive functions</Link>.
                </p>
                <div className={styles.backendRoute}>Verification conditions <span aria-hidden="true">→</span> <Link to="https://github.com/Z3Prover/z3">Z3</Link></div>
              </div>
              <div>
                <h3><Link to="https://jani-spec.org/">JANI</Link> / <Link to="https://www.stormchecker.org/">Storm</Link></h3>
                <Link to="/docs/model-checking" className={styles.backendLabel}>An alternative model-checking backend</Link>
                <p className={styles.backendScope}>Automatic analysis of finite-state models</p>
                <p className={styles.backendDescription}>
                  For programs with finitely many states, <Link to="https://www.stormchecker.org/">Storm</Link> can calculate expected values without user-provided invariants.
                  Caesar exports a <Link to="/docs/model-checking#supported-programs">subset of HeyVL</Link> to <Link to="https://jani-spec.org/">JANI</Link>, a format for probabilistic models that Storm can read.
                </p>
                <p className={styles.backendDescription}>Infinite-state models can also be <Link to="/docs/model-checking#parametric-and-infinite-state-models">approximated by exploring a limited number of states</Link>.</p>
                <div className={styles.backendRoute}>Executable subset <span aria-hidden="true">→</span> <Link to="https://jani-spec.org/">JANI</Link> <span aria-hidden="true">→</span> <Link to="https://www.stormchecker.org/">Storm</Link></div>
              </div>
            </div>
          </div>
        </figure>
        <div className={styles.sectionLinks}>
          <Link to="/docs/heyvl">HeyVL reference →</Link>
          <Link to="/docs/proof-rules">Proof-rule reference →</Link>
        </div>
      </div>
    </section>
  );
}

function ToolSupport() {
  return (
    <section className={styles.section} aria-labelledby="tools-title">
      <div className={`container ${styles.tools}`}>
        <div>
          <h2 id="tools-title">Verify in VS Code</h2>
          <p>
            The Caesar extension verifies HeyVL programs directly in the editor.
            It also installs and updates Caesar for you.
          </p>
          <ul className={styles.editorFeatures}>
            <li>
              <h3>Verification on Save</h3>
              <p>See verification results beside the code, with errors and warnings at the relevant statements.</p>
            </li>
            <li>
              <h3><Link to="/blog/2024/05/20/caesar-2-0#caesar20-vscode-extension">Inline Explanations</Link></h3>
              <p>Inspect the computed verification conditions to understand how Caesar reasons about your program.</p>
            </li>
            <li>
              <h3><Link to="/docs/caesar/slicing">Slicing Diagnostics</Link></h3>
              <p>Locate failing proof obligations and identify which statements are needed for verification.</p>
            </li>
            <li>
              <h3>HeyVL Editing Support</h3>
              <p>Use syntax highlighting, code snippets, and reference hovers for language constructs and proof annotations.</p>
            </li>
          </ul>
          <div className={styles.toolLinks}>
            <Link className="button button--primary" to="https://marketplace.visualstudio.com/items?itemName=rwth-moves.caesar">Install the VS Code extension ↗</Link>
            <Link to="https://open-vsx.org/extension/rwth-moves/caesar">Open VSX for VSCodium ↗</Link>
            <Link to="/docs/caesar/vscode-and-lsp">Extension documentation →</Link>
          </div>
        </div>
        <figure className={styles.editor}>
          <a href="/img/slicing-demo.png" aria-label="View the VS Code diagnostic screenshot at full size">
            <img src="/img/slicing-demo.png" alt="Caesar in VS Code, showing the diagnostic “invariant might not be inductive” at a loop annotation." width="994" height="818" loading="lazy" />
          </a>
          <figcaption>
            Caesar points to a loop invariant that may not be inductive.
          </figcaption>
        </figure>
      </div>
    </section>
  );
}

const publications = [
  {
    title: 'Securing the Foundations of an Intermediate Language for Probabilistic Program Verification',
    venue: 'ITP 2026',
    description: 'Mechanized foundations in Lean for the correctness of HeyVL encodings and probabilistic verification techniques.',
    url: '/blog/2026/07/22/itp26-securing-foundations',
  },
  {
    title: 'Caesar: A Deductive Verifier for Probabilistic Programs',
    venue: 'CAV 2026',
    description: 'The Caesar tool paper, covering its verification workflow, editor support, and backends.',
    url: '/blog/2026/04/20/caesar-tool-paper-cav',
  },
  {
    title: 'Highly Incremental: A Simple Programmatic Approach for Many Objectives',
    venue: 'FM 2026',
    description: 'Reward transformations for verifying higher moments, tail probabilities, and other quantitative objectives.',
    url: '/blog/2026/03/04/highly-incremental',
  },
  {
    title: 'Verifying Almost-Sure Termination for Randomized Distributed Algorithms',
    venue: 'POPL 2026',
    description: 'Proof rules for almost-sure termination under weak fairness, used to verify randomized consensus protocols.',
    url: '/blog/2026/01/15/popl26-ast-distributed',
  },
  {
    title: 'Error Localization, Certificates, and Hints for Probabilistic Program Verification via Slicing',
    venue: 'ESOP 2026',
    description: 'The foundations of Caesar’s slicing diagnostics for locating errors and simplifying proofs.',
    url: '/blog/2025/12/23/esop26-slicing',
  },
  {
    title: 'Foundations for Deductive Verification of Continuous Probabilistic Programs: From Lebesgue to Riemann and Back',
    venue: 'OOPSLA 2025',
    description: 'HeyVL encodings of Riemann-sum approximations to verify expectation bounds for continuous distributions.',
    url: '/blog/2025/04/11/foundations-continuous',
  },
  {
    title: 'A Game-Based Semantics for the Probabilistic Intermediate Verification Language HeyVL',
    venue: 'AISoLA 2024',
    description: 'An operational semantics for HeyVL based on refereed stochastic games.',
    url: '/blog/2024/12/31/game-based-semantics',
  },
  {
    title: 'A Deductive Verification Infrastructure for Probabilistic Programs',
    venue: 'OOPSLA 2023',
    description: 'The foundations of Caesar: HeyLo, HeyVL, and encodings of probabilistic proof rules.',
    url: '/blog/2023/09/28/oopsla23',
  },
];

function Institutions() {
  const institutions = [
    {name: 'RWTH Aachen University (MOVES)', logo: 'rwth-aachen', url: 'https://moves.rwth-aachen.de/'},
    {name: 'Saarland University (QUAVE)', logo: 'saarland', url: 'https://quave.cs.uni-saarland.de/'},
    {name: 'Technical University of Denmark (SSE)', logo: 'dtu', url: 'https://www.compute.dtu.dk/english/research/research-sections/software-systems-engineering'},
    {name: 'University College London (PPLV)', logo: 'ucl', url: 'http://pplv.cs.ucl.ac.uk/welcome/'},
    {name: 'University of Oldenburg (Theory of Correct Systems)', logo: 'oldenburg', url: 'https://uol.de/en/computingscience/groups/theorie-korrekter-systeme'},
  ];

  return (
    <section className={styles.institutions} aria-label="Universities contributing to Caesar">
      <div className={`container ${styles.institutionsInner}`}>
        <p>An open-source project from</p>
        <ul className={styles.institutionLogos}>
          {institutions.map(({name, logo, url}) => (
            <li key={logo}>
              <Link to={url}>
                <img src={`/img/institutions/${logo}.svg`} alt={name} width="168" height="56" />
              </Link>
            </li>
          ))}
        </ul>
      </div>
    </section>
  );
}

function News({latestPost}) {
  return (
    <section className={styles.section} aria-labelledby="news-title">
      <div className={`container ${styles.news}`}>
        <div>
          <h2 id="news-title">News</h2>
          <Link to="/blog">All posts →</Link>
        </div>
        {latestPost ? (
          <article>
            <time className={styles.venue} dateTime={latestPost.date}>
              {new Intl.DateTimeFormat('en-GB', {day: 'numeric', month: 'long', year: 'numeric', timeZone: 'UTC'}).format(new Date(latestPost.date))}
            </time>
            <h3><Link to={latestPost.permalink}>{latestPost.title}</Link></h3>
            <p>{latestPost.description}</p>
          </article>
        ) : <p>Release announcements and research updates are available on the <Link to="/blog">blog</Link>.</p>}
      </div>
    </section>
  );
}

function Research() {
  return (
    <section className={`${styles.section} ${styles.research}`} aria-labelledby="research-title">
      <div className="container">
        <div className={styles.sectionHeading}>
          <h2 id="research-title">Research and Publications</h2>
          <p>
            Peer-reviewed work on Caesar, its foundations, and applications.
          </p>
        </div>
        <ul className={styles.publications} aria-label="Peer-reviewed publications">
          {publications.map(({title, venue, description, url}) => (
            <li className={styles.publication} key={url}>
              <span className={styles.venue}>{venue}</span>
              <div>
                <h3><Link to={url}>{title}</Link></h3>
                <p>{description}</p>
              </div>
            </li>
          ))}
        </ul>
        <Link to="/docs/publications">Full references and theses →</Link>
      </div>
    </section>
  );
}

export default function HomepageFeatures({latestPost}) {
  return (
    <>
      <Institutions />
      <ProbabilisticPrograms />
      <Infrastructure />
      <HomepageExample />
      <Motivation />
      <ToolSupport />
      <News latestPost={latestPost} />
      <Research />
      <nav className={styles.projectLinks} aria-label="Caesar project links">
        <div className={`container ${styles.sectionLinks}`}>
          <Link to="https://github.com/moves-rwth/caesar">Source code ↗</Link>
          <Link to="/about">About Caesar →</Link>
        </div>
      </nav>
    </>
  );
}

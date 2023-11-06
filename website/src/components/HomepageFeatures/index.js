import React from 'react';
import clsx from 'clsx';
import Link from '@docusaurus/Link';
import styles from './styles.module.css';
import CodeBlock from '@theme/CodeBlock';

const FeatureList = [
  {
    title: 'Expectation-Based Reasoning',
    image: '/img/expected-value.svg',
    alt: 'E(X)',
    description: (
      <>
        Our approach is based on <i>weakest precondition-style reasoning</i>, generalized to probabilistic programs.
        We can reason about lower and upper bounds of expected values.
      </>
    ),
    invertDark: true,
  },
  {
    title: 'A Quantitative Intermediate Verification Language',
    image: '/img/heyvl.svg',
    alt: 'HeyVL Logo',
    description: (
      <>
        Caesar is built on our novel quantitative intermediate verification language <i>HeyVL</i>. <br />
        <Link to="/docs/publications#oopsla-23">See our OOPSLA '23 paper!</Link>
      </>
    ),
    invertDark: true,
  },
  {
    title: 'A Collaborative Effort',
    image: '/img/logos.svg',
    alt: 'i2 Logo',
    description: (
      <>
        Caesar is an open-source project from <Link to="https://moves.rwth-aachen.de/">RWTH Aachen University (MOVES group)</Link>, <Link to="https://quave.cs.uni-saarland.de/">Saarland University (QUAVE group)</Link>, <Link to="https://www.compute.dtu.dk/english/research/research-sections/software-systems-engineering">Denmark Technical University (SSE section)</Link>, and <Link to="http://pplv.cs.ucl.ac.uk/welcome/">University College London (PPLV group)</Link>.
      </>
    ),
    invertDark: false,
  },
];

function FeatureBox({ title, image, alt, description, invertDark }) {
  const svgClassName = invertDark ? `${styles.featureSvg} ${styles.invertDark}` : styles.featureSvg;

  // unfortunately, we can't embed an SVG image directly here using the Svg
  // class because that breaks the CSS filter that we use in dark mode to invert
  // the images in some browsers [1]. so we just use an img with a url.
  //
  // [1]: https://bugs.webkit.org/show_bug.cgi?id=104169

  return (
    <div className={clsx('col col--4', styles.featureBox)}>
      <div className="text--center">
        <img src={image} className={svgClassName} alt={alt} />
      </div>
      <div className="text--center padding-horiz--md">
        <h3>{title}</h3>
        <p>{description}</p>
      </div>
    </div>
  );
}

export default function HomepageFeatures() {
  return (
    <section className={styles.features}>
      <div className="container">
        <div className="row">
          {FeatureList.map((props, idx) => (
            <FeatureBox key={idx} {...props} />
          ))}
        </div>

        <hr style={{ marginTop: '2.5em', marginBottom: '2.5em' }} />

        <div className="row">
          <div className="col col--12">
            <h2>Features of HeyVL &mdash; Lossy List Traversal Example</h2>
            <p>Let's look at a program that traverses a list but has a chance of crashing during the traversal. We'll verify that the crash probability is at least 50% if the list has length 1.</p>
            <p>
              We explain more of the details <Link to="/docs/getting-started/verifying-heyvl">as part of our getting started guide</Link>.
            </p>
          </div>
        </div>

        <div className="row">
          <div className="col col--6">
            <h3>💥 <code>lossy_list</code> Procedure</h3>
            <p>This <Link to="docs/heyvl/procs">procedure</Link> is the entry point. It has one output, the resulting list <code>l</code>. In the body of <code>lossy_list</code>, we traverse the list by repeatedly removing the first element using <code>pop</code>. We model a 50% chance of crashing by a coin flip (<code>flip(0.5)</code>) leading to <code>assert [false]</code>.</p>
            <CodeBlock language='heyvl'>{`proc lossy_list(init_l: List) -> (l: List)
    pre [len(init_l) == 1] * 0.5  // quantitative specification!
    post [true]
{
    l = init_l
    @invariant(exp(0.5, len(l)))
    while len(l) > 0 {
        var prob_choice: Bool = flip(0.5) // coin flip
        if prob_choice {
            l = pop(l)     // next list element
        } else {
            assert [false] // crash
        }
    }
}
`}
            </CodeBlock>
          </div>

          <div className="col col--6">
            <h3>📐 Reading The Spec</h3>
            <p>
              Let's focus on the <i>quantitative specification</i> of <code>lossy_list</code>:
            </p>
            <CodeBlock language='heyvl'>{`pre [len(init_l) == 1] * 0.5
post [true]` }
            </CodeBlock>
            <p>
              The <code>post</code> says that we are looking at the expected value of <code>[true]</code> (i.e. 1) in the final states of the program. In other words, we are interested in the probability of running without an error.
            </p>
            <p>
              The <code>pre</code> specifies a lower bound to the probability of a run without crashing (expected value of the post <code>[true]</code>).
              It says that if the length of the list is 1, then the lower bound is <code>0.5</code> and otherwise <code>0</code>.
            </p>
            <p>To verify the spec, the <code>while</code> loop has an <code>@invariant</code> annotation with a <Link to="/docs/proof-rules/induction">probabilistic invariant</Link>.</p>

          </div>

        </div>

        <div className="row">

          <div className="col col--6">
            <h3>🌍 Axiomatizing Exponentials and Lists</h3>
            <p>Here is a strength of deductive verification: users can axomatize additional functions and data types that can be used for verification! We simply declare the <Link to="/docs/heyvl/domains">uninterpreted sort and functions</Link> with just the necessary axioms in HeyVL.</p>
            <CodeBlock language='heyvl'>{`domain Exponentials {
    func exp(base: UReal, exponent: UInt): EUReal

    axiom exp_base forall base: UReal. 
      exp(base, 0) == 1
    axiom exp_step forall base: UReal, exponent: UInt. 
      exp(base, exponent + 1) == base * exp(base, exponent)
}

domain List {
    func len(l: List): UInt
    func pop(l: List): List 

    axiom list_len forall l: List. 
      len(pop(l)) == len(l) - 1
}`}
            </CodeBlock>
          </div>

          <div className="col col--6">
            <h3>🏃 Running Caesar</h3>
            <p>
              After <Link to="https://www.rust-lang.org/tools/install">installing Rust</Link>, install the <code>caesar</code> binary (<Link to="/docs/getting-started">c.f. <i>Getting Started</i></Link>):
            </p>
            <CodeBlock language='bash'>{`git clone git@github.com:moves-rwth/caesar.git
cd caesar
cargo install --path . caesar
caesar tests/domains/lossy_list.heyvl` }
            </CodeBlock>
            <p>
              This will run Caesar on the example above (it is included in the Git repository).
              Caesar will print: <code>tests/domains/lossy_list.heyvl: Verified.</code>
            </p>
          </div>
        </div>


      </div>
    </section>
  );
}

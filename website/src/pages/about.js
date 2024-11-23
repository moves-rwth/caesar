import React from 'react';
import Layout from '@theme/Layout';
import Link from '@docusaurus/Link';

export default function About() {
  return (
    <Layout title="About Caesar" description="About Caesar">
      <div
        style={{
          display: 'grid',
          maxWidth: '800px',
          margin: '2em auto',
          textAlign: 'justify',
        }}>
        <h1>About Caesar</h1>
        <p>
          Caesar is a deductive verification infrastructure specifically designed for probabilistic programs.
          That means it is a tool to provide formal guarantees for programs that incorporate probabilistic behaviours, such as drawing random numbers or making random choices.
        </p>
        <p>
          Probabilistic programs can be found in randomized algorithms, communication protocols, machine learning models, and many other domains.
          When designing or analyzing such programs, many questions can be formulated with respect to some kind of <em>expected value</em>, such as the probability of reaching a certain state, the expected number of steps until a certain event occurs, or the expected value of some variable at the end of the program.
          We support the use of different proof rules, from areas such as martingale analysis or domain theory, thus enabling reasoning about programs with infinite state spaces and unbounded loops.
        </p>
        <p>
          Caesar aims to be a <em>verification infrastructure</em> that combines many different techniques to formally reason about such expected values.
          We want to provide a tool that automates the verification process as much as possible, while still allowing the user to guide the verification process and provide additional information when needed.
          This differs from <em>probabilistic model checkers</em> such as <Link to="https://www.stormchecker.org/">Storm</Link> or <Link to="https://www.prismmodelchecker.org/">PRISM</Link>, which are more "push-button" approaches that require less user interaction but struggle with e.g. infinite state spaces.
        </p>

        <p>
          Caesar is an open-source project from <Link to="https://moves.rwth-aachen.de/">RWTH Aachen University (MOVES group)</Link>, <Link to="https://quave.cs.uni-saarland.de/">Saarland University (QUAVE group)</Link>, <Link to="https://www.compute.dtu.dk/english/research/research-sections/software-systems-engineering">Denmark Technical University (SSE section)</Link>, and <Link to="http://pplv.cs.ucl.ac.uk/welcome/">University College London (PPLV group)</Link>.
          The <Link to="https://www.github.com/moves-rwth/caesar">source code is available on GitHub</Link>.
          The name "Caesar" comes from "veni, vidi, vc", where we let "vc" stand for "verification conditions".
        </p>

        <h2>Main Features</h2>
        <ul>
          <li>Verification of expected values in probabilistic programs</li>
          <li>Support for infinite state spaces, unbounded loops, and recursion</li>
          <li>Support for different proof rules, such as from martingale analysis or domain theory</li>
          <li>Integration with SMT solvers and probabilistic model checkers</li>
          <li>Program slicing for error localization and hints</li>
          <li>Integration with Visual Studio Code</li>
        </ul>

        <h2>Key Components</h2>

        <h3>The Quantitative Intermediate Verification Language <em>HeyVL</em></h3>
        <p>
          The architecture of Caesar is inspired by modern program verifiers that use an <em>intermediate verification language</em> (IVL) to encode a program, its specification, and proof rules into a common representation.
          Our <em>quantitative</em> IVL is called <em><Link to="/docs/heyvl/">HeyVL</Link></em>.
          HeyVL generalizes classical IVLs to the quantitative setting through <em>HeyLo</em>, our new quantitative logic developed for Caesar.
          The names come from <Link to="https://en.wikipedia.org/wiki/Heyting_algebra">Heyting algebras</Link>, which underlie the logic.
        </p>
        <p>
          In Caesar, HeyVL also has high-level constructs such as loops or procedure calls, but these are all encoded into a smaller core language.
          This core language and many encodings are described in our <Link to="docs/publications#oopsla-23">OOPSLA 2023 publication <em>"A Deductive Verification Infrastructure for Probabilistic Programs"</em></Link>.
        </p>

        <h3>Backends: SMT Solving and Probabilistic Model Checking</h3>
        <p>
          Caesar uses the <Link to="https://www.microsoft.com/en-us/research/project/z3-3/">Z3 SMT solver</Link> to reason about HeyVL programs.
          This allows Caesar to use symbolic reasoning to prove properties of probabilistic programs, enabling reasoning about infinite state spaces and unbounded loops.
          It is also possible to use other SMT solvers (<Link to="docs/caesar/">by emitting SMT-LIB</Link>).
        </p>
        <p>
          In addition, Caesar has <Link to="/docs/model-checking">a model checking backend</Link> that emits files in the <Link to="https://jani-spec.org/">JANI format</Link>, a JSON-based interchange format for probabilistic models.
          This is possible for an "executable" subset of HeyVL programs that can be translated into JANI models.
          The result can be fed into probabilistic model checkers such as <Link to="https://www.stormchecker.org/">Storm</Link>.
        </p>

        <h3>Slicing for Error Localization and Hints</h3>
        <p>
          Caesar includes a <Link to="docs/caesar/slicing"><em>program slicing</em> engine called <em>Brutus</em></Link> (get it?) that reduces HeyVL programs with respect to certain properties.
          Slicing is Caesar's theoretical and practical foundation for error localization and hints.
          For example, by removing assertions from the program, we can find out the remaining assertions which must cause a verification failure.
        </p>

        <h3>Visual Studio Code Integration</h3>
        <p>
          We value usability and user-friendliness highly and want to make Caesar as easy to use as possible.
          It is our belief that UX is a key factor in making formal verification succeed in practice.
          This is why we put a lot of effort into <Link to="/docs/caesar/vscode-and-lsp/">integrating Caesar with Visual Studio Code</Link> with our <Link to="https://marketplace.visualstudio.com/items?itemName=rwth-moves.caesar">Caesar for VSCode extension</Link>.
        </p>

        <h2>Disclaimer: (Un)Related Work</h2>
        <p>
          Caesar should not be confused with the set of tools in the <Link to="https://cadp.inria.fr/">CADP toolbox</Link> by INRIA, which includes tools like the CAESAR or CAESAR.ADT compilers, or the OPEN/CAESAR software architecture.
        </p>
      </div>
    </Layout>
  );
}
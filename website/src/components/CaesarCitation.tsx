import React, {useState} from 'react';
import Citation from './Citation';
import {references} from '../data/references';

const toolPaper = String.raw`@inproceedings{SchroerBatzEtAl2026Caesar,
  author = {Schr{\"o}er, Philipp and Batz, Kevin and Dural, Umut Yi{\u{g}}it and
            Haase, Darion and Kaminski, Benjamin Lucien and Katoen, Joost-Pieter and
            Matheja, Christoph},
  title = {{Caesar}: A Deductive Verifier for Probabilistic Programs},
  booktitle = {Computer Aided Verification},
  editor = {Darulova, Eva and Lin, Anthony W. and R{\"u}mmer, Philipp},
  series = {Lecture Notes in Computer Science},
  volume = {16684},
  pages = {565--582},
  publisher = {Springer},
  year = {2026},
  doi = {10.1007/978-3-032-32537-2_27},
}`;

const foundationsPaper = String.raw`@article{SchroerBatzEtAl2023HeyVL,
  author = {Schr{\"o}er, Philipp and Batz, Kevin and Kaminski, Benjamin Lucien and
            Katoen, Joost-Pieter and Matheja, Christoph},
  title = {A Deductive Verification Infrastructure for Probabilistic Programs},
  journal = {Proceedings of the {ACM} on Programming Languages},
  volume = {7},
  number = {OOPSLA2},
  pages = {2052--2082},
  year = {2023},
  doi = {10.1145/3622870},
}`;

function BibTeXActions({bibtex, conference, filename}: {bibtex: string; conference: string; filename: string}) {
  const [status, setStatus] = useState<'idle' | 'copied' | 'unavailable'>('idle');

  async function copy() {
    try {
      await navigator.clipboard.writeText(bibtex);
      setStatus('copied');
    } catch {
      setStatus('unavailable');
    }
  }

  return <>
    <button
      type="button"
      className="button button--secondary button--sm"
      aria-label={`Copy BibTeX for ${conference}`}
      onClick={copy}>
      Copy BibTeX
    </button>
    {' '}
    <a
      href={`data:application/x-bibtex;charset=utf-8,${encodeURIComponent(bibtex)}`}
      download={filename}
      aria-label={`Download .bib for ${conference}`}>
      Download .bib
    </a>
    <span role="status">
      {status === 'copied' && ' Copied to clipboard.'}
      {status === 'unavailable' && ' Clipboard unavailable. Use the download link.'}
    </span>
  </>;
}

export default function CaesarCitation() {
  return <ul className="clean-list margin-bottom--none">
    <li className="margin-bottom--md">
      <p className="margin-bottom--xs">For Caesar as a verifier, cite the CAV 2026 tool paper.</p>
      <Citation {...references.caesar2026} variant="full">
        <BibTeXActions bibtex={toolPaper} conference="CAV 2026" filename="caesar-cav-2026.bib" />
      </Citation>
    </li>
    <li>
      <p className="margin-bottom--xs">For HeyVL and the foundations of the verification infrastructure, cite the OOPSLA 2023 paper.</p>
      <Citation {...references.heyvl2023} venue="OOPSLA 2023" variant="full">
        <BibTeXActions bibtex={foundationsPaper} conference="OOPSLA 2023" filename="heyvl-oopsla-2023.bib" />
      </Citation>
    </li>
  </ul>;
}

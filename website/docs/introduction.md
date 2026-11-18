---
sidebar_position: 1
slug: /
---

# Introduction

```mdx-code-block
import Citation from '@site/src/components/Citation';
import {references as sources} from '@site/src/data/references';

export const references = {
  oopsla: sources.heyvl2023,
};
```

Hello and welcome!
This is the user documentation for [_Caesar_](https://github.com/moves-rwth/caesar), a deductive verification framework for probabilistic programs.

### Overview

After [installing Caesar](./getting-started/installation.mdx), continue with our [getting started guide](./getting-started/) to learn the basics of HeyVL and Caesar.

The language is documented in the [HeyVL language section](./heyvl/).
Built-in functions and types are documented in the [standard library section](./stdlib/).

In the [Caesar section](./caesar/), we have documentation for the Caesar tool, its command-line interface and the VSCode extension, as well as for our slicing algorithm.

### Our Theory Paper

Our OOPSLA 2023 paper introduces Caesar and its theory.

<Citation {...references.oopsla} variant="full" />

You can [find the preprint on arxiv](https://arxiv.org/abs/2309.07781).
More information on the [publications page](./publications.md).

### Contact Us!

**This is research software**, so it's not bug-free and there may be missing documentation in places.
Please open [start a discussion in our forum](https://github.com/moves-rwth/caesar/discussions), [open an issue](https://github.com/moves-rwth/caesar/issues), or send an email to [phisch@cs.rwth-aachen.de](mailto:phisch@cs.rwth-aachen.de) with questions or ideas.

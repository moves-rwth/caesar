# Caesar

_Caesar_ is a deductive verification platform for probabilistic programs.
It accepts input in a verification language called _HeyVL_.
Caesar generates so-called verification conditions of the HeyVL input program(s).
These verification conditions are in the form of logical formulas of a logic we call _HeyLo_.
If the verification conditions are valid, then we say the HeyVL program _verifies_.
If a counter-example is found, Caesar will reject the input program.

**This is research software** and we're still working on a nice user interface, documentation, and fixing bugs.
Do not hesitate to open an issue or send an email to phisch@cs.rwth-aachen.de with questions or ideas.
I am also happy to discuss anything via Zoom as well!

**The documentation is available at [www.caesarverifier.org](https://www.caesarverifier.org).**
Start at with the [introduction](https://www.caesarverifier.org), then walk through the [quick start guide](https://www.caesarverifier.org/quickstart.html).

We have an OOPSLA 2023 paper on Caesar and its theory: [_A Deductive Verification Infrastructure for Probabilistic Programs_](https://doi.org/10.1145/3622870).
You can [find the preprint on arxiv](https://arxiv.org/abs/2309.07781).

There is also a [development guide](https://www.caesarverifier.org/devguide.html) if you want to work on Caesar itself.

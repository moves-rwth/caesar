# Related Work on Deductive Verification

Although caesar is first quantitative deductive verification infrastructure, there has been lots of previous work in deductive verification.
In this section, we collect links to related work for inspiration and reference.

## The Viper Project

[Viper](https://www.pm.inf.ethz.ch/research/viper.html) is a verification infrastructure from ETH Zurich that supports _permissions_.
There are front-ends for Go ([Gobra](https://www.pm.inf.ethz.ch/research/gobra.html)), Python ([Nagini](https://www.pm.inf.ethz.ch/research/nagini.html)), and Rust ([Prusti](https://www.pm.inf.ethz.ch/research/prusti.html))
There are also projects that use it for the verification of OpenCL and Java ([VerCors](https://vercors.ewi.utwente.nl/)).

There is an extensive [tutorial for the Viper intermediate language](http://viper.ethz.ch/tutorial/) and a [collection of examples](http://viper.ethz.ch/examples/).

Viper in turn uses Boogie for verification condition generation.
The translation from Viper to Boogie is implemented in the [Carbon verifier](https://github.com/viperproject/carbon/).

## Boogie

[Boogie](https://github.com/boogie-org/boogie) is an intermediate verification language and verification condition generator.
Various verifiers are built on top, e.g. [VCC](https://github.com/microsoft/vcc) and [HAVOC](https://www.microsoft.com/en-us/research/project/havoc) for C, as well as the "verification-ready" languages [Dafny](https://github.com/dafny-lang/dafny), [Chalice](https://www.microsoft.com/en-us/research/project/chalice) and [Spec#](https://www.microsoft.com/en-us/research/project/spec).

There is also a [paper by Parthasarathy et al.](https://arxiv.org/abs/2105.14381)  on the formal verification of Boogie's verification condition generation.

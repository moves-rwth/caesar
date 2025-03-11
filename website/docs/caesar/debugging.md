---
sidebar_position: 1
---

# Debugging

Follow this guide if you are debugging verification with Caesar.


## SMT Theories and Incompleteness {#incompleteness}

[Expressions](../heyvl/expressions.md) are the main reason for *incompleteness* of Caesar, i.e. instances Caesar is unable to decide whether a given HeyVL program verifies or not.
Caesar's incompleteness comes from incompleteness of the underlying SMT solver which is used to prove or disprove verification.

At the moment, Caesar's translation of HeyVL verification problems is rather direct: most expressions are translated as one would intuitively expect.
If operators have a direct correspondence in [SMT-LIB](https://smt-lib.org/), then we translate directly to those.
Otherwise, usually only additional simple case distinctions are introduced.
We have some more explanations in [Section 5 of our paper on HeyVL](https://arxiv.org/pdf/2309.07781#page=23).

As a consequence, it is usually pretty simple to predict which [SMT-LIB theories](https://smt-lib.org/theories.shtml) will be used for the SMT query done by Caesar.
[Caesar supports Z3 probes](#z3-probes) to help you check in which theory your problem falls.
Also refer to the [Z3 documentation on arithmetic theories](https://microsoft.github.io/z3guide/docs/theories/Arithmetic/), since a lot of Caesar's reasoning will need arithmetic.

Here are some rules of thumb for (in-)completeness:
 * Linear integer and real arithmetic (QF_LRA, QF_LIRA) is decidable.
 * Nonlinear integer arithmetic (QF_NIA) is undecidable.
 * Nonlinear real arithmetic (QF_NRA) is decidable for algebraic reals.
 * Quantifiers usually introduce undecidability, although there are [a bunch of strategies and fragments in Z3 that allow decidability](https://microsoft.github.io/z3guide/docs/logic/Quantifiers#model-based-quantifier-instantiation).
   * In particular, restrictive [quantifier triggers](../heyvl/expressions.md#triggers) can help e-matching prove many instances.
 * HeyVL's [quantitative quantifiers](../heyvl/expressions.md#quantifiers) (`inf` and `sup`) currently have a very naive default encoding that is problematic for Z3.  If the quantitative quantifiers cannot be eliminated by Caesar's quantifier elimination (QE) procedure, then they are often a cause of nontermination of Caesar.
   * Quantitative quantifiers also come from the semantics of [`havoc` and `cohavoc`](../heyvl/statements.md#havoc). However, for e.g. the [induction-based proof rules](../proof-rules/induction.md), the HeyVL encodings fall into a fragment where Caesar's QE applies and the generated quantifiers are eliminated.
 * In practice, the SMT solver can often *prove* correctness, but it often has problems with *refutations* (i.e. providing counter-examples).


### Z3 Probes

Caesar supports the use of [Z3's *probes*](https://microsoft.github.io/z3guide/docs/strategies/probes/) to quickly help you determine performance-relevant properties about the SMT query, such as the presence of quantifiers or the theoretical complexity of the problem.

Run Caesar with the `--probe` flag to enable probes.
Caesar will print an output of the following form to standard error:

```
Probe results for test.heyvl::test:
Has quantifiers: false
Detected theories: NIRA
 - complexity: Undecidable
 - rejected theories: LRA, LIA, LIRA, NRA, NIA
Number of arithmetic constants: 1
Number of Boolean constants: 4
Number of bit-vector constants: 0
Number of constants: 1
Number of expressions: 71
```

The tool also tries to compute the complexity class of the problem to help you determine whether a problem is "easy".
Note that none of these metrics can be used to conclusively determine whether a problem can be verified or not.
For example, the presence of quantifiers means that the problem can not be associated with a decidable fragment, but often times the SMT solver can still solve the problem.
Similarly, the number of expressions or constants can sometimes be useful indicators to *compare* different problems, but on their own they are often not very informative.
In general, it is seldom useful to micro-optimize these metrics.

## Debugging Quantifier Instantiations with SMTscope

The [SMTscope tool](https://viperproject.github.io/smt-scope/) by the [Viper project](https://viper.ethz.ch/) can be used to debug quantifier instantiations in SMT queries.
SMTscope is a graphical tool that allows you to visualize the quantifier instantiations that Z3 performs during the solving process.
This can be useful to understand why a query is taking a long time to solve or why it is not solving at all.

To use SMTscope with Caesar, you need to run Caesar with the `--z3-trace` flag.
This will create a `z3.log` file in the current directory.
Load this file into SMTscope to visualize the quantifier instantiations.

SMTscope's *matching loop* detection is very useful.
A matching loop occurs when Z3 repeatedly instantiates the same quantifier pattern.
This can be a sign that some quantifiers need additional [triggers](../heyvl/expressions.md#triggers) to help Z3 find a solution.

## Further Reading

 * [Dafny's guidelines for verification](https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-verification) can be helpful.
   Many of the ideas translate pretty much directly to Caesar.

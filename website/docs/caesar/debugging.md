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

## Further Reading

 * [Dafny's guidelines for verification](https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-verification) can be helpful.
   Many of the ideas translate pretty much directly to Caesar.

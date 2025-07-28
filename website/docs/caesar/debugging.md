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
 * [Definitional functions](../heyvl/domains.md#definitional-functions) can introduce nontermination. See the section on [function encodings and limited functions](#function-encodings-and-limited-functions) for more information.
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

### Z3 Statistics

With the `--print-z3-stats` command-line flag, Caesar will print Z3 statistics to standard error.

## Debugging Quantifier Instantiations


### Function Encodings and Limited Functions

Caesar supports many different encodings of [definitional functions](../heyvl/domains.md#definitional-functions), which can be selected via the `--function-encoding` command-line option.

The default is `--function-encoding fuel-param`, which uses a *fuel parameter* to limit how many times a function can be unfolded in the SMT query by the *e-matching* quantifier instantiation strategy.
For example, a simple recursive definition of exponentials, `exp(x)` will only be unfolded at most `2` times (c.f. [Definitional Functions](../heyvl/domains.md#definitional-functions) for a definition).

Available function encodings:

- **`axiomatic`**: The most direct encoding with FO + uninterpreted functions, allowing for unbounded computations and arbitrary quantifier instantiations.
- **`decreasing`**: Like axiomatic encoding but only allows decreasing instantiations, where the defining axiom is only instantiated based on occurrences of the function it defines, not other functions in the definition. These instantiations are unbounded.
- **`fuel-mono`**: Add a version of the function for each fuel value (f_0, f_1, ...) and recursive calls decrease the fuel value.
- **`fuel-param`** (default): Add a symbolic fuel parameter to the function.
- **`fuel-mono-computation`**: Like `fuel-mono`, additionally allowing unbounded unfolding if the parameter values are literals.
- **`fuel-param-computation`**: Like `fuel-param`, additionally allowing unbounded unfolding if the parameter values are literals.
- **`define-fun-rec`** (alias: `recfun`): Uses [SMT-LIB's `define-fun-rec`](https://microsoft.github.io/z3guide/docs/logic/Recursive%20Functions/) to encode functions.
  - Only supports input parameter types without SMT invariants right now.

#### Literals

The `fuel-mono-computation` and `fuel-param-computation` encodings additionally allow unbounded unfolding if the parameter values are *literals*.
Literals are expressions that do not contain variables.
Caesar will also mark calls to *definitional* functions with literal parameters as literals, so that e.g. `exp(5)` is a literal and the definition of `exp` can be unfolded as many times as needed.
Calls to [uninterpreted functions](../heyvl/domains.md#axiomatizing-uninterpreted-functions) are never considered literals, except when [annotated with the `@computable` annotation](../heyvl/domains.md#computable-annotation).

#### Termination

Specific encodings can guarantee termination of the SMT query, which in practice means that we can quickly and stably obtain a result of either "verified", "counter-example found", or "unknown".
Termination guarantees can only be given when using the [`--quantifier-instantiation e-matching` command-line option](#selecting-quantifier-instantiation-strategies) (disabling MBQI).

Then:
- **`axiomatic`** does not guarantee termination.
- **`decreasing`** guarantees termination only if the defined functions are terminating.
- **`fuel-mono` and `fuel-mono-computation`** guarantee termination.
- **`fuel-param` and `fuel-param-computation`** guarantee termination.
- **`define-fun-rec`** does not guarantee termination.


### Selecting Quantifier Instantiation Strategies

You can select which strategies Z3 is allowed to use with Caesar's `--quantifier-instantiation` command-line option.
When restricting the quantifier instantiation to `e-matching`, the fuel encodings guarantee termination of the SMT query.
Available quantifier instantiation strategies:

- **`all`** (default): Use all available quantifier instantiation heuristics, in particular both e-matching and MBQI are enabled.
- **`e-matching`**: Only use E-matching for quantifier instantiation.
    * This disables MBQI; when using the fuel encodings, e-matching is guaranteed to terminate.
- **`mbqi`**: Only use [MBQI](https://microsoft.github.io/z3guide/docs/logic/Quantifiers/#model-based-quantifier-instantiation) for quantifier instantiation.

### Simple QI Profiling

With Caesar's `--z3-qi-profile` command-line flag, you can enable logging of quantifier instantiations.
This will enable [Z3's `smt.qi.profile` option](https://microsoft.github.io/z3guide/programming/Parameters/#smt).

Currently, this will print Z3's quantifier instantiation statistics to standard error every 1000 instantiations.

The output will look like this:

```
[quantifier_instances]    135-141 :     11 :   0 :   0 :   0 : 1
[quantifier_instances] exp(return_invariant) :     57 :   0 :   0 :   3 : 4
[quantifier_instances] exp(fuel_synonym) :     30 :   0 :   0 :   2 : 3
[quantifier_instances] exp(definitional) :     30 :   0 :   0 :   2 : 3
```

Where the columns represent the following:[^z3-qi-profile-docs]
  1. The quantifier instance name, e.g. `exp(return_invariant)`.
  2. The number of instantiations of this quantifier.
  3. <small>(always zero?)</small>
  4. <small>(always zero?)</small>
  5. Maximum generation depth of the quantifier instantiation.
      * <small>Let's say we have `forall x . p(x) => p(x + 1)`, and `p(0)`. Then `p(1)` has generation 1, `p(2)` has generation 2, etc.</small>
  6. Maximum cost of the quantifier instantiation.

[^z3-qi-profile-docs]: [Z3's documentation on `smt.qi.profile`](https://microsoft.github.io/z3guide/programming/Parameters/#smt.qi.profile) is rather sparse. The description is based on the [source code of `smt_quantifier.cpp` of Z3](https://github.com/Z3Prover/z3/blob/f77123c13cc8dabe8d1d0217a3312738da834eba/src/smt/smt_quantifier.cpp#L169-L189) and [this issue comment by Nikolaj Bjorner](https://github.com/Z3Prover/z3/issues/4522#issuecomment-644454562).

### MBQI Tracing

When using MBQI, you can enable tracing of the quantifier instantiation process with the `--z3-mbqi-trace` command-line flag.
It will enable Z3's `smt.mbqi.trace` option, which will print a message before every round of MBQI.

### Debugging with SMTscope

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

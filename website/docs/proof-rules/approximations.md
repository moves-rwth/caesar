---
title: Soundness of Proof Rules
sidebar_position: 0
description: Approximations, sound verifications and refutations.
---

```mdx-code-block
import Mermaid from '@theme/Mermaid';
import Tabs from '@theme/Tabs';
import TabItem from '@theme/TabItem';
import styles from './approximations.module.css';
import { QuickGuide } from '@site/src/components/ProofRuleQuickCard';
import { TokLFP, TokGFP, TokProc, TokCoproc, TokExact, TokOver, TokUnder, TokUnknown } from '@site/src/components/SemanticToken';
```

# Soundness of Proof Rules

Using a proof rule to verify a HeyVL program can introduce approximations compared to the original program semantics.
These approximations influence guarantees Caesar gives during verification:

1. **Sound verification:** verification succeeds $\implies$ property holds for original program.
2. **Sound refutation:** verification fails $\implies$ property does not hold for original program (counterexample is valid).

Without sound verification, a property may not hold for the original program (_unsound verification_).
On the other hand, without sound refutations, a counter-example may be _spurious_ (not valid in the original program).
However, it still is a _counter-example to verification_, which can be used to e.g. improve loop invariants.

Most program verifiers aim for sound verifications, but Caesar also supports sound refutations.
This is useful when you want to show that a certain expectation is not a lower or upper bound.

This guide gives an overview of Caesar's proof rules and how they affect soundness of verifications and refutations.
Caesar gives diagnostics when a verification or refutation might be unsound because of an incompatible proof-rule/calculus setup.
For an overview of what Caesar does and does not check automatically, see [What Is Checked By Caesar](#what-is-checked).

## Quick Overview

To verify or refute a lower/upper bound (<TokProc />/<TokCoproc />), the proof rules must induce the right approximation (<TokOver />/<TokUnder />) between original semantics ($orig$) and verification condition semantics ($vc$).
The cards below are the quick reference; the detailed rule mapping appears later in [Proof Rule Approximations](#proof-rule-approximations).

{(() => {
  const procKind = <TokProc />;
  const coprocKind = <TokCoproc />;

  const underRows = [
    {
      id: 'lfp',
      semantics: <TokLFP />,
      calculi: [
        { href: '#calculus-annotations', label: '@wp' },
        { href: '#calculus-annotations', label: '@ert' },
      ],
      rules: [
        { href: './unrolling', label: '@unroll' },
        { href: './omega-invariants', label: '@omega_invariant' },
        { href: './ost', label: '@ost' },
        { href: './ast#new-proof-rule', label: '@ast' },
      ],
    },
    {
      id: 'gfp',
      semantics: <TokGFP />,
      calculi: [{ href: '#calculus-annotations', label: '@wlp' }],
      rules: [
        { href: '../heyvl/procs#calling-procedures', label: 'calls' },
        { href: './induction', label: '@invariant' },
        { href: './induction', label: '@k_induction' },
      ],
    },
  ];

  const overRows = [
    {
      id: 'lfp',
      semantics: <TokLFP />,
      calculi: [
        { href: '#calculus-annotations', label: '@wp' },
        { href: '#calculus-annotations', label: '@ert' },
      ],
      rules: [
        { href: '../heyvl/procs#calling-procedures', label: 'calls' },
        { href: './induction', label: '@invariant' },
        { href: './induction', label: '@k_induction' },
        { href: './past#past-from-ranking-superinvariants', label: '@past' },
      ],
    },
    {
      id: 'gfp',
      semantics: <TokGFP />,
      calculi: [{ href: '#calculus-annotations', label: '@wlp' }],
      rules: [
        { href: './unrolling', label: '@unroll' },
        { href: './omega-invariants', label: '@omega_invariant' },
      ],
    },
  ];

  const cards = [
    { mode: 'Verification', kind: procKind, boundHint: 'lower bounds', approx: 'Under', rows: underRows },
    { mode: 'Verification', kind: coprocKind, boundHint: 'upper bounds', approx: 'Over', rows: overRows },
    { mode: 'Refutation', kind: procKind, boundHint: 'lower bounds', approx: 'Over', rows: overRows },
    { mode: 'Refutation', kind: coprocKind, boundHint: 'upper bounds', approx: 'Under', rows: underRows },
  ];
  return <QuickGuide cards={cards} />;
})()}

<div className={styles.exampleBox}>
<div className={styles.exampleBoxTitle}>Example: Sound and Unsound Proofs and Refutations</div>

All four examples share the same geometric loop and [`@invariant` annotation](./induction.md); only kind (`proc`/`coproc`) and `pre` differ, so each one is an <TokOver /> approximation of the original loop semantics.

<Tabs groupId="full-spectrum-outcomes">
  <TabItem value="sound-proof" label="Sound Proof">
<div className={styles.fullSpectrumCode}>

Caesar reports _sound verification_: We show that `init_x + 2` is an upper bound (`coproc`) on the expected value of `x` on termination (`@wp`).
The actual expected value is `init_x + 1`.

```heyvl {1-2}
@wp coproc sound_proof(init_x: UInt) -> (x: UInt)
    pre init_x + 2
    post x
{
    x = init_x
    var cont: Bool = true
    @invariant(ite(cont, x + 1, x))
    while cont {
        cont = flip(0.5)
        if cont {x = x + 1 } else { }
    }
}
```
</div>
  </TabItem>
  <TabItem value="sound-refutation" label="Sound Refutation">
<div className={styles.fullSpectrumCode}>

Caesar reports _a counter-example to the property_: We refute that `init_x + 2` is a lower bound (`proc`) on the expected value of `x` on termination (`@wp`).
The actual expected value is `init_x + 1`.

```heyvl {1-2}
@wp proc sound_refutation(init_x: UInt) -> (x: UInt)
    pre init_x + 2
    post x
{
    x = init_x
    var cont: Bool = true
    @invariant(ite(cont, x + 1, x))
    while cont {
        cont = flip(0.5)
        if cont { x = x + 1 } else {}
    }
}
```
</div>
  </TabItem>
  <TabItem value="unsound-proof" label="Unsound Proof">
<div className={styles.fullSpectrumCode}>

Caesar reports _unsound verification_: We want to verify that `init_x + 1` is a lower bound (`proc`) on the expected value of `x` on termination (`@wp`), but Park induction does not give us this guarantee.

```heyvl {1-2}
@wp proc unsound_proof(init_x: UInt) -> (x: UInt)
    pre init_x + 1
    post x
{
    x = init_x
    var cont: Bool = true
    @invariant(ite(cont, x + 1, x))
    while cont {
        cont = flip(0.5)
        if cont { x = x + 1 } else {}
    }
}
```
</div>
  </TabItem>
  <TabItem value="unsound-refutation" label="Unsound Refutation">
<div className={styles.fullSpectrumCode}>

Caesar reports _a counter-example to verification_: it is a <abbr className={styles.hoverHint} title="init_x = 0, cont = false, x = 2" aria-label="Counterexample details: init_x equals 0, cont equals false, x equals 2">counterexample</abbr> against `init_x + 1` as an upper bound (`coproc`) on the expected value of `x` on termination (`@wp`).
But this is only because the `@invariant(1)` is not inductive (as Caesar reports), not because the specification does not hold.

```heyvl {1-2,7}
@wp coproc unsound_refutation(init_x: UInt) -> (x: UInt)
    pre init_x + 1
    post x
{
    x = init_x
    var cont: Bool = true
    @invariant(1)
    while cont {
        cont = flip(0.5)
        if cont { x = x + 1 } else {}
    }
}
```
</div>
  </TabItem>
</Tabs>
</div>

## Original Program Semantics

The _original semantics_ ($orig$) is the semantics of the high-level program, which may feature constructs such as loops and recursion.
During verification, we want to obtain sound results with respect to the original semantics.
There are different ways to define the original semantics, but here we are mainly concerned with how they differ in their treatment of nonterminating loop and recursion runs.

### A Zoo of Original Semantics

We distinguish:

- **Least Fixed Point** (<TokLFP />) Semantics: while loops and recursive calls are interpreted via _least_ fixed points.
  - This is used in calculi such as $wp$ and $ert$.
  - In short: "nonterminating runs contribute post $0$ to the expected value".
- **Greatest Fixed Point** (<TokGFP />) Semantics: while loops and recursive calls are interpreted via _greatest_ fixed points.
  - This is used in calculi such as $wlp$.
  - In short: "nonterminating runs contribute post $1$ to the expected value".

### Calculus Annotations {#calculus-annotations}

Caesar supports procedure annotations to make the intended calculus explicit:

- `@wp`: weakest pre-expectation calculus (least fixed points, nontermination contributes `0`).
- `@wlp`: weakest liberal pre-expectation calculus (greatest fixed points, nontermination contributes `1`).
- `@ert`: expected runtime calculus (least fixed points).

These annotations let Caesar check additional soundness conditions for proof-rule usage.

:::note RECOMMENDED PAPERS
We recommend reading the following literature for formal accounts of the above semantics:

- **wp (LFP) and wlp (GFP) Semantics:** [Advanced Weakest Precondition Calculi for Probabilistic Programs](https://publications.rwth-aachen.de/record/755408/files/755408.pdf#page=91), Chapter 4, Kaminski (2019).
- **Least Fixpoint Semantics in Detail:** [J-P: MDP. FP. PP -- Characterizing Total Expected Rewards in Markov Decision Processes as Least Fixed Points with an Application to Operational Semantics of Probabilistic Programs](https://doi.org/10.1007/978-3-031-75783-9_11), Batz et al. (2024).
:::

### How Caesar Selects Original Semantics

1. If a calculus annotation (`@wp`, `@wlp`, or `@ert`) is present on a (co)proc:
   - <TokLFP /> for `@wp` and `@ert`,
   - <TokGFP /> for `@wlp`.
2. Otherwise selected by the proof rule so that verifications are sound (see [Proof Rule Approximations](#proof-rule-approximations)).
   - E.g. for Induction, <TokGFP /> semantics are used for <TokProc />s and <TokLFP /> semantics for <TokCoproc />s.
   - E.g. for Loop Unrolling, <TokLFP /> semantics are used for <TokProc />s and <TokGFP /> semantics for <TokCoproc />s.

## Approximations, Proofs, and Refutations

Correct results &mdash; sound verification or sound refutation &mdash; depend on how we approximate the original semantics ($orig$) by the _verification condition semantics_ ($vc$).
The verification condition semantics is the semantics of the verification conditions that Caesar generates and reasons about.

:::note RECOMMENDED READING
 Our paper [_A Deductive Verification Infrastructure for Probabilistic Programs_](../publications#oopsla-23) explains the verification condition semantics in detail and covers several of the proof rules.
:::


<figure className={`${styles.figureCard} ${styles.decisionFigure}`}>
    <Mermaid value={`
%%{init: {
  'themeVariables': { 'edgeLabelBackground': '#ffffff' },
  'flowchart': { 'nodeSpacing': 22, 'rankSpacing': 20, 'padding': 6 }
}}%%
flowchart LR
    subgraph L[" "]
        direction TB
        LB["Lower Bound (proc)"]
        UB["Upper Bound (coproc)"]
    end

    subgraph R[" "]
        direction TB
        UNDER(["Under-approximation"])
        OVER(["Over-approximation"])
    end

    LB -->|Verification| UNDER
    LB -->|Refutation| OVER
    UB -->|Verification| OVER
    UB -->|Refutation| UNDER

    classDef bound fill:#edf2ff,stroke:#5b79b5,stroke-width:1px,color:#111;
    classDef approx fill:#eaf7ed,stroke:#5e946b,stroke-width:1px,color:#111;
    class LB,UB bound;
    class UNDER,OVER approx;

    style L fill:none,stroke:none;
    style R fill:none,stroke:none;

    linkStyle 0,2 stroke:#1f4b99,stroke-width:2.2px,color:#1f4b99,font-weight:bold,font-size:14px;
    linkStyle 1,3 stroke:#8a2b0f,stroke-width:2.2px,color:#8a2b0f,font-weight:bold,font-size:14px;
`} />
    <figcaption>Overview of which approximation is required to verify/refute lower/upper bounds.</figcaption>
</figure>

We distinguish between four kinds of approximations: <TokExact />, <TokOver />, <TokUnder />, or <TokUnknown />.
Correct results also depend on whether you reason about lower bounds (<TokProc />) or upper bounds (<TokCoproc />).
We explain the details in this section.

The figure gives a quick overview: for lower bounds (<TokProc />), _verification_ requires <TokUnder /> and _refutation_ requires <TokOver /> approximations; for upper bounds (<TokCoproc />), _verification_ requires <TokOver /> and _refutation_ requires <TokUnder /> approximations.
With <TokExact /> approximations, both verifications and refutations are sound; with <TokUnknown /> approximations, neither verifications nor refutations are sound.

<!-- Clear the floating figure above -->
<div style={{"clear": "both"}} />

### Kinds of Approximations

<figure className={`${styles.figureCard} ${styles.latticeFigure}`}>
    <Mermaid value={`
graph TD;
    Exact-->Over;
    Exact-->Under;
    Over-->Unknown;
    Under-->Unknown;
`} />
    <figcaption>Arrows indicate one approximation being stronger than the other.</figcaption>
</figure>

We distinguish four kinds of approximations between the original semantics ($orig$) and the verification condition semantics ($vc$). Let $S$ be a HeyVL statement and $X$ be a post-expectation.

- <TokExact />: No approximation is performed. <br></br> Formally: $orig[S](X) = vc[S](X)$ for all $X$.
- <TokUnder />: The pre-expectation is approximated from below. <br></br> Formally: $orig[S](X) \geq vc[S](X)$ for all $X$.
- <TokOver />: The pre-expectation is approximated from above. <br></br> Formally: $vc[S](X) \geq orig[S](X)$ for all $X$.
- <TokUnknown />: None of the above holds.

Approximations are compositional[^1].
For example, the sequential composition $S_1;~ S_2$ of two <TokExact /> statements $S_1, S_2$ is also <TokExact />.
Same for <TokOver /> and <TokUnder />.
Combining <TokExact /> with either <TokOver /> or <TokUnder /> yields the respective approximation.
However, combining <TokOver /> and <TokUnder /> statements results in an <TokUnknown /> approximation.

[^1]: Compositionality of approximations follows from the fact that the semantics of HeyVL's statements is monotonic with respect to the expectation ordering. The only exception are non-monotonic negation statements, which always yield an <TokUnknown /> approximation.

### Sound Verifications

When Caesar says that a (co)proc is verified, then a bound on verification condition semantics ($vc$) has been established.

In a <TokProc />, Caesar reasons about lower bounds $pre$ of the verification condition semantics ($vc$), i.e. $pre \leq vc[S](post)$.

- If $vc[S](post)$ is an <TokUnder /> approximation of the original semantics ($orig$), then we have sound verifications:

$$
\texttt{pre} \;\leq\; vc[S](post) \;\leq\; orig[S](post).
$$

Dually, in a <TokCoproc />, Caesar reasons about upper bounds $pre$ of the verification condition semantics ($vc$), i.e. $pre \geq vc[S](post)$.

- If $vc[S](post)$ is an <TokOver /> approximation of the original semantics ($orig$), then we have sound verifications:

$$
\texttt{pre} \;\geq\; vc[S](post) \;\geq\; orig[S](post).
$$

The results also apply for <TokExact /> approximations.

### Sound Refutations

When Caesar gives a counterexample for a (co)proc, then a bound on verification condition semantics ($vc$) has been refuted.

In a <TokProc />, a refutation means showing that $pre \nleq vc[S](post)$.

- If $vc[S](post)$ is an <TokOver /> approximation of the original semantics ($orig$), then we have sound refutations because $pre$ cannot be a lower bound of $orig[S](post)$:

$$
\texttt{pre} \;\nleq\; vc[S](post) \;\land\; vc[S](post) \;\geq\; orig[S](post) \;\Rightarrow\; \texttt{pre} \;\nleq\; orig[S](post).
$$

Dually, in a <TokCoproc />, a refutation means showing that $pre \ngeq vc[S](post)$.

- If $vc[S](post)$ is an <TokUnder /> approximation of the original semantics ($orig$), then we have sound refutations because $pre$ cannot be an upper bound of $orig[S](post)$:

$$
\texttt{pre} \;\ngeq\; vc[S](post) \;\land\; vc[S](post) \;\leq\; orig[S](post) \;\Rightarrow\; \texttt{pre} \;\ngeq\; orig[S](post).
$$

The results also apply for <TokExact /> approximations.

<details>
    <summary>Formal Proof: Sound Refutations in <TokProc />s</summary>

    Let a <TokProc /> not verify ($pre \nleq vc[S](post)$) and let $vc[S](post)$ be an <TokOver /> approximation ($vc[S](post) \geq orig[S](post)$).
    For the sake of a contradiction, assume $pre \leq orig[S](post)$.

    By transitivity with $orig[S](post) \leq vc[S](post)$, we get
    $pre \;\leq\; orig[S](post) \;\leq\; vc[S](post)$, hence $pre \leq vc[S](post)$, contradicting $pre \nleq vc[S](post)$.
    Therefore $pre \nleq orig[S](post)$.

</details>

## Proof Rule Approximations

As explained above, proof rules such as `@invariant` may introduce approximations between the original semantics ($orig$) and the verification condition semantics ($vc$).
Below, we summarize which of [Caesar's built-in proof rules](../proof-rules/) induce which approximations, and thus which proof rules are applicable for sound verification/refutation of lower/upper bounds.

| Original Semantics | Approximation | Applicable Proof Rules |
| --- | --- | --- |
| <TokLFP /> | <TokOver /> | [Procedure Calls](../heyvl/procs#calling-procedures)<br/>[(k)-Induction](./induction) (`@invariant`, `@k_induction`)<br/>[Positive Almost-Sure Termination Rule](./past#past-from-ranking-superinvariants) (`@past`) |
| <TokLFP /> | <TokUnder /> | [Loop Unrolling](./unrolling) (`@unroll`)<br/>[ω-invariants](./omega-invariants) (`@omega_invariant`)<br/>[Optional Stopping Theorem](./ost) (`@ost`)<br/>[Almost-Sure Termination Rule](./ast#new-proof-rule) (`@ast`) |
| <TokGFP /> | <TokOver /> | [Loop Unrolling](./unrolling) (`@unroll`)<br/>[ω-invariants](./omega-invariants) (`@omega_invariant`) |
| <TokGFP /> | <TokUnder /> | [Procedure Calls](../heyvl/procs#calling-procedures)<br/>[(k)-Induction](./induction) (`@invariant`, `@k_induction`) |

For loops, the loop-body approximation must be compatible with the chosen rule.
For example, for k-Induction under <TokLFP />, the loop body must be <TokOver /> so the whole loop is <TokOver />.
Additionally, the rules [Almost-Sure Termination Rule](./ast#new-proof-rule), [Positive Almost-Sure Termination Rule](./past#past-from-ranking-superinvariants), and [Optional Stopping Theorem](./ost) require the loop body to be <TokExact />.

## What Is Checked By Caesar {#what-is-checked}

HeyVL is designed as an intermediate verification language and intentionally allows dangerous constructs.
See our [OOPSLA '23 paper](../publications#oopsla-23) for more background.

Caesar checks many proof-rule soundness conditions automatically, but not all modeling assumptions.

**Hard errors:**

- In calculus-annotated procedures, calling a procedure with a conflicting calculus annotation is rejected.
- Potentially recursive calls are rejected where Park induction is not sound (`@wp proc`, `@wlp coproc`, `@ert proc`).

**Diagnostics during verification:**

- Caesar tracks approximation information per procedure, errors when a proof result may be unsound, and marks counterexamples as potentially spurious when they may not be valid.

**Not checked:**

- Contradictions make verification trivially succeed — e.g., `assume ?(false)` in a `proc`; [contradictory axioms](../heyvl/domains#axioms-as-assumptions) are a common source.
- There is no enforcement that `@ert` procedures contain `tick` statements, nor that `@wp`/`@wlp` procedures do not.

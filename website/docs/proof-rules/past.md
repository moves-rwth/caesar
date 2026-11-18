---
sidebar_position: 6
---

# Positive Almost-Sure Termination

```mdx-code-block
import Citation from '@site/src/components/Citation';
import ProofRuleGuarantee from '@site/src/components/ProofRuleGuarantee';
import {references as sources} from '@site/src/data/references';
import TOCInline from '@theme/TOCInline';

export const references = {
  kaminski: {
    ...sources.kaminski2019,
    href: "https://publications.rwth-aachen.de/record/755408/files/755408.pdf#page=143",
  },
  martingales: sources.martingales2013,
  fioriti: sources.probabilisticTermination2015,
};
```

<ProofRuleGuarantee rule="past" />

_Positive almost-sure termination_ (PAST for short) means that a program [terminates almost surely](./ast.md) and the expected runtime to termination is finite.
In HeyVL, [`reward` statements](../heyvl/statements.md#reward-and-weigh) model the cost measured by the expected runtime calculus.
`tick` is an alias for `reward`.

```mdx-code-block
<TOCInline toc={toc} maxHeadingLevel="2" />
```

## Upper Bounds on `ert`

[Park induction](./induction.md) suffices to prove PAST when every nonterminating execution accumulates infinite total reward.
A finite upper bound $\mathrm{ert}\llbracket C \rrbracket(0) \leq g < \infty$ then establishes both almost-sure termination and finite expected reward.
If each execution of the loop body terminates, adding `reward 1` per iteration makes the iteration count at most the total reward.

## PAST from Ranking Superinvariants

In an `@ert coproc`, `@past(I, epsilon, K)` proves that a loop terminates almost surely using a *ranking superinvariant* $I$.
From an initial state $s$, it bounds the expected number of iterations by $I(s) / \epsilon$ and the expected sum of the loop's rewards by $I(s)$.
The [soundness proof](#past-via-ert-superinvariants) derives these guarantees by Park induction.

If the `coproc` omits its calculus annotation, `@past` selects least-fixed-point semantics.

The rule follows the ranking-superinvariant argument <Citation {...references.kaminski} locator="Theorem 6.3" />.
Related results use the term *ranking supermartingale* <Citation {...references.martingales} locator="Theorem 4" />, <Citation {...references.fioriti} locator="Theorem 5.6" />.

### Verification Conditions {#formal-theorem}

Let $L$ be a loop `while G { Body }` with a loop-free probabilistic body and valid sampling parameters.
The body may use local declarations, assignments, conditionals, built-in sampling, and rewards.
The constants $\epsilon$ and $K$ are `UReal` literals with $0 < \epsilon < K$.

1. **Exit.** $I \leq K$ when $G$ is false.
2. **Ranking.** $I < \infty$ in every state and $K \leq I$ when $G$ is true.
3. **Decrease.** $\mathrm{ert}\llbracket \mathtt{Body} \rrbracket(I) \leq I - \epsilon$ when $G$ is true.

In the decrease check, $\mathrm{ert}$ adds the body's expected reward to the expected value of $I$ after the iteration.
The sum must be at least $\epsilon$ below the entry value of $I$.

<details>
<summary>Generated HeyVL checks</summary>

Here `vars` denotes the variables used by the loop or annotation, excluding loop-local variables.

```heyvl
proc I_bounded_on_exit(vars: ...) -> ()
{
    assert ?(([!G(vars)] * I(vars)) <= K)
}

proc K_bounded_by_I(vars: ...) -> ()
{
    assert ?(I(vars) < ∞ && ([G(vars)] * K <= [G(vars)] * I(vars) + [!G(vars)]))
}

coproc I_decreases(init_vars: ...) -> (vars: ...)
    pre [G(init_vars)] * (I(init_vars) - epsilon)
    post 0
{
    vars = init_vars
    if G {
        Body
        assert I(vars)
        assume 0
    } else {}
}
```

</details>

### Usage

To bound the procedure's expected reward, set `post 0` and give a finite upper bound in `pre`.

The countdown charges one reward per coin flip and decrements `x` on heads.
Caesar verifies almost-sure termination and an upper bound of $3 \cdot \mathtt{init\_x} + 1$ on the expected number of flips.

```heyvl
@ert
coproc main(init_x: UInt) -> (x: UInt)
    pre 3 * init_x + 1
    post 0
{
    var prob_choice: Bool
    x = init_x
    @past(
        /* invariant: */ 3 * x + 1,
        /* epsilon:   */ 0.5,
        /* K:         */ 1)
    while 0 < x {
        reward 1
        prob_choice = flip(0.5)
        if prob_choice {
            x = x - 1
        } else {}
    }
}
```

On heads, $3 \cdot x + 1$ drops by $3$, so the expected drop after charging the reward is $\tfrac12 \cdot 3 - 1 = \tfrac12$.

### Loop Summary

The summary adds the reward bound $I$, evaluated at entry, to the supremum of the postexpectation over states that satisfy $\neg G$ and agree with the entry state outside `modified`.
Here `modified` lists the variables assigned by the body that remain in scope after the loop.
When $G$ is false on entry, the summary acts as `skip`.

```heyvl
if G {
    tick I
    cohavoc modified
    coassume ?(G)
} else {}
```

This [over-approximation](./approximations.md#kinds-of-approximations) can yield spurious counterexamples.

### Soundness {#past-via-ert-superinvariants}

We prove that the [verification conditions](#formal-theorem) imply almost-sure termination and bound the expected number of iterations and the expected reward.
Under $G$, the parameter and ranking checks give $\epsilon < K \leq I < \infty$.
Starting from the decrease check, we derive a bound for `Body; reward epsilon`, which charges an extra $\epsilon$ per completed iteration.

$$
\begin{aligned}
    &\mathrm{ert}\llbracket \mathtt{Body} \rrbracket(I) \leq I - \epsilon
        && \text{(decrease check)} \\
    \iff{} &\mathrm{ert}\llbracket \mathtt{Body} \rrbracket(I) + \epsilon \leq I
        && \text{(add }\epsilon\text{)} \\
    \iff{} &\mathrm{ert}\llbracket \mathtt{Body} \rrbracket(I + \epsilon) \leq I
        && \text{(the body terminates)} \\
    \iff{} &\mathrm{ert}\llbracket \mathtt{Body};\,\mathtt{reward}\,\epsilon \rrbracket(I) \leq I
        && \text{(composition).}
\end{aligned}
$$

The last inequality and $0 \leq I$ when $G$ is false give the [Park induction](./induction.md) premises for `while G { Body; reward epsilon }` with postexpectation $0$.
For a run with $T$ iterations the extra reward contributes $\epsilon \cdot T$, so from an initial state $s$ we have

$$
\begin{aligned}
    I(s)
    &\geq \mathrm{ert}\llbracket \mathtt{while}\ G\ \{\mathtt{Body};\,\mathtt{reward}\,\epsilon\} \rrbracket(0)(s) \\
    &= \mathrm{ert}\llbracket L \rrbracket(0)(s) + \epsilon \cdot \mathbb{E}_s[T].
\end{aligned}
$$

Every nonterminating execution has $T = \infty$ because each execution of the body terminates.
Since $\mathbb{E}_s[T] \leq I(s) / \epsilon < \infty$, the loop terminates almost surely.

---
description: Induction and k-Induction are proof rules for while loops.
sidebar_position: 2
---

# Induction and k-Induction

_Induction_ and the more general _$k$-induction_ are built-in proof rules to reason about `while` loops.
The *non-probabilistic* intuition goes as follows: induction requires an _invariant_ that is maintained by each loop iteration.
The invariant must hold before the loop, and then we are guaranteed that the invariant holds after the loop.
The rule corresponds to the well-known [proof rule for loops from Hoare logic](https://en.wikipedia.org/wiki/Hoare_logic#While_rule).

Generalized to *probabilistic* `wlp` semantics, induction allows us to prove a lower bound on the `wlp`-semantics of a loop.
$I$ must be an expression whose expected value does not decrease with each loop iteration.
Formally:
$$
    I \sqsubseteq [G] \cdot \mathrm{wlp}\llbracket Body \rrbracket(I) + [\neg G] \cdot f \quad\text{implies}\quad I \sqsubseteq \mathrm{wlp}\llbracket \texttt{while G \{ Body \}} \rrbracket(f)
$$
A dual version exists for `wp` and `ert` semantics.

*$k$-induction* is a strictly stronger version of induction.
Refer to the [CAV 2021 paper presenting *latticed k-induction*](https://link.springer.com/chapter/10.1007/978-3-030-81688-9_25) for more details.
It allows us to reason about multiple loop iterations: the invariant is not required to be re-established after just one loop iteration, but may be re-established after $1$, $2$, ..., up to $k$ loop iterations.

## Usage

### Using Induction

To use _induction_, simply add an `@invariant(I)` annotation to your loop with a probabilistic invariant `I`.
In this case, it is `ite(cont, c + 1, c)`.
```heyvl
@wp coproc geo1_induction(init_c: UInt) -> (c: UInt)
    pre init_c + 1
    post c
{
    c = init_c
    var cont: Bool = true
    @invariant(ite(cont, c + 1, c))
    while cont {
        var prob_choice: Bool = flip(0.5)
        if prob_choice { cont = false } else { c = c + 1 }
    }
}
```

In a `coproc`, Caesar will use the *super-invariant* version to prove an upper bound on the least fixed-point semantics of the loop (`wp`, `ert` semantics):
$$
    I \sqsupseteq [G] \cdot \mathrm{wp}\llbracket Body \rrbracket(I) + [\neg G] \cdot f \quad\text{implies}\quad I \sqsupseteq \mathrm{wp}\llbracket \texttt{while G \{ Body \}} \rrbracket(f)
$$

In a `proc`, Caesar will use the *sub-invariant* version to prove a lower bound on the greatest fixed-point semantics of the loop (`wlp` semantics):
$$
    I \sqsubseteq [G] \cdot \mathrm{wlp}\llbracket Body \rrbracket(I) + [\neg G] \cdot f \quad\text{implies}\quad I \sqsubseteq \mathrm{wlp}\llbracket \texttt{while G \{ Body \}} \rrbracket(f)
$$

See the [section on soundness](#soundness) below for more information when it is sound to use induction.
The [section on internal details](#internal-details) below explains the precise encoding and behavior also when the invariant is not inductive.

### Using k-Induction

To use _k-induction_, you can use the `@k_induction(k, I)` annotation on a loop.
It takes two parameters: The number literal `k` specifies the number of unrollings are to be done and `I` is the invariant.
```heyvl
@wp coproc geo1_2induction(init_c: UInt) -> (c: UInt)
    pre init_c + 1
    post c
{
    c = init_c
    var cont: Bool = true
    @k_induction(2, c + 1)
    while cont {
        var prob_choice: Bool = flip(0.5)
        if prob_choice { cont = false } else { c = c + 1 }
    }
}
```
This program will not verify if `k` is set to `1` because the invariant `c + 1` is not 1-inductive.

Just like induction, the `@k_induction` annotation will result in a HeyVL encoding of the loop that checks whether the invariant is inductive.
Again, Caesar will encode the *super-invariant* version for upper bounds in a `coproc` and the *sub-invariant* version for lower bounds in a `proc`.
Check the [soundness section](#soundness) and the [details section](#internal-details) below for more details.

We recommend reading the [*Latticed k-induction* paper](https://link.springer.com/chapter/10.1007/978-3-030-81688-9_25) for more details on the principle of k-induction applied to the verification of probabilistic programs.

## Soundness

:::tip

Use the [calculus annotations](./calculi.md) `@wp`, `@wlp`, `@ert` to have Caesar check that the applied proof rules are sound with respect to the semantics of the chosen calculus.
Then you don't have to worry about this section yourself.

:::

For all loops and all *invariant candidates* $I$, the following holds:
 * In `proc`s: $\mathrm{vc}\llbracket \texttt{@invariant(I) while G \{ B \}} \rrbracket \sqsubseteq \mathrm{wlp}\llbracket \texttt{while G \{ B \}} \rrbracket$ <small>&mdash; (wlp uses greatest fixed-point semantics)</small>,
    * Thus: `proc` verifies using `@invariant(I)` $\implies$ specification also holds for the original `wlp` semantics.
 * In `coproc`s: $\mathrm{vc}\llbracket \texttt{@invariant(I) while G \{ B \}} \rrbracket \sqsupseteq \mathrm{wp}\llbracket \texttt{while G \{ B \}} \rrbracket$ <small>&mdash; (wp uses least fixed-point semantics)</small>,
    * Thus: `coproc` verifies using `@invariant(I)` $\implies$ specification also holds for the original `wlp` semantics.
 * In `coproc`s: $\mathrm{vc}\llbracket \texttt{@invariant(I) while G \{ B \}} \rrbracket \sqsupseteq \mathrm{ert}\llbracket \texttt{while G \{ B \}} \rrbracket$ <small>&mdash; (ert uses least fixed-point semantics)</small>,
    * Thus: `coproc` verifies using `@invariant(I)` $\implies$ specification also holds for the original `ert` semantics.

Stated in terms of fixed points:
 * In `proc`s, `@invariant` *under-approximates* the *greatest fixed-point* loop semantics,
 * In `coproc`s, `@invariant` *over-approximates* the *least fixed-point* loop semantics.

The same statements hold for _k-induction_ (`@k_induction(k, I)`).

## Internal Details

The following section describes the internal details of the encoding of the `@invariant` and `@k_induction` proof rules in Caesar.
We describe the [encoding](#heyvl-encoding) of the proof rules in HeyVL, the [verification pre-expectation semantics](#verification-pre-expectation-semantics) of the encoding, and a more detailed proof of [soundness](#soundness-of-the-encoding) of the encoding.

:::note

More polished formal details on the HeyVL encodings and the (simplified) semantics of the above proof rules are provided in the [extended version of our OOPSLA '23 paper](https://arxiv.org/abs/2309.07781), both in the main text and in Appendix C.

:::

For most of this section, we focus on the encoding of loops with `@invariant` in a `proc` below, i.e. Park induction for lower bounds on greatest fixed-point semantics.
The `coproc`/least-fixed point case is dual.
[k-induction details](#k-induction-encoding-and-interpretation) are similar, and handled at the end of this section.
Let `@invariant(I) while G { Body }` be a loop with an invariant candidate `I`.

### HeyVL Encoding

Internally, the loop with the `@invariant` annotation will be replaced in the following HeyVL encoding:
```heyvl
assert I            // I must hold before the loop
havoc modified_vars // forget values of all variables modified by the loop
validate
assume I            // assume I holds before each iteration
if G {
    Body
    assert I        // I must hold after the loop body
    assume ?(false) // nothing else to establish but I
} else {}
```

The comments indicate a classical (Boolean) interpretation of the encoding:
 1. The `assert I` statement checks that the invariant holds before the loop.
 2. The `havoc modified_vars` statement forgets the values of all variables that are modified by the loop body.
 3. The `validate` statement ensures that the following inductivity check is "classically" valid.
 4. The `assume I` statement checks that the invariant holds before each loop iteration.
 5. The `if G { Body ... } else {}` statement executes the loop body if the guard `G` holds.
 6. The `assert I` statement checks that the invariant holds after the loop body.
 7. The `assume ?(false)` statement says that there is nothing else to establish after the loop body, i.e., the invariant is the only thing we care about.

In the following, we dive into the formal details of the quantitative semantics and soundness of this encoding.

### Verification Pre-Expectation Semantics

In effect, the semantics of the above `proc` encoding evaluates to the following value in state $\sigma$ w.r.t. post $f$:
$$
    \mathrm{vc}\llbracket \texttt{@invariant(I) while G \{ B \}} \rrbracket(f)(\sigma) =
        \begin{cases}
            I(\sigma) & \text{if } I \text{ is an inductive invariant w.r.t. } f \text{ from } \sigma, \\
            0 & \text{otherwise~.}
        \end{cases}
$$
The two cases:
 1. If the invariant $I$ is *inductive* in the initial state $\sigma$, then the encoding evaluates to $I(\sigma)$ (the value of the invariant in that state).
 2. If the invariant is *not* inductive, then the encoding evaluates to $0$.

The check for whether $I$ is *inductive* corresponds to the part of the encoding above starting with the `assume I` statement.
In terms of `wlp` semantics, the common[^common-park-induction] definition of inductivity can be expressed as
$$
    \forall \sigma \in \mathsf{States}.\quad I(\sigma) \leq ([G] \cdot \mathrm{wlp}\llbracket B \rrbracket(I) + [\neg G] \cdot f)(\sigma)~.
$$

[^common-park-induction]: A thorough exposition on the usual definition of *inductive invariants* for probabilistic programming is found in [Benjamin Kaminski's PhD thesis at Definition 5.1](https://publications.rwth-aachen.de/record/755408/files/755408.pdf#page=121).

### Local Inductive Invariants

Caesar's encoding provides a more refined version of the inductivity check.
Intuitively, an invariant is _locally inductive_ if it is inductive in the initial state $\sigma$ and also in all states reachable from $\sigma$.

Reachability is over-approximated in this encoding by the set of states $\text{Havoc}(I, vars)$ that can be reached from $\sigma$ by modifying the variables $vars$ to arbitrary values.
Formally, we consider the set of states $\sigma'$ that agree with $\sigma$ on all variables except those in $vars$:
$$
    \text{Havoc}(\sigma, vars) = \{ \sigma' \in \mathsf{States} \mid \forall v \in \mathsf{Vars} \setminus vars.~ \sigma(v) = \sigma'(v) \}~.
$$
Therefore, in the above semantics, _$I$ is an inductive invariant w.r.t. $f$ from $\sigma$_ (for lower bounds) in a `proc` is formally stated as follows:
$$
    \forall \sigma' \in \text{Havoc}(\sigma, vars).\qquad I(\sigma') \leq ([G] \cdot \mathrm{wlp}\llbracket B \rrbracket(I) + [\neg G] \cdot f)(\sigma').
$$

If the above condition holds, the one can apply the theorem of *Park induction* on the sub-lattice of expectations defined on only the states $\text{Havoc}(\sigma, vars)$ to obtain for state $\sigma$:[^local-park-induction]
$$
    I(\sigma) \leq (\mathrm{gfp}\,X.~\Phi_f(X))(\sigma)~,
$$
where $\Phi_f(X)$ is defined as $[G] \cdot \mathrm{wlp}\llbracket B \rrbracket(X) + [\neg G] \cdot f$.
We call this technique _local Park induction_.

[^local-park-induction]: Formally, one maps every expectation $f \in \mathbb{E}$ to an expectation in the sub-lattice $\mathbb{E}_{\sigma,vars}$ local to $\sigma$ with modified variables $vars$: $\hat{f}(\hat{\sigma}) = f(\sigma)$ where $\hat{\sigma}$ is given by $\hat{\sigma}(v) = \sigma(v)$ if $v \in vars$ and $\hat{\sigma}(v) = \sigma'(v)$ otherwise. In addition, one needs to adjust the definition of $\Phi_f$ to be defined on $\mathbb{E}_{\sigma,vars}$ instead of $\mathbb{E}$.

<details>
<summary>Example: The Advantage of *Local Invariants*</summary>

Consider the following example, where an upper bound is verified on the expected runtime of a geometric loop.
```heyvl
@ert coproc geo_past(p: UReal) -> (c: UInt)
    pre ite(p < 1, 1/(1-p), \infty)
    post 0
{
    c = 0
    var cont: Bool = true
    @invariant(ite(cont, 1/(1-p), 0))
    while cont {
        p = p // removing this makes the program verify
        reward 1
        cont = flip(p)
        if cont { c = c + 1 } else {}
    }
}
```

The above example works *only* because we check for _local inductivity_ of the invariant `ite(cont, 1/(1-p), 0)`.
Here, local inductivity allows Caesar to use the fact that $p < 1$ holds during the loop.

For a counter-example to verification, consider the modified program below which modifies the variable `p` inside the loop.
It is modified by a trivial assignment `p = p`, so it does not change the loop's actual semantics.
However, Caesar will now `havoc` the variable `p` as well, which means that the invariant `ite(cont, 1/(1-p), 0)` is no longer inductive.

```heyvl
@ert coproc geo_past(init_p: UReal) -> (c: UInt)
    pre ite(init_p < 1, 1/(1-init_p), \infty)
    post 0
{
    var p: UReal = init_p
    c = 0
    var cont: Bool = true
    @invariant(ite(cont, 1/(1-p), 0))
    while cont {
        p = p // trivial assignment, but modifies `p`
        reward 1
        cont = flip(p)
        if cont { c = c + 1 } else {}
    }
}
```

The counter-example from Caesar shows that the variable `p` in the loop was assigned the value `2`, clearly indicating the global knowledge $p < 1$ has been lost.

Using the invariant annotation `@invariant(ite(p < 1, ite(cont, 1/(1-p), 0), \infty))` re-adds the lost information and makes the above program verify again.

</details>


### Soundness of the Encoding

The above semantics guarantees [soundness](#soundness) of the `@invariant` proof rule in `proc`s for all post-expectations $f$ and initial states $\sigma$:
$$
    \mathrm{vc}\llbracket \texttt{@invariant(I) while G \{ B \}} \rrbracket(f)(\sigma) \quad\leq\quad \mathrm{wlp}\llbracket \texttt{while G \{ B \}} \rrbracket(f)(\sigma)
$$

In case 1 of [the semantics of the above encoding](#verification-pre-expectation-semantics), the invariant $I$ is inductive w.r.t. $f$ from $\sigma$.
The encoding evaluates to $I(\sigma)$.
By [local Park induction](#local-inductive-invariants), this is a lower bound on the `wlp`-semantics of the loop, thus soundness holds.

In case 2, $I$ is not inductive.
However, $0$ is the trivial lower bound on the `wlp`-semantics of a loop, thus soundness holds trivially.

The cases are dual for upper bound semantics in `coproc`s: If the invariant $I$ is not inductive, then the trivial *upper bound* $0$ is returned.
If the invariant is inductive, $I$ is returned as before.

### k-Induction Encoding and Interpretation

The encoding is similar for k-induction (`@k_induction`).
It also evaluates to `I` if the invariant is *k-inductive* and to $0$ otherwise.

Refer to the [k-induction paper](https://link.springer.com/chapter/10.1007/978-3-030-81688-9_25) for the precise definition and properties of k-inductive invariants.

For *2-induction* for lower bounds, one obtains an encoding of the following form:
```heyvl
assert I            // I must hold before the loop
havoc modified_vars // forget values of all variables modified by the loop
validate
assume I            // assume I holds before each iteration
if G {
    Body
    if ⊔ {              // angelic choice
        assert I        // I must hold after the loop body
        assume ?(false) // nothing else to establish but I
    } else {
        if G {
            Body
            assert I        // I must hold after the loop body
            assume ?(false) // nothing else to establish but I
        } else {}
    }
} else {}
```

One can go for an intuitive Boolean interpretation of this encoding of 2-induction.
It is similar to the [interpretation for (1-)induction](#heyvl-encoding), with the relevant difference in step 6 (marked in bold):
 1. The `assert I` statement checks that the invariant holds before the loop.
 2. The `havoc modified_vars` statement forgets the values of all variables that are modified by the loop body.
 3. The `validate` statement ensures that the following inductivity check is "classically" valid.
 4. The `assume I` statement checks that the invariant holds before each loop iteration.
 5. The `if G { Body ... } else {}` statement executes the loop body if the guard `G` holds.
 6. **The `if ⊔ { ... } else { ... }` allows choosing *angelically* whether to run the loop functional once or twice.**
 7. The `assert I` statements check that the invariant holds after each branch of the loop body.
 8. The `assume ?(false)` statements say that there is nothing else to establish after the loop body, i.e., the invariant is the only thing we care about.

Choosing higher values of `k` in the `@k_induction(k, I)` annotation will result in a similar encoding with nested angelic choices, *allowing to run the loop body up to $k$ times* to establish the invariant again.

Note that the angelic choices `if ⊔ { ... } else { ... }` can also be rewritten via `coassert` statements.
For the encoding of the loop iteration:
```heyvl
... // omitted
if G {
    Body
    coassert I // may stop here and establish I
    if G {
        Body
        assert I        // I must hold after the loop body
        assume ?(false) // nothing else to establish but I
    } else {}
}
```

The above explanation follows the version of $k$-induction for lower bounds on greatest fixed-point semantics.
However, in the literature, $k$-induction is often defined for upper bounds on least fixed-point semantics.[^literature-kind-upper-bounds]
Then, the explanation is dual, and the encoding is similar, but essentially just with the angelic choices `if ⊔ { ... } else { ... }` replaced by demonic choices `if ⊓ { ... } else { ... }`.

[^literature-kind-upper-bounds]: For example, the [Latticed k-induction paper](https://link.springer.com/chapter/10.1007/978-3-030-81688-9_25) defines and interprets latticed $k$-induction only for upper bounds on least fixed-point semantics.

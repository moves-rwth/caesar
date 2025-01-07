---
title: Procedures
description: Procedures are HeyVL's logical units of code.
sidebar_position: 1
---

# Procedures and Coprocedures

HeyVL [statements](statements.md) are placed inside the body of _(co)procedures_ or _(co)procs_ for short.
A *procedure* has a name, a list of parameters, a list of return values, and a list of specification attributes.
Caesar tries to verify each procedure in the given HeyVL files using the specification.
*Coprocedures* are like procedures, but the specification is interpreted differently (see below).

Procedures can be [called inside other procedures](#calling-procedures).
This enables modular reasoning about code: Prove that some code satisfies the specification once, and then use the specification when at the call site - without reasoning about the procedure's body again.

There are also [procedures without an associated body](#procs-without-body).
They are not verified by Caesar, but can be called inside other procedures.

## Procs by Example: Increment With 50% Probability

The following procedure named `maybe_increment` increments the value of the input parameter `init_x` by one with probability 50% and leaves it unchanged with 50% probability, returning the result in output parameter `x`.

```heyvl
proc maybe_increment(init_x: UInt) -> (x: UInt)
    pre init_x + 0.5
    post x
{
    x = init_x
    var prob_choice: Bool = flip(0.5)
    if prob_choice {
        x = x + 1
    } else {}
}
```

Verifying this proc checks the following equation:
$$
    \underbrace{\mathtt{init\_x} + 0.5}_\texttt{pre} \quad\underbrace{\leq}_\texttt{proc}\quad \underbrace{\mathbb{E}}_\text{body}(\underbrace{\mathtt{x}}_\texttt{post})~.
$$

Let us decompose the example into its parts:

 1. **Keyword `proc`**: We verify that $\mathtt{init\_x} + 0.5 \leq \mathbb{E}(\mathtt{x})$ holds, i.e. the expected value of `x` after executing `maybe_increment` is at least `init_x + 0.5`.
    - If we used the `coproc` keyword instead, we would verify $\mathtt{init\_x} + 0.5 \geq \mathbb{E}(\mathtt{x})$ (*upper* instead of *lower* bounds).
 2. We have one **input parameter** `init_x` of type [`UInt`](../stdlib/numbers.md#uint).
    - Input parameters may not be modified in the program.
 3. We have one **output parameter** `x` of type [`UInt`](../stdlib/numbers.md#uint).
    - There may be multiple parameters (input and output), which can be separated by commas (e.g. `init_x: UInt, init_y: UInt`).
 4. The `pre` declares the **pre-expectation** `init_x + 0.5`. It is evaluated in the *initial state* (when calling the proc). This is why it is called "pre" (= before running the proc).
 5. The `post` is the **post-expectation** `x` and evaluated in the final states of the proc (post = after running the proc). We always compare its expected value against the pre.
 6. The **body of the proc** assigns `init_x` to `x`. We then do a [probabilistic coin flip](../stdlib/distributions.md#symbolic-with-probabilities) and assign `true` to `prob_choice` with probability `0.5` (and `false` with probability `0.5`). It determines the expected value ($\mathbb{E}$) we look at.
    - See [documentation on statements](./statements.md) for more information.
    - [The body is optional](#procs-without-body).

Different specifications yield different results.
Remember that we have $\mathbb{E}(\mathtt{x}) = \mathtt{init\_x} + 0.5$.

| Kind | Pre | Post | Verifies? | Explanation
| ---- | --- | ---- | --------- | -----------
| `proc` | `init_x + 0.4` | `x` | Yes | $\mathtt{init\_x} + 0.4 \leq \mathbb{E}(\mathtt{x})$. |
| `proc` | `init_x + 0.6` | `x` | No | $\mathtt{init\_x} + 0.6 \not\leq \mathbb{E}(\mathtt{x})$. |
| `coproc` | `init_x + 0.6` | `x` | Yes | $\mathtt{init\_x} + 0.6 \geq \mathbb{E}(\mathtt{x})$. |
| `coproc` | `init_x + 0.4` | `x` | No | $\mathtt{init\_x} + 0.4 \not\geq \mathbb{E}(\mathtt{x})$. |

## Writing Specifications

The specifications in HeyVL follow the *probabilistic predicate transformer* paradigm.
Caesar transforms a *post* backwards through the program to compute its expected value.
The result is then checked against the *pre*, for each possible initial state.

There is an inductive definition on the [statements documentation page](./statements.md) for the *verification pre-expectation transformer* $\mathrm{vp}\llbracket{}S\rrbracket(\varphi)$ that Caesar uses to compute the expected value of the post $\varphi$ after running statements $S$.
However, for now it is sufficient to think of expected values as they intuitively are.

### The Specification Type: `EUReal` for Quantitative Reasoning

In HeyVL, the `pre` and `post` expressions have type [`EUReal`](../stdlib/numbers.md#eureal), i.e. non-negative real numbers or infinity.
We have $\texttt{EUReal} = \set{ x \in \mathbb{R} \mid x \geq 0 } \cup \set{ \infty }$.

This allows us to reason about various kinds expected values of probabilistic programs.
However, all of these expected values are limited to non-negative values.
This is seldom a practical limitation.[^on-negative-numbers]

HeyVL supports the syntax of the [*relatively complete assertion language* by Batz et al](https://doi.org/10.1145/3434320).
This means we can express practically all expected values of interest in our syntax.
For more information, read the [Caesar documentation on relative completeness](./expressions.md#relative-completeness).

### Embedding Boolean Specifications

The $\mathrm{vp}$ semantics of HeyVL is a generalization of classical (Boolean) predicate transformer reasonining as found in verifiers such as [Dafny](https://dafny.org/).
The Boolean reasoning can be fully embedded into our quantitative setting.

The [*embed expression*](./expressions.md) `?(b)` takes a Boolean expression `b` and maps it to $\infty$ if `b` evaluates to true in the current state.
Otherwise, `?(b)` evaluates to $0$.

The following procedure named `forty_two` accepts a single parameter, `x` of type `UInt` and returns a value `y` of type `UInt`.
The procedure has a body with just a single assignment statement that increments `x` by 1 and saves the result in `y`.

```heyvl
proc forty_two(x: UInt) -> (y: UInt)
    pre ?(x == 41)
    post ?(y == 42)
{
    y = x + 1
}
```

The `proc` verifies that `y == 42` holds after all executions (`post`) when we started in a state that satisfied `x == 41` (`pre`).

Why do the semantics work out so neatly?
Let's examine the semantics manually to see how it works.
Recall that the [verification pre-expectation transformer](./statements.md#semantics) $\mathrm{vp}\llbracket{S}\rrbracket(\varphi)$ in effect computes the expected value $\mathbb{E}(\varphi)$ of $\varphi$ after running statement $S$.
$$
\newcommand{\embed}[1]{\mathrm{?}({#1})}
\begin{align*}
    && \embed{x = 41} &\quad\leq\quad \mathrm{vp}\llbracket{S}\rrbracket(\embed{y = 42}) \tag{the specification} \\
    \text{iff}\quad && \embed{x = 41} &\quad\leq\quad \embed{y = x + 1} \tag{$\mathrm{vp}$ semantics} \\
    \clap{\text{Assume $x = 41$ holds, then we have $\embed{x = 41} = \infty$ and thus:}} \\
    \text{iff}\quad && \infty &\quad\leq\quad \embed{y = x + 1} \tag{$\mathrm{vp}$ semantics} \\
    \text{iff}\quad && \infty &\quad=\quad \embed{y = x + 1} \tag{$\embed{b} \in \set{0, \infty}$} \\
    \text{iff}\quad && \clap{y = x + 1} \tag{$\mathrm{vp}$ semantics} \\
    \text{iff}\quad && \clap{y = 42} \tag{assumption $x = 41$} \\
    \clap{\text{Assume $x = 41$ does not hold, then we have $\embed{x = 41} = 0$ and thus:}} \\
    \text{iff}\quad && 0 &\quad\leq\quad \embed{y = x + 1} \tag{$\mathrm{vp}$ semantics} \\
    \text{iff}\quad && \mathrm{true}
\end{align*}
$$

So if we assume $x = 41$ holds in the beginning, then we know that $y = 42$ holds afterwards.
If we assume $x \neq 41$, then we know nothing ($\mathrm{true}$) about the final state.

In short: we can use embed expressions `?(b)` to write Boolean assumptions in the `pre` and Boolean assertions in the `post`.

### Embedding Boolean Specifications in Coprocedures

The same kind of reasoning for embedding Boolean specifications applies to coprocedures.
However, there is one thing to be careful about: We usually need to *negate* the Boolean specification to obtain the "intuitive" result.

**TLDR:** In coprocedures, you'll usually want to use `!?(b)` instead of `?(b)`.

#### Accidental Incorrectness Reasoning

Consider the following modified example which *always* assigns `y = 42`.

```heyvl
coproc forty_two_upper(x: UInt) -> (y: UInt)
    pre ?(x == 41)
    post ?(y == 42)
{
    y = 42
}
```

This will **not verify** because it actually checks $\texttt{?}(x = 41) \geq \mathrm{vp}\llbracket{S}\rrbracket(\texttt{?}(y = 42))$, which is equivalent to $(42 = 42) \Rightarrow (x = 41)$, i.e. the only way the coprocedure does **not** verify is if there is an initial state satisfying $42 = 42$ such that $x = 41$ does not hold.
But since *all* states satisfy $42 = 42$, e.g. the initial state $x = 0$ is a counter-example to verification.

One can understand this as an instance of *Reverse Hoare Logic* or *(Partial) Incorrectness Reasoning*, i.e. asking a question of the form: "Do all initial states that *reach* $y = 42$ satisfy $x = 41$?".

<details>
    <summary>How To: Obtaining the above formula via <code>caesar --print-theorem --no-slice-error</code>.</summary>

    Using the <code>--print-theorem</code> command-line flag, you can print the theorem Caesar tries to prove about your (co)procedures. The result will have some optimizations applied, but it might be helpful to understand what exactly is being verified.
    We recommend adding the <code>--no-slice-error</code> flag to obtain a simpler version that is not cluttered with stuff from slicing for error messages.
</details>

#### Usually You Want `!?(b)` {#usually-you-want-coembed}

We often write `!?(b)` to abbreviate `?(!(b))`, i.e. mapping `b` to $0$ if it is true and to $\infty$ otherwise.[^bang-question-operator]

```heyvl
coproc forty_two_upper2(x: UInt) -> (y: UInt)
    pre !?(x == 41)
    post !?(y == 42)
{
    y = 42
}
```

In this example, the `pre` works as expected.
It tells the verifier to verify only from initial states that satisfy $x = 41$.
And the `post` encodes that we reach $y = 42$ &mdash; the set of initial states that reach $y \neq 42$ contains only states that satisfy $x \neq 41$.

### Multiple Or No `pre`/`post` Annotations

Multiple `pre` and `post` annotations are logically combined.[^spec-combination]
`⊓` is the minimum operator and `⊔` maximum operator (see [expressions documentation](./expressions.md)).

| | `pre A pre B` | `post C post D` |
|- | - | - |
| `proc` | `pre (A ⊓ B)` | `post (C ⊓ D)` |
| `coproc` | `pre (A ⊔ B)` | `post (C ⊔ D)` |

In `proc`s, we combine `pre`s and `post`s with the minimum `⊓`.
In `coproc`s, the combination is dual and uses the maximum `⊔`.

This generalizes the Boolean setting neatly:

| | `pre ?(A) pre ?(B)` | `post ?(C) post ?(D)` |
|- | - | - |
| `proc` | `pre ?(A && B)` | `post ?(C && D)` |
| `coproc` | `pre ?(A \|\| B)` | `post ?(C \|\| D)` |

If [we use `!?(b)` in `coproc`s](#usually-you-want-coembed), then we obtain that `pre !?(A) pre !?(B)` is equivalent to `pre !?(A && B)` as one might expect.
Same for `post` annotations.

The specification is optional; if it's not provided, Caesar will add a default specification: `pre ?(true)` and `post ?(true)` for procedures and `pre ?(false)` and `post ?(false)` for coprocedures.

The defaults correspond to the empty conjunction ($\bigwedge \emptyset = \mathrm{true}$) and empty disjunction ($\bigvee \emptyset = \mathrm{false}$).
The quantitative setting behaves the same, we have $\inf \emptyset = \infty$ and $\sup \emptyset = 0$.

### Procedures Without a Body {#procs-without-body}

Procedures and coprocedures can be written without a corresponding body.
This allows us to _[program from specifications](https://www.cs.ox.ac.uk/publications/books/PfS/)_, i.e. write and verify programs incrementally.
We can start with a specification and step-by-step fill in executable code (or just don't if we don't feel like it).

Since [procedure calls only need the callee specification](#calling-procedures), we can just write a procedure specification and use it in other places.
There does not need to be procedure body of the callee at all.

This can be used to introduce unsoundness even without using [`assume` statements](./statements.md#assert-and-assume).
Calling the following procedure is essentially the same as writing `assume ?(false)`.
```heyvl
proc unsound() -> ()
    pre ?(true)
    post ?(false)
```


## Calling Procedures

We can call `proc`s from `proc`s and `coproc`s from `coproc`s.
Mixing both is unsound and will result in an error.
In the following, we will talk about procedures, but everything applies to coprocedures as well.

Procedure calls make use of the procedure's specification *only* and do not inspect the procedure body.
Somewhat informally, we could say that *assuming* the callee procedure verifies, the procedure call can be replaced by the procedure's body and the program will still verify.
This enables modular reasoning: one can verify a big program and we can re-use already-verified parts of it in other parts.

### Example: A Spare Engine

The following example models running an engine with a spare engine available.
In `runPrimaryOrSpare`, the primary engine works with probability of 90%.
If it fails, we have another spare available that is guaranteed to work with the same probability.

```heyvl
proc spare() -> (working: Bool)
    pre 0.9
    post [working]
{
    working = flip(0.95)
}

proc runPrimaryOrSpare() -> (working: Bool)
    pre 0.99
    post [working]
{
    working = flip(0.9)
    if !working {
        working = spare()
    } else {}
}
```

The specification of `spare` says `working` is true with probability of at least `0.9` (and in fact the coin flip says it is `0.95`).
Thus, we can verify a success probability of `runOrSpare` of at least `0.99`.
However, we cannot verify a lower bound of `0.995` because the specification of `spare` does not guarantee it (even though it is true here).

### Multiple Or No Return Values

If the callee has multiple return values, multiple variables may be assigned to by comma-separating them.
For example, if `spare` returned two variables, we could obtain the results via `working1, working2 = spare()`.

If the callee has no return values, we just call it without the assignment.
For example, we simply write `spare()` as a statement to call it without assignment.

### Assert-Assume Understanding of Procedure Calls

Internally, procedure calls are translated to HeyVL verification statements (see [statements documentation](./statements.md)).
We can understand how procedure calls work by understanding this encoding.

During the verification of `runPrimaryOrSpare`, we replace the call to `spare` by a sequence of `assert`, `havoc,` `validate`, and `assume` statements.
```heyvl
proc runPrimaryOrSpare() -> (working: Bool)
    pre 0.99
    post [working]
{
    working = flip(0.9)
    if !working {
        assert 0.95
        havoc success
        validate
        assume [success]
    } else {}
}
```

<details>
    <summary>How To: Obtaining intermediate encodings via <code>caesar --print-core</code>.</summary>

    To obtain the intermediate encodings from Caesar, we can use the <code>--print-core</code> command-line flag.
    This will print the fully desugared HeyVL code for each procedure to standard output.
</details>

We can now read the encoding as follows:
 1. Before the call, `assert` the `pre` `spare()`. This means that the expected value (going backwards) is at most `0.95`.
 2. We then forget the current value of `success` via `havoc`. This models that `spare` can have arbitrary effects on return values.
 3. We `validate` (the following assumption must be absolutely true).
 4. We can only `assume` the `post` of `spare`, i.e. that `success` is true.

This generalizes the Boolean setting:
 1. Before the call, the `pre` must hold.
 2. Forget the current value of modified variables.
 3. (The `validate` does not have any effect in the Boolean setting.)
 4. Assume that the `post` holds after the call.

A more formal treatment of the encoding and semantics of procedure calls can be found in our [OOPSLA '23 paper](../publications.md#oopsla-23).



[^spec-combination]: The combination of specifications is a logical consequence of their encodings in HeyVL. When *verifying* a procedure, `pre` annotations will be translated to `assume` and `post` annotations will be translated to `assert` statements.
One can prove that the HeyVL statements `assume A1; assume A2` are equivalent to `assume (A1 ⊓ A2)`, and also that the sequence `assert A1; assert A2` is equivalent to `assert (A1 ⊓ A2)`.
The same equalities can be used for the procedure *call* encoding.

[^on-negative-numbers]: Many verification tasks that require reasoning with negative numbers can be embedded in this framework. First, note that we can still have negative numbers in our program states, we just have to ensure that the `post` is non-negative. [Chapter 11 of the paper _"Relatively Complete Verification for Probabilistic Programs"_](https://dl.acm.org/doi/pdf/10.1145/3434320#page=24) by Batz et al. might be of interest for further reading.

[^bang-question-operator]: `!?(b)` is not a special kind of operator, it is simply the `!` operator applied to `?(b)`, i.e. `!(?(b))`.
The negation operator `!` is defined on `EUReal` by $!0 = \infty$ and $!x = 0$ for all $x \neq 0$.
Thus, `!?(b)` is logically equivalent to `?(!b)`.
In the [OOPSLA '23 paper](../publications.md#oopsla-23), we denoted `!?(b)` by $\mathrm{co?}(b)$.

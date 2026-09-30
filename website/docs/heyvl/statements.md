---
description: HeyVL statement syntax, program behavior, and quantitative verification semantics.
sidebar_position: 2
---

# Statements

```mdx-code-block
import styles from './statements.module.css';
```

<div className={styles.reference}>

HeyVL statements describe programs and proofs inside [procedure bodies](./procs.md).

<div className={styles.overview}>
<div>

Program statements

- [Blocks](#blocks) · [Variables](#variable-declarations)
- [Assignments and calls](#assignments)
- [Boolean choices](#boolean-choices) · [Nondeterministic choices](#nondeterministic-choices)
- [While loops](#while-loops) · [Sampling and weights](#sampling-and-weights)
- [Rewards](#reward-and-weigh) · [Weights](#weigh)

</div>
<div>

Proofs and semantics

- [Assertions](#assert-and-assume)
- [Assumptions](#assumptions)
- [Havoc](#havoc)
- [Validations](#validations)
- [Verification conditions](#semantics)
- [Game semantics](#game-semantics)
- [Legacy statements](#deprecated-statements)

</div>
</div>

## Concrete Statements

### Blocks

<div className={styles.syntax}>

A block is a sequence of statements enclosed by curly braces.

```heyvl
{ ... }
```

</div>

Variables declared inside a block are local to it.
Assignments to outer variables remain visible afterwards:

```heyvl
var x: UInt = 1
{
    var y: UInt = 2
    x = x + y
}
// x is now 3
// y is no longer in scope
```

Blocks can be nested, and an empty block `{}` has no effect.
Semicolons between statements are optional.

### Variable Declarations

<div className={styles.syntax}>

Declare a variable with its type and an optional initial value.

```heyvl
var x: T
var x: T = e
```

</div>

`var count: UInt = 0` declares an unsigned integer with initial value `0`.
Without an initializer, verification considers every possible value of the variable's type.
See the [standard library](../stdlib/) for built-in types and [domains](./domains.md) for user-defined types.

### Assignments and Procedure Calls {#assignments}

<div className={styles.syntax}>

An assignment stores the value of an expression in a variable.

```heyvl
x = e
```

</div>

`x = 39 + y` updates `x` using the current value of `y`.
Assignments can update local variables and output parameters.
Input parameters are immutable.
The assigned value must have a compatible type.

<div className={styles.syntax}>

A [distribution call](../stdlib/distributions.md) samples a random value.
HeyVL provides Bernoulli, uniform, binomial, and hypergeometric distributions.

```heyvl
x = flip(p)
x = ber(pa, pb)
x = unif(a, b)
x = binom(n, pa, pb)
x = hyper(N, k, n)
```

</div>

`var b: Bool = flip(0.5)` assigns `true` or `false` with equal probability.
Distribution calls must appear directly on the right-hand side of an assignment or initializer.
`flip` accepts symbolic arguments.
The other distributions require numeric literals.

<div className={styles.syntax}>

A [procedure call](./procs.md#calling-procedures) assigns its outputs to a list of variables.

```heyvl
x, y = p(args)
p(args)
```

</div>

A call with no outputs stands alone.
Caesar verifies calls against the callee's specification.

### Boolean Choices

<div className={styles.syntax}>

An `if` executes one of two blocks according to a Boolean condition.

```heyvl
if b { ... } else { ... }
```

</div>

This decrements `x` if it is positive:

```heyvl
if x > 0 {
    x = x - 1
} else {}
```

The `else` block is required, but may be empty.

### While Loops

<div className={styles.syntax}>

HeyVL supports while loops that run a block of code while a condition evaluates to true.

```heyvl
while b { ... }
```

</div>

For example, keep flipping a coin until it returns `false`:

```heyvl
var cont: Bool = true
@invariant(...)
while cont {
    cont = flip(0.5)
}
```

For verification, while loops need [proof-rule annotations](../proof-rules/) such as the [`@invariant(...)` annotation](../proof-rules/induction.md) in the example.
If a while loop does not have a proof-rule annotation, Caesar cannot verify the program and will show an error.

Proof-rule annotations also determine whether the loop has least or greatest fixpoint semantics.
Use [calculus annotations](../proof-rules/approximations.md#calculus-annotations) on procedures to make this choice explicit.

With the [model-checking translation](../model-checking.md), proof-rule annotations are not necessary.
It supports probabilistic model checkers such as [Storm](https://www.stormchecker.org/) for a subset of HeyVL programs.
You can use these to get an initial estimate of expected values.

### Rewards {#reward-and-weigh}

<div className={styles.syntax}>

`reward` adds a reward, such as elapsed time or resource consumption.

```heyvl
reward e
```

</div>

The reward `e` must be non-negative.
`tick e` is an alias.
Rewards accumulate along an execution.
With `post 0`, `reward 2; reward 3` has total reward $5$.
A nonzero `post` adds a final reward.

### Weights {#weigh}

<div className={styles.syntax}>

`weigh` multiplies the remaining program's contribution by a weight.

```heyvl
weigh e
```

</div>

The weight `e` must be non-negative.
For example, `weigh 0.5; reward 2` contributes $1$ with `post 0`, while `reward 2; weigh 0.5` contributes $2$.

Combine `weigh` with additive choice `if +` to weight each branch and sum the results.
The [example below](#sampling-and-weights) uses this to express a probabilistic choice.

### Nondeterministic Choices

<div className={styles.syntax}>

Demonic choice `if ⊓` minimizes the expected outcome.
Angelic choice `if ⊔` maximizes it.
Additive choice `if +` sums the contributions of both branches.

```heyvl
if ⊓ { ... } else { ... }
if ⊔ { ... } else { ... }
if + { ... } else { ... }
```

</div>

For example, choose between two rewards:

```heyvl
if ⊓ {
    reward 2
} else {
    reward 6
}
```

With `post 0`, changing the choice operator gives:

<dl className={styles.rules}>

<dt><code>if ⊓</code></dt>
<dd>

$2$, the smaller reward.

</dd>

<dt><code>if ⊔</code></dt>
<dd>

$6$, the larger reward.

</dd>

<dt><code>if +</code></dt>
<dd>

$8$, the sum of both rewards.

</dd>

</dl>

A fair probabilistic choice between these rewards has expectation $4$.
The [example below](#sampling-and-weights) expresses it with sampling and a Boolean `if`.
For ASCII spellings, use `\cap` for `⊓`, `\cup` for `⊔`, and `\oplus` for `+`.
Additive choice also accepts `⊕`.

<details id="sampling-and-weights">
<summary id="examples">Probabilistic choice, using sampling or weights</summary>

The comments show the expected reward from each point onward.

```heyvl
coproc expected_reward() -> ()
    pre 4
    post 0
{
    // 4
    var b: Bool = flip(0.5)
    // ite(b, 2, 6)
    if b {
        // 2
        reward 2
    } else {
        // 6
        reward 6
    }
}
```

This verifies because the expected reward is $\tfrac12\cdot2+\tfrac12\cdot6=4$.
Replacing `coproc` by `proc` verifies the matching lower bound.
An upper bound of `3` or a lower bound of `5` fails verification.

Weights and additive choice give the same result:

```heyvl
// 4
if + {
    // 1
    weigh 0.5
    // 2
    reward 2
} else {
    // 3
    weigh 0.5
    // 6
    reward 6
}
```

Each branch contributes half its value, so the sum is again $4$ with `post 0`.

</details>

## Verification Statements

Verification statements express conditions to prove, assumptions to use, and changes to the proof state.
Each verification statement has a dual with a `co` prefix, such as `assert` and `coassert`.
Both forms can occur in a `proc` or `coproc`.

These statements have quantitative semantics.
We introduce common Boolean uses first for intuition, then give the general quantitative rules.

Caesar's [proof rules](../proof-rules/) generate these statements for supported proof techniques.

### Verification Conditions {#semantics}

An *expectation* assigns a non-negative number or $\infty$ to each program state.
Starting from `post`, Caesar works backwards through the body to compute a *verification pre-expectation*.
We write $\mathrm{vp}\llbracket S\rrbracket(f)$ for the result before statement $S$, where $f$ is the expectation for the remaining code.
All operations on expectations below are pointwise.
For a whole procedure body $S$, the *verification condition* (VC) compares this result with `pre` in every initial state:

<dl className={styles.rules}>

<dt><code>proc</code></dt>
<dd>

$\mathrm{pre} \leq \mathrm{vp}\llbracket S\rrbracket(\mathrm{post})$ (lower bound).

</dd>

<dt><code>coproc</code></dt>
<dd>

$\mathrm{pre} \geq \mathrm{vp}\llbracket S\rrbracket(\mathrm{post})$ (upper bound).

</dd>

</dl>

A smaller pre-expectation can make a lower-bound proof harder and an upper-bound proof easier.
Probabilistic failures can involve several statements across multiple paths.
See the [slicing guide](../caesar/slicing.md#assertion-slicing) for how to diagnose them.

The [VS Code extension](../caesar/vscode-and-lsp.md#features) can show pre-expectations inline with the command *Caesar: Explain Verification Condition Generation*.

<details id="transformer-rules">
<summary>Rules for program statements</summary>

Sequential composition works backwards:

$$
\mathrm{vp}\llbracket S_1; S_2\rrbracket(f)
= \mathrm{vp}\llbracket S_1\rrbracket\bigl(\mathrm{vp}\llbracket S_2\rrbracket(f)\bigr).
$$

An empty block leaves $f$ unchanged.
For a choice with branches $S_1,S_2$, write $f_i=\mathrm{vp}\llbracket S_i\rrbracket(f)$.
Each line gives $\mathrm{vp}\llbracket S\rrbracket(f)$ for the indicated statement.

<dl className={styles.rules}>

<dt><code>x = e</code></dt>
<dd>

$f[x\mapsto e]$

</dd>

<dt><code>x = flip(p)</code></dt>
<dd>

$p\,f[x\mapsto\mathrm{true}]+(1-p)\,f[x\mapsto\mathrm{false}]$, for $0\leq p\leq1$.

</dd>

<dt><code>if b</code></dt>
<dd>

$\operatorname{ite}(b,f_1,f_2)$

</dd>

<dt><code>if ⊓</code></dt>
<dd>

$\min(f_1,f_2)$

</dd>

<dt><code>if ⊔</code></dt>
<dd>

$\max(f_1,f_2)$

</dd>

<dt><code>if +</code></dt>
<dd>

$f_1+f_2$

</dd>

<dt><code>reward e</code></dt>
<dd>

$e+f$

</dd>

<dt><code>weigh e</code></dt>
<dd>

$e\cdot f$, with $0\cdot\infty=0$.

</dd>

</dl>

</details>

### Assertions {#assert-and-assume}

<div className={styles.syntax}>
<span className={styles.syntaxTag}>Boolean</span>

Add a condition that the proof must establish at this point.
The usual forms are `assert` in a `proc` and `coassert` in a `coproc`.

```heyvl
assert ?(b)
coassert !?(b)
```

</div>

For example, `assert ?(x >= 1)` adds the obligation that `x` is at least $1$.
In a `coproc`, write `coassert !?(x >= 1)` for the same Boolean condition.

Assertions also accept a quantitative expectation `e`.

<div className={styles.syntax}>
<span className={styles.syntaxTag}>Quantitative</span>

`assert` chooses demonically whether to stop and collect `e` or continue with the remaining program.
`coassert` makes this choice angelically.

```heyvl
assert e
coassert e
```

</div>

`e` has type `EUReal`.

<div className={styles.dualRules}>
<div>

$\mathrm{vp}\llbracket\texttt{assert }e\rrbracket(f)=\min(e,f)$

</div>
<div>

$\mathrm{vp}\llbracket\texttt{coassert }e\rrbracket(f)=\max(e,f)$

</div>
</div>

The Boolean forms above use these same rules, with the embeddings `?(b)` or `!?(b)` as `e`.
`?(b)` is $\infty$ when `b` holds and $0$ otherwise.
`!?(b)` is $0$ when `b` holds and $\infty$ otherwise.
When `b` holds, both forms leave $f$ unchanged.
Otherwise, `assert ?(b)` gives $0$ and `coassert !?(b)` gives $\infty$, matching the [bound direction of the proof](./procs.md#usually-you-want-coembed).

The [Iverson bracket](./expressions.md) `[b]` takes values $1$ and $0$ instead, for reasoning about probabilities.

### Assumptions {#assumptions}

<div className={styles.syntax}>
<span className={styles.syntaxTag}>Boolean</span>

Assume a condition holds at this point in the proof.
The usual forms are `assume` in a `proc` and `coassume` in a `coproc`.

```heyvl
assume ?(b)
coassume !?(b)
```

</div>

For example, with `x: UInt`, this fragment uses `x > 0` to prove `x >= 1`:

```heyvl
assume ?(x > 0)
assert ?(x >= 1)
```

In a `coproc`, use `coassume !?(x > 0)` followed by `coassert !?(x >= 1)`.
Caesar uses the assumed condition without proving it.
Proof encodings use assumptions to record branch conditions, loop invariants, and procedure specifications.

Assumptions also accept a quantitative expectation `e`.

<div className={styles.syntax}>
<span className={styles.syntaxTag}>Quantitative</span>

If the remaining expectation is at least `e`, `assume` makes a lower-bound goal trivial.
`coassume` does the same for an upper-bound goal when the expectation is at most `e`.

```heyvl
assume e
coassume e
```

</div>

<div className={styles.dualRules}>
<div>

$\mathrm{vp}\llbracket\texttt{assume }e\rrbracket(f)=\begin{cases}\infty & e\leq f\\f & e>f\end{cases}$

</div>
<div>

$\mathrm{vp}\llbracket\texttt{coassume }e\rrbracket(f)=\begin{cases}0 & f\leq e\\f & f>e\end{cases}$

</div>
</div>

The Boolean forms use these same rules with the embeddings `?(b)` and `!?(b)`.
When `b` holds, both leave $f$ unchanged.
Otherwise, `assume ?(b)` gives $\infty$ and `coassume !?(b)` gives $0$.

<div className={styles.detailsGroup}>

<details>
<summary>Proving an assertion from an assumption</summary>

```heyvl
proc positive_integer(x: UInt) -> ()
    pre \infty
    post \infty
{
    // \infty
    assume ?(x > 0)
    // ?(x >= 1)
    assert ?(x >= 1)
}
```

The comments show the pre-expectation immediately before each statement.
The assertion requires `x >= 1`, which follows from the assumption `x > 0`.
The resulting pre-expectation is $\infty$ in every initial state, so the procedure verifies.
The dual proof uses $0$ to represent a satisfied obligation:

```heyvl
coproc positive_integer_dual(x: UInt) -> ()
    pre 0
    post 0
{
    // 0
    coassume !?(x > 0)
    // !?(x >= 1)
    coassert !?(x >= 1)
}
```

Removing the assumption makes either proof fail at `x = 0`.

</details>

<details>
<summary>Ending a proof branch</summary>

For an expectation `I`, this fragment has verification pre-expectation exactly $I$, whatever follows it:

```heyvl
// I
assert I
// \infty
assume 0
```

Reading backwards, `assume 0` transforms any continuation into $\infty$, and `assert I` then yields $\min(I,\infty)=I$.
Proof-rule encodings use this to finish a branch after introducing its obligation.
The dual fragment is:

```heyvl
// I
coassert I
// 0
coassume \infty
```

`coassume` makes the continuation $0$, and `coassert I` gives $\max(I,0)=I$.
For complete encodings, see [procedure calls](./procs.md#assert-assume-understanding-of-procedure-calls) and [Park induction](../proof-rules/induction.md#internal-details).

</details>

</div>

### Havoc

<div className={styles.syntax}>

Forget the current values of variables and choose replacements.
The choice is demonic for `havoc` and angelic for `cohavoc`.

```heyvl
havoc x, ...
cohavoc x, ...
```

</div>

To prove a Boolean property for every replacement value, the usual pattern uses `havoc` in a `proc` or `cohavoc` in a `coproc`.
For example, after forgetting the value of a local `x: UInt`, assume it is positive:

```heyvl
havoc x
assume ?(x > 0)
assert ?(x >= 1)
```

The proof now concerns an arbitrary positive integer, regardless of the earlier value of `x`.
Loop proofs use this pattern to forget values from earlier iterations and then assume the loop invariant.
Procedure-call encodings use it to forget the previous values of output variables.

Both statements accept local variables and output parameters.

<div className={styles.dualRules}>
<div>

$\mathrm{vp}\llbracket\texttt{havoc }x\rrbracket(f)=\inf_{v\in\mathrm{Type}(x)} f[x\mapsto v]$

</div>
<div>

$\mathrm{vp}\llbracket\texttt{cohavoc }x\rrbracket(f)=\sup_{v\in\mathrm{Type}(x)} f[x\mapsto v]$

</div>
</div>

### Validations {#validations}

<div className={styles.syntax}>

Turn the remaining expectation into a Boolean proof obligation.

```heyvl
validate
covalidate
```

</div>

Validation leaves Boolean obligations unchanged: values $0$ and $\infty$ stay as they are.

<div className={styles.dualRules}>
<div>

$\mathrm{vp}\llbracket\texttt{validate}\rrbracket(f)=\begin{cases}\infty & f=\infty\\0 & f<\infty\end{cases}$

</div>
<div>

$\mathrm{vp}\llbracket\texttt{covalidate}\rrbracket(f)=\begin{cases}0 & f=0\\\infty & f>0\end{cases}$

</div>
</div>

`validate; assume 2` checks whether the expectation of the following code is at least $2$.
This example fails because its `post 1` is below that bound:

```heyvl
proc require_two() -> ()
    pre 1
    post 1
{
    // 0
    validate
    // 1
    assume 2
}
```

Without `validate`, the computed pre-expectation would be $1$, so `pre 1` would verify.
`validate` turns that value into $0$, making the check $1\leq0$ fail.
With `post 3`, `assume 2` produces $\infty$, which `validate` preserves, so the procedure verifies.

`validate; assume I` returns $?(I \leq f)$.
Its dual `covalidate; coassume I` returns $!?(f \leq I)$.

<details>
<summary>Combining assert, havoc, and assume</summary>

This procedure combines all four statements to verify `pre 1`:

```heyvl
proc check_bound() -> (x: UInt)
    pre 1
    post x + 2
{
    // 1
    assert 1
    // \infty
    havoc x
    // \infty
    validate
    // \infty
    assume x + 2
}
```

Reading backwards, `assume x + 2` compares $x+2$ with the `post`, and `validate` turns the result into $0$ or $\infty$.
`havoc x` checks the comparison for every replacement value of `x`, giving $\infty$ here.
`assert 1` then gives $\min(1,\infty)=1$.

With `post x + 1`, the comparison fails for every `x`.
Validation then gives $0$, so the proof fails.
Without `validate`, the failed comparisons would leave $x+1$.
`havoc` would give $\inf_{x\in\mathbb{N}}(x+1)=1$, so the procedure would still verify.

In general, `assert P; havoc x; validate; assume Q` gives $P$ if $Q\leq f$ holds for every replacement value of `x`, and $0$ otherwise.
Replacing all four statements with their `co` forms gives $P$ if $f\leq Q$ holds for every replacement value, and $\infty$ otherwise.
In both cases, $P$ is evaluated before forgetting `x`.
This pattern appears in [procedure-call encodings](./procs.md#assert-assume-understanding-of-procedure-calls) and [loop-invariant proofs](../proof-rules/induction.md#heyvl-encoding).

</details>

## Game Semantics {#game-semantics}

HeyVL programs describe a [game between two players](../publications.md#aisola-24-a-game-based-semantics-for-the-probabilistic-intermediate-verification-language-heyvl): the *demonic* player minimizes expected reward, and the *angelic* player maximizes it.
For the core HeyVL language, the game's value is the [pre-expectation](#semantics) defined above.

**Programs and choices.**
A play follows assignments and sampling, collects `reward` values, and collects `post` on reaching the end.
The demonic player controls `if ⊓` and `havoc`, the angelic player `if ⊔` and `cohavoc`.
The *remaining game value* is the expected reward still to come, accounting for future random outcomes and both players' choices.

**Assertions.**
At `assert e`, the demonic player may stop for reward `e` or continue.
`coassert e` gives this choice to the angelic player.
Stopping keeps earlier rewards and replaces future rewards, including `post`.[^assertion-game]

**Assumptions.**
A referee evaluates this remaining game value.
For `assume e`, it ends play with reward $\infty$ when that value is at least `e`.
For `coassume e`, it ends play with reward $0$ when the value is at most `e`.
Otherwise, play continues.

**Validations.**
At `validate`, the referee lets play continue if the remaining value is $\infty$, and otherwise stops it with reward $0$.
At `covalidate`, it lets play continue if the remaining value is $0$, and otherwise stops it with reward $\infty$.

## Deprecated Statements

:::caution

The legacy `compare`, `cocompare`, `negate`, and `conegate` statements may be removed from Caesar.
Prefer the supported proof rules and procedure-call syntax when encoding proofs.

:::

### Compare

`compare f` is shorthand for `validate; assume f`.
Its dual `cocompare f` is shorthand for `covalidate; coassume f`.

<div className={styles.dualRules}>
<div>

$\mathrm{vp}\llbracket\texttt{compare }e\rrbracket(f)=\begin{cases}\infty & e\leq f\\0 & e>f\end{cases}$

</div>
<div>

$\mathrm{vp}\llbracket\texttt{cocompare }e\rrbracket(f)=\begin{cases}0 & f\leq e\\\infty & f>e\end{cases}$

</div>
</div>

### Negations

The `negate` and `conegate` statements apply HeyLo's negations.

`validate` is equivalent to `conegate; conegate`, and `covalidate` is equivalent to `negate; negate`.

<div className={styles.dualRules}>
<div>

$\mathrm{vp}\llbracket\texttt{negate}\rrbracket(f)=\begin{cases}\infty & f=0\\0 & f>0\end{cases}$

</div>
<div>

$\mathrm{vp}\llbracket\texttt{conegate}\rrbracket(f)=\begin{cases}0 & f=\infty\\\infty & f<\infty\end{cases}$

</div>
</div>

:::danger

Sound [(co)procedure calls](procs.md#calling-procedures) require _monotonicity_.
Negation statements can break this property and make calls unsound.

:::

</div>

## Further Reading

- [OOPSLA '23](../publications.md#oopsla-23): formal statement semantics and how `assert`, `havoc`, `validate`, and `assume` encode procedure calls.
- [CAV '26](../publications.md#cav-26-caesar-a-deductive-verifier-for-probabilistic-programs) ([PDF](https://link.springer.com/content/pdf/10.1007/978-3-032-32537-2_27.pdf?pdf=inline%20link)): how HeyVL proof encodings connect to Caesar's verification backends and editor support.
- [Weighted programming](https://arxiv.org/pdf/2608.18971): how `weigh` and additive choice express weighted programs beyond probabilities.
- [Game semantics (AISoLA '24)](../publications.md#aisola-24-a-game-based-semantics-for-the-probabilistic-intermediate-verification-language-heyvl): interpreting verification statements as a game between two players, with a referee for assumptions and validations.
- [Slicing (ESOP '26)](../publications.md#esop-26-error-localization-certificates-and-hints-for-probabilistic-program-verification-via-slicing): why a failed proof can involve several statements and paths, and how slicing finds them.

[^assertion-game]: The paper models assertions with referee decisions (Section 4.2, Table 1).
    Here we use an equivalent stop-or-continue choice.

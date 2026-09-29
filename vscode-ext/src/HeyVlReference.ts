/**
 * Concise summaries of the linked sections in website/docs, bundled for offline hovers.
 * Keep wording and examples aligned with those sections.
 */
export interface ReferenceEntry {
    readonly title: string;
    readonly description: string;
    readonly details?: string;
    readonly example?: string;
    readonly documentation: string;
}

const docs = "https://www.caesarverifier.org/docs/";
const expressions = `${docs}heyvl/expressions/`;
const statements = `${docs}heyvl/statements/`;
const procedures = `${docs}heyvl/procs/`;
const domains = `${docs}heyvl/domains/`;
const numbers = `${docs}stdlib/numbers/`;
const calculus = `${docs}proof-rules/approximations/#calculus-annotations`;

function aliases(spellings: readonly string[], entry: ReferenceEntry): Record<string, ReferenceEntry> {
    return Object.fromEntries(spellings.map(spelling => [spelling, entry]));
}

/** Keys are source spellings; compound choices use a single space after `if`. */
export const HEYVL_REFERENCE: Readonly<Record<string, ReferenceEntry>> = {
    domain: {
        title: "domain — uninterpreted type",
        description: "Groups related functions and axioms and introduces a new uninterpreted type.",
        details: "Values of the domain type support equality (`==`) and inequality (`!=`).",
        documentation: `${domains}#defining-types-with-domains`,
    },
    axiom: {
        title: "axiom — assumed fact",
        description: "Declares a named Boolean formula that Caesar assumes holds in all program states.",
        documentation: `${domains}#axioms`,
    },
    func: {
        title: "func — mathematical function",
        description: "Declares a function inside a domain, for use in expressions.",
        details: "A body after `=` defines the function's value; a function without a body is uninterpreted and can be specified by axioms.",
        example: "func double(x: UInt): UInt = 2 * x",
        documentation: `${domains}#definitional-functions`,
    },
    proc: {
        title: "proc — lower-bound specification",
        description: "Declares a procedure with input parameters, output parameters, and a quantitative specification.",
        details: "Verification transforms `post` backwards through the body and checks `pre ≤ vc[body](post)` in every initial state. " +
            "The `pre` therefore gives a lower bound on the resulting expectation.\n\n" +
            "**Specification details**\n\n" +
            "The `pre` is an `EUReal` expression over input parameters, evaluated in the initial state. " +
            "The `post` is an `EUReal` expression over input and output parameters, evaluated in the final state.\n\n" +
            "Multiple `pre` clauses combine by minimum (`⊓`), as do multiple `post` clauses. " +
            "For `pre A pre B` and `post C post D`, verification checks:\n\n" +
            "```text\n(A ⊓ B) ≤ vc[body](C ⊓ D)\n```\n\n" +
            "An omitted `pre` or `post` defaults to `∞`.\n\n" +
            "For Boolean conditions, use `pre ?(P)` and `post ?(Q)`. " +
            "Repeated clauses then combine their conditions by conjunction.",
        documentation: procedures,
    },
    coproc: {
        title: "coproc — upper-bound specification",
        description: "Declares a coprocedure with input parameters, output parameters, and a quantitative specification.",
        details: "Verification transforms `post` backwards through the body and checks `pre ≥ vc[body](post)` in every initial state. " +
            "The `pre` therefore gives an upper bound on the resulting expectation.\n\n" +
            "**Specification details**\n\n" +
            "The `pre` is an `EUReal` expression over input parameters, evaluated in the initial state. " +
            "The `post` is an `EUReal` expression over input and output parameters, evaluated in the final state.\n\n" +
            "Multiple `pre` clauses combine by maximum (`⊔`), as do multiple `post` clauses. " +
            "For `pre A pre B` and `post C post D`, verification checks:\n\n" +
            "```text\n(A ⊔ B) ≥ vc[body](C ⊔ D)\n```\n\n" +
            "An omitted `pre` or `post` defaults to `0`.\n\n" +
            "For Boolean conditions, use `pre !?(P)` and `post !?(Q)`. " +
            "Repeated clauses then combine their conditions by conjunction.",
        documentation: procedures,
    },
    pre: {
        title: "pre — pre-expectation",
        description: "Declares the procedure's pre-expectation: an `EUReal` expression over input parameters, evaluated in the initial state.",
        details: "Its value supplies the bound in the verification obligation:\n\n" +
            "```text\nproc:   pre ≤ vc[body](post)\ncoproc: pre ≥ vc[body](post)\n```\n\n" +
            "`vc[body]` denotes the body's verification pre-expectation transformer. " +
            "Multiple `pre` clauses combine by minimum in a `proc` and maximum in a `coproc`.\n\n" +
            "For a Boolean precondition `b`, use `pre ?(b)` in a `proc` and `pre !?(b)` in a `coproc`.",
        documentation: `${procedures}#writing-specifications`,
    },
    post: {
        title: "post — post-expectation",
        description: "Declares the procedure's post-expectation: an `EUReal` expression evaluated in the final state.",
        details: "It may reference input and output parameters. " +
            "Verification requires the following inequality in every initial state:\n\n" +
            "```text\nproc:   pre ≤ vc[body](post)\ncoproc: pre ≥ vc[body](post)\n```\n\n" +
            "`vc[body]` denotes the body's verification pre-expectation transformer. " +
            "Multiple `post` clauses combine by minimum in a `proc` and maximum in a `coproc`.\n\n" +
            "For a Boolean postcondition `b`, use `post ?(b)` in a `proc` and `post !?(b)` in a `coproc`.",
        documentation: `${procedures}#writing-specifications`,
    },
    var: {
        title: "var — local variable",
        description: "Declares a typed variable in the current block, optionally initialized.",
        details: "An uninitialized variable ranges over all values of its type during verification.",
        example: "var count: UInt = 0",
        documentation: `${statements}#variable-declarations`,
    },
    if: {
        title: "if — conditional choice",
        description: "`if b { S } else { T }` executes `S` when the Boolean guard `b` is true and `T` when it is false.",
        documentation: `${statements}#boolean-choices`,
    },
    else: {
        title: "else — alternative branch",
        description: "Introduces the second branch of an `if` statement.",
        documentation: `${statements}#boolean-choices`,
    },
    while: {
        title: "while — loop",
        description: "Executes its body repeatedly while the Boolean guard holds.",
        details: "For deductive verification, a proof rule annotation such as `@invariant(I)` specifies how to verify the loop.",
        documentation: `${statements}#while-loops`,
    },
    assert: {
        title: "assert — quantitative assertion",
        description: "`assert e` takes the minimum of `e` and the current verification condition `f`: `e ⊓ f`.",
        details: "In a `proc`, use `assert ?(b)` for a Boolean assertion:\n\n" +
            "```text\nvc[assert ?(b)](f) = ite(b, f, 0)\n```",
        documentation: `${statements}#assert-and-assume`,
    },
    coassert: {
        title: "coassert — dual quantitative assertion",
        description: "`coassert e` takes the maximum of `e` and the current verification condition `f`: `e ⊔ f`.",
        details: "In a `coproc`, use `coassert !?(b)` for a Boolean assertion:\n\n" +
            "```text\nvc[coassert !?(b)](f) = ite(b, f, ∞)\n```",
        documentation: `${statements}#assert-and-assume`,
    },
    assume: {
        title: "assume — quantitative assumption",
        description: "`assume e` applies quantitative implication to the current verification condition `f`: `e ==> f`.",
        details: "Working backwards from `f` after the statement, the result is `∞` when `e ≤ f`, and `f` otherwise.\n\n" +
            "In a `proc`, use `assume ?(b)` for a Boolean assumption:\n\n" +
            "```text\nvc[assume ?(b)](f) = ite(b, f, ∞)\n```",
        documentation: `${statements}#assert-and-assume`,
    },
    coassume: {
        title: "coassume — dual quantitative assumption",
        description: "`coassume e` applies quantitative coimplication to the current verification condition `f`: `e <== f`.",
        details: "Working backwards from `f` after the statement, the result is `0` when `e ≥ f`, and `f` otherwise.\n\n" +
            "In a `coproc`, use `coassume !?(b)` for a Boolean assumption:\n\n" +
            "```text\nvc[coassume !?(b)](f) = ite(b, f, 0)\n```",
        documentation: `${statements}#assert-and-assume`,
    },
    havoc: {
        title: "havoc — forget variable values",
        description: "Forgets the current values of the specified variables by taking an infimum over them in the verification condition.",
        example: "havoc x, y, z",
        documentation: `${statements}#havoc`,
    },
    cohavoc: {
        title: "cohavoc — forget variable values, dual",
        description: "Forgets the current values of the specified variables by taking a supremum over them in the verification condition.",
        example: "cohavoc x, y, z",
        documentation: `${statements}#havoc`,
    },
    ...aliases(["reward", "tick"], {
        title: "reward / tick — accumulate a quantity",
        description: "Adds an expression to the current verification condition: `vc[reward r](f) = f + r`.",
        details: "`tick` is another name for `reward`.",
        documentation: `${statements}#reward-and-weigh`,
    }),
    weigh: {
        title: "weigh — scale a quantity",
        description: "Multiplies the current verification condition by an expression: `vc[weigh w](f) = f * w`.",
        documentation: `${statements}#reward-and-weigh`,
    },
    ...aliases(["if ⊓", "if \\cap"], {
        title: "if ⊓ — demonic choice",
        description: "Takes the minimum of both branch pre-expectations.",
        details: "`vc[if ⊓ { S } else { T }](f) = vc[S](f) ⊓ vc[T](f)`.",
        documentation: `${statements}#nondeterministic-choices`,
    }),
    ...aliases(["if ⊔", "if \\cup"], {
        title: "if ⊔ — angelic choice",
        description: "Takes the maximum of both branch pre-expectations.",
        details: "`vc[if ⊔ { S } else { T }](f) = vc[S](f) ⊔ vc[T](f)`.",
        documentation: `${statements}#nondeterministic-choices`,
    }),
    ...aliases(["if +", "if ⊕", "if \\oplus"], {
        title: "if + — additive choice",
        description: "Adds both branch pre-expectations.",
        details: "`vc[if + { S } else { T }](f) = vc[S](f) + vc[T](f)`.",
        documentation: `${statements}#nondeterministic-choices`,
    }),
    forall: {
        title: "forall — universal quantifier",
        description: "`forall x: T. b` is true when `b` holds for every value of `x` of type `T`.",
        documentation: `${expressions}#quantifiers`,
    },
    exists: {
        title: "exists — existential quantifier",
        description: "`exists x: T. b` is true when `b` holds for some value of `x` of type `T`.",
        documentation: `${expressions}#quantifiers`,
    },
    "@trigger": {
        title: "@trigger(expr, ...) — quantifier instantiation pattern",
        description: "Tells the SMT solver to instantiate a Boolean quantifier when it finds terms matching the given pattern.",
        details: "Comma-separated expressions form a multi-pattern.",
        documentation: `${expressions}#triggers`,
    },
    inf: {
        title: "inf — quantitative infimum",
        description: "`inf x: T. e` takes the greatest lower bound of `e` over all values of `x`.",
        details: "The body and result have type `EUReal`.",
        documentation: `${expressions}#quantifiers`,
    },
    sup: {
        title: "sup — quantitative supremum",
        description: "`sup x: T. e` takes the least upper bound of `e` over all values of `x`.",
        details: "The body and result have type `EUReal`.",
        documentation: `${expressions}#quantifiers`,
    },
    ite: {
        title: "ite — conditional expression",
        description: "`ite(b, x, y)` evaluates to `x` when `b` is true and to `y` otherwise.",
        documentation: `${expressions}#if-then-else`,
    },
    let: {
        title: "let — local name in an expression",
        description: "`let(x, e, body)` binds `x` to `e` within `body`.",
        details: "The type of `x` is inferred from `e`.",
        documentation: `${expressions}#let-expressions`,
    },
    "?": {
        title: "?(b) — Boolean embedding",
        description: "Embeds a Boolean expression into `EUReal`: `?(b)` is `∞` when `b` is true and `0` otherwise.",
        details: "In a `proc`, use `?(b)` for Boolean `pre` / `post` conditions and in `assert ?(b)` or `assume ?(b)`.",
        documentation: `${procedures}#embedding-boolean-specifications`,
    },
    "!?": {
        title: "!?(b) — dual Boolean embedding",
        description: "Embeds a Boolean expression into `EUReal`: `!?(b)` is `0` when `b` is true and `∞` otherwise.",
        details: "In a `coproc`, use `!?(b)` for Boolean `pre` / `post` conditions and in `coassert !?(b)` or `coassume !?(b)`.",
        documentation: `${procedures}#usually-you-want-coembed`,
    },
    ...aliases(["[", "]"], {
        title: "[b] — Iverson bracket",
        description: "The `EUReal` indicator of a Boolean expression: `[b]` is `1` when `b` is true and `0` otherwise.",
        documentation: `${expressions}#expression-syntax`,
    }),
    "!": {
        title: "! — negation",
        description: "On `Bool`, negates truth. " +
            "On `EUReal`: `!e == ite(e == 0, ∞, 0)`.",
        documentation: `${expressions}#semantics-and-under-specified-expressions`,
    },
    "~": {
        title: "~ — conegation",
        description: "On `Bool`, negates truth. " +
            "On `EUReal`: `~e == ite(e == ∞, 0, ∞)`.",
        documentation: `${expressions}#semantics-and-under-specified-expressions`,
    },
    ...aliases(["⊓", "\\cap"], {
        title: "⊓ / \\cap — minimum",
        description: "The minimum of two values; Boolean conjunction on `Bool`.",
        documentation: `${expressions}#expression-syntax`,
    }),
    ...aliases(["⊔", "\\cup"], {
        title: "⊔ / \\cup — maximum",
        description: "The maximum of two values; Boolean disjunction on `Bool`.",
        documentation: `${expressions}#expression-syntax`,
    }),
    ...aliases(["→", "==>"], {
        title: "→ / ==> — implication",
        description: "Boolean and quantitative implication.",
        details: "On `Bool`:\n\n```text\na → b = ¬a ∨ b\n```\n\n" +
            "On `EUReal`:\n\n```text\na → b = ⎧ ∞   if a ≤ b\n        ⎩ b   otherwise\n```",
        documentation: `${expressions}#semantics-and-under-specified-expressions`,
    }),
    ...aliases(["←", "<=="], {
        title: "← / <== — coimplication",
        description: "The lattice-theoretic dual of implication.",
        details: "On `Bool`:\n\n```text\na ← b = ¬a ∧ b\n```\n\n" +
            "On `EUReal`:\n\n```text\na ← b = ⎧ 0   if a ≥ b\n        ⎩ b   otherwise\n```",
        documentation: `${expressions}#semantics-and-under-specified-expressions`,
    }),
    "↘": {
        title: "↘ — quantitative comparison",
        description: "Compares two expectations, returning `∞` when `a ≤ b` and `0` otherwise.",
        details: "On `EUReal`: `(a ↘ b) == ite(a <= b, ∞, 0)`.",
        documentation: `${expressions}#semantics-and-under-specified-expressions`,
    },
    "↖": {
        title: "↖ — quantitative cocomparison",
        description: "Compares two expectations, returning `0` when `a ≥ b` and `∞` otherwise.",
        details: "On `EUReal`: `(a ↖ b) == ite(a >= b, 0, ∞)`.",
        documentation: `${expressions}#semantics-and-under-specified-expressions`,
    },
    "-": {
        title: "- — subtraction / monus",
        description: "Ordinary subtraction on signed types; truncating subtraction (monus) on unsigned types.",
        details: "On `UInt`, `2 - 3 == 0`.",
        documentation: `${expressions}#semantics-and-under-specified-expressions`,
    },
    ...aliases(["∞", "\\infty"], {
        title: "∞ / \\infty — infinity",
        description: "The greatest value of `EUReal`.",
        documentation: `${numbers}#eureal`,
    }),
    ...aliases(["<", "<=", ">", ">="], {
        title: "<, <=, >, >= — numeric comparison",
        description: "Numeric comparisons `<`, `<=`, `>`, `>=` returning `Bool`.",
        documentation: `${expressions}#expression-syntax`,
    }),
    ...aliases(["==", "!="], {
        title: "== / != — equality / inequality",
        description: "`a == b` tests equality; `a != b` tests inequality. " +
            "Both return `Bool`.",
        documentation: `${expressions}#expression-syntax`,
    }),
    "&&": {
        title: "&& — Boolean conjunction",
        description: "`a && b` holds iff both Boolean operands are true.",
        documentation: `${expressions}#expression-syntax`,
    },
    "||": {
        title: "|| — Boolean disjunction",
        description: "`a || b` holds iff at least one Boolean operand is true.",
        documentation: `${expressions}#expression-syntax`,
    },
    Bool: {
        title: "Bool — Boolean type",
        description: "The two truth values `false` and `true`.",
        documentation: `${docs}stdlib/booleans/`,
    },
    UInt: {
        title: "UInt — non-negative integers",
        description: "Unbounded unsigned integers: `0`, `1`, `2`, and so on.",
        documentation: `${numbers}#uint`,
    },
    Uint: {
        title: "Uint — legacy spelling of UInt",
        description: "The previous name of `UInt`, still accepted as an alias.",
        documentation: `${numbers}#uint`,
    },
    Int: {
        title: "Int — signed integers",
        description: "Unbounded signed integers.",
        documentation: `${numbers}#int`,
    },
    UReal: {
        title: "UReal — non-negative real numbers",
        description: "Unsigned real numbers: all real values greater than or equal to `0`.",
        documentation: `${numbers}#ureal`,
    },
    Real: {
        title: "Real — signed real numbers",
        description: "The mathematical real numbers.",
        documentation: `${numbers}#real`,
    },
    EUReal: {
        title: "EUReal — extended non-negative reals",
        description: "Extended unsigned real numbers: all values of `UReal`, together with `∞`.",
        details: "The verification domain for quantitative specifications.",
        documentation: `${numbers}#eureal`,
    },
    Realplus: {
        title: "Realplus — legacy spelling of EUReal",
        description: "The previous name of `EUReal`, still accepted as an alias.",
        documentation: `${numbers}#eureal`,
    },
    "[]": {
        title: "[]T — list type",
        description: "A list with elements of type `T` and an associated length, e.g. `[]UInt`.",
        details: "Use `len(list)` for its length, `select(list, index)` to read an element, and `store(list, index, value)` to obtain an updated list.",
        documentation: `${docs}stdlib/lists/`,
    },
    "@wp": {
        title: "@wp — weakest pre-expectation calculus",
        description: "Selects the weakest pre-expectation calculus for this procedure.",
        details: "Loops and recursive calls use least fixed points, with nonterminating runs contributing `0`. " +
            "Caesar checks that the proof rules used are compatible with this calculus.",
        documentation: calculus,
    },
    "@wlp": {
        title: "@wlp — weakest liberal pre-expectation calculus",
        description: "Selects the one-bounded weakest liberal pre-expectation calculus for this procedure.",
        details: "Expectations range over `[0, 1]`; loops and recursive calls use greatest fixed points, with nonterminating runs contributing `1`. " +
            "Caesar checks that the proof rules used are compatible with this calculus.",
        documentation: calculus,
    },
    "@uwlp": {
        title: "@uwlp — unbounded weakest liberal pre-expectation calculus",
        description: "Selects the unbounded weakest liberal pre-expectation calculus for this procedure.",
        details: "Expectations range over `EUReal`; loops and recursive calls use greatest fixed points, starting from the greatest expectation `∞`. " +
            "Caesar checks that the proof rules used are compatible with this calculus.",
        documentation: calculus,
    },
    "@ert": {
        title: "@ert — expected runtime calculus",
        description: "Selects the expected runtime calculus for this procedure.",
        details: "Loops and recursive calls use least fixed points. " +
            "Caesar checks that the proof rules used are compatible with this calculus.",
        documentation: calculus,
    },
    "@invariant": {
        title: "@invariant(I) — loop induction",
        description: "Verifies a loop using the candidate expectation `I` as its invariant.",
        details: "Let `Φ(X)` be the pre-expectation of one guarded loop step with continuation `X`, using the loop's post-expectation on exit. " +
            "The induction check is:\n\n" +
            "```text\nproc:   I ≤ Φ(I)\ncoproc: I ≥ Φ(I)\n```\n\n" +
            "This proves lower bounds on `wlp` / `uwlp` in a `proc`, and upper bounds on `wp` / `ert` in a `coproc`.",
        documentation: `${docs}proof-rules/induction/#using-induction`,
    },
    "@k_induction": {
        title: "@k_induction(k, I) — induction over several steps",
        description: "Verifies a loop invariant by considering up to `k` iterations at once.",
        details: "`I` is the candidate expectation, and `k` is a positive integer literal. " +
            "The induction check allows `I` to be re-established after one, two, or up to `k` iterations. " +
            "With `k == 1`, this is ordinary loop induction.\n\n" +
            "Proves lower bounds on `wlp` / `uwlp` in a `proc`, and upper bounds on `wp` / `ert` in a `coproc`.",
        documentation: `${docs}proof-rules/induction/#using-k-induction`,
    },
    "@unroll": {
        title: "@unroll(k, terminator) — loop unrolling",
        description: "Expands a loop into `k` guarded copies of its body.",
        details: "`k` is a non-negative integer literal. " +
            "If the loop continues after those iterations, its remaining computation is replaced by the expectation `terminator`.\n\n" +
            "The optional `terminator` defaults to `0` for `@wp` / `@ert`, `1` for `@wlp`, and `∞` for `@uwlp`. " +
            "These defaults give lower bounds on `wp` / `ert` and upper bounds on `wlp` / `uwlp`.",
        documentation: `${docs}proof-rules/unrolling/#usage`,
    },
    "@omega_invariant": {
        title: "@omega_invariant(n, I, terminator) — ω-invariants",
        description: "Proves a loop bound by induction over a sequence of expectations.",
        details: "`n` introduces a natural-number index within `I`; each index gives a candidate bound for a finite loop unrolling. " +
            "Let `Φ(X)` be the pre-expectation of one guarded loop step with continuation `X`, using the loop's post-expectation on exit.\n\n" +
            "For `wp` / `ert`, Caesar checks the base case and induction step:\n\n" +
            "```text\nI(0)     ≤ Φ(terminator)\nI(n + 1) ≤ Φ(I(n))       for all n ≥ 0\n```\n\n" +
            "The resulting lower bound is `sup n: UInt. I`. " +
            "For `wlp` / `uwlp`, the inequalities reverse and `inf n: UInt. I` gives an upper bound.\n\n" +
            "The optional `terminator` supplies the expectation at the base-case cutoff: `0` for `@wp` / `@ert`, `1` for `@wlp`, or `∞` for `@uwlp` by default.",
        documentation: `${docs}proof-rules/omega-invariants/#usage`,
    },
    "@ost": {
        title: "@ost(invariant, past_invariant, cdb, post) — optional stopping",
        description: "Proves that `invariant` is a lower bound on the loop's `wp` using the Optional Stopping Theorem.",
        details: "- `invariant`: the candidate lower bound, which agrees with `post` on loop exit.\n" +
            "- `past_invariant`: an invariant bounding the expected number of loop iterations.\n" +
            "- `cdb`: a bound on the expected absolute change in `invariant` per iteration.\n" +
            "- `post`: the loop's post-expectation.",
        documentation: `${docs}proof-rules/ost/#usage`,
    },
    "@past": {
        title: "@past(invariant, epsilon, K) — positive almost-sure termination",
        description: "Proves that a loop terminates in a finite expected number of iterations.",
        details: "The non-negative expression `invariant` measures the work remaining and must decrease in expectation by at least `epsilon` per iteration. " +
            "Its value must be at least `K` while the guard holds, and at most `K` on exit.\n\n" +
            "`epsilon` and `K` are `UReal` literals with `0 < epsilon < K`.",
        documentation: `${docs}proof-rules/past/#past-from-ranking-superinvariants`,
    },
    "@ast": {
        title: "@ast(I, V, v, prob(v), decrease(v)) — almost-sure termination",
        description: "Proves that a loop terminates with probability one from every initial state satisfying `I`.",
        details: "- `I`: a Boolean invariant that holds at loop entry and after each iteration.\n" +
            "- `V`: a non-negative expression measuring progress towards termination.\n" +
            "- `v`: a logical variable for the value of `V` before an iteration, bound within `prob(v)` and `decrease(v)`.\n" +
            "- `prob(v)`: a lower bound on the probability of exiting or decreasing `V` by at least `decrease(v)`.\n" +
            "- `decrease(v)`: the size of the decrease required for progress.",
        documentation: `${docs}proof-rules/ast/#new-proof-rule`,
    },
    flip: {
        title: "flip(p) — Bernoulli sampling",
        description: "Returns `true` with probability `p`, `false` with probability `1 - p`; requires `0 <= p && p <= 1`.",
        example: "var heads: Bool = flip(0.5)",
        documentation: `${docs}stdlib/distributions/#symbolic-with-probabilities`,
    },
};

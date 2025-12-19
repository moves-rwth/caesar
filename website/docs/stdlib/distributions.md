---
sidebar_position: 4
---

# Distribution Expressions

Caesar supports a limited number of probability distributions as built-ins.
They are allowed as the right-hand side of an assignment, e.g. `x = ber(1, 1);`.
Distribution expressions are not allowed to occur nested inside expressions.

All distribution expressions except for `flip` take _literal_ arguments, i.e. numbers.
Expressions such as `1+x` or even `1+1` are not supported as arguments.

## Bernoulli

The [Bernoulli distribution](https://en.wikipedia.org/wiki/Bernoulli_distribution).

### Constant-only with Odds

```heyvl
proc ber(pa: UInt, pb: UInt) -> (r: Bool)
```

This version takes two _odds_: `ber(pa, pb)` returns `true` with probability `pa/(pa+pb)` and `false` with probability `pb/(pa+pb)`.

Formally: `vc[x = ber(pa, pb)](φ) = (pa/(pa+pb)) * φ[x/true] + (pb/(pa+pb)) * φ[x/false]`.

<small>Note that calls with <code>pa+pb = 0</code> will result in a constant zero expectation.</small>

### Symbolic with Probabilities

```heyvl
proc flip(p: UReal) -> (r: Bool)
```

Returns `true` with probability `p` and `false` with probability `1-p`.
Note: if `p` is not a valid probability (not in the range `[0,1]`), then the result of this distribution is undefined!

This distribution accepts symbolic parameters (not just constants).

## Uniform

```heyvl
proc unif(a: UInt, b: UInt) -> (r: UInt)
```

The [uniform distribution](https://en.wikipedia.org/wiki/Discrete_uniform_distribution) returns the values in the closed interval `[a,b]` with uniform probability.

Note that calls with `a < b` will result in a constant zero expectation.

## Binomial

```heyvl
proc binom(n: UInt, pa: UInt, pb: UInt) -> (r: UInt)
```

Returns values `r` according to the [binomial distribution](https://en.wikipedia.org/wiki/Binomial_distribution) where `n` is the number of trials, `pa` are the odds of success and `pb` are the odds of failure.

## Hypergeometric

```heyvl
proc hyper(pN: UInt, k: UInt, pn: UInt) -> (r: UInt)
```

Return values according to the [hypergeometric distribution](https://en.wikipedia.org/wiki/Hypergeometric_distribution) where `pN` is the population size, `k` is the number of success states in the population and `pn` is the number of draws.
The result `r` is the number of observed successes, weighted by its probability.

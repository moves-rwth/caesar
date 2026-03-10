---
sidebar_position: 7
description: Checking entailment of verification conditions for `coproc` and `proc` declarations in a HeyVL file.
---

# Entailment Checking

The `caesar entailment` command checks entailment of verification conditions for `coproc` and `proc` declarations in a HeyVL file.

For each checked pair `(C, P)` with `C` a `coproc` and `P` a `proc`, Caesar checks:

`vc[C](0) ≤ vc[P](∞)`

Before comparing, Caesar renames parameters of `P` to match `C`.

:::warning Experimental Feature

`caesar entailment` is experimental.
Its behavior, input restrictions, and command-line interface may change in future Caesar versions.

:::

## Usage

Caesar checks consecutive declaration pairs in source order:

1. first declaration: `coproc`,
2. second declaration: `proc`.

Each pair must have matching parameter signatures (same arity, names, types, and order).

Run entailment checking with:

```bash
caesar entailment example.heyvl
```

The example below shows a simple refinement check for two implementations of binary randomized response, a privacy mechanism for sensitive Boolean data.

Example:

```heyvl
domain Refinement {
    func payoff(secret: Bool, reported: Bool): EUReal
}

coproc rr_two_coin(secret: Bool) -> (reported: Bool)
    post payoff(secret, reported)
{
    var truthful: Bool = flip(0.5)
    if truthful {
        reported = secret
    } else {
        var random_bit: Bool = flip(0.5)
        reported = random_bit
    }
}

proc rr_direct(secret: Bool) -> (reported: Bool)
    post payoff(secret, reported)
{
    var keep: Bool = flip(0.75)
    if keep {
        reported = secret
    } else {
        reported = !secret
    }
}
```

Binary randomized response means: sometimes report the true secret bit, sometimes report a random/noisy bit.
`rr_two_coin` is the "truthful-or-random" version, while `rr_direct` is the equivalent collapsed version.

The `post` is just the uninterpreted function `payoff(secret, reported)`, so the check is for all possible quantitative observations.
For this example, Caesar reports:

```
example.heyvl::rr_two_coin: Verified.
```

For all available options, run `caesar entailment --help`.
This command reuses the same option set as [`caesar verify`](./README.md#subcommand-caesar-verify).

# Other Loop Rules

This directory contains slicing benchmarks for loop-rule examples that are not
part of the Park-induction benchmark families.

Several files that used to live here were exact duplicates of canonical tests
and were removed. Use the canonical tests instead:

- `ast-rule.heyvl`: `tests/loop-rules/ast2018/ast-flipflop_core.heyvl`
- `ast-rule2.heyvl`: `tests/loop-rules/ast2018/ast-state-machine.heyvl`
- `optional-stopping-theorem.heyvl`:
  `tests/loop-rules/ost2019/aiming-low-example39.heyvl`
- `past.heyvl`: `tests/loop-rules/past2013/past.heyvl`
- `simple-omega-invariant.heyvl`:
  `tests/loop-rules/omega_invariants/countdown_core.heyvl`

Files remaining in this directory should be slicing-specific variants or
examples that do not already exist byte-for-byte elsewhere in `tests`.

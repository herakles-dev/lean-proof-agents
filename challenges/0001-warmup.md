# Challenge 0001 — Warmup: √2 is irrational

- **Module:** `MathProof/Challenges/C0001Warmup.lean`
- **Theorem:** `MathProof.Challenges.C0001Warmup.sqrt_two_irrational`
- **Status:** ✅ SOLVED

## Problem

Prove that `√2` is irrational — i.e. there is no rational `q` with `q = √2`.

## Formal statement

```lean
theorem sqrt_two_irrational : Irrational (Real.sqrt 2)
```

## Notes

Classic first formalization. Mathlib already provides `irrational_sqrt_two`, so the
proof is a one-liner — the point here is to exercise the toolchain, the cache, and the
`check-proof.sh` no-`sorry` gate, not to reprove it from first principles.

Wolfram oracle sanity check (exploration only, **not** proof):
`scripts/wolfram.sh "is sqrt(2) rational"` → confirms irrationality before you formalize.

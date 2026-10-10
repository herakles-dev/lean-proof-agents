# Challenge 0003 — Gauss's sum by induction

- **Module:** `MathProof/Challenges/C0003GaussSum.lean`
- **Theorem:** `MathProof.Challenges.C0003GaussSum.gauss_sum`
- **Status:** ✅ SOLVED

## Problem

Prove `0 + 1 + ⋯ + n = n(n+1)/2` — stated division-free as `(∑_{i<n+1} i) · 2 = n·(n+1)`.

## Formal statement

```lean
theorem gauss_sum (n : ℕ) : (∑ i ∈ range (n + 1), i) * 2 = n * (n + 1)
```

## Notes

First genuine hand-proof (fluency track). Induction on `n`; step unfolds the sum with
`Finset.sum_range_succ`, rewrites by the induction hypothesis, and closes with `ring`.
Deliberately does **not** cite Mathlib's `Finset.sum_range_id`. Axioms clean, no `sorry`.

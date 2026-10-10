# Challenge 0017 — Telescoping Reciprocals

- **Module:** `MathProof/Challenges/C0017TelescopingReciprocals.lean`
- **Theorem:** `MathProof.Challenges.C0017TelescopingReciprocals.recip_telescope`
- **Status:** ✅ SOLVED

## Problem

For every natural number `n`, the sum of reciprocal products `1/((k+1)(k+2))` for
`k = 0, 1, …, n-1` equals `n/(n+1)`.

## Formal statement

```lean
theorem recip_telescope (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 : ℚ) / ((k + 1) * (k + 2))) = n / (n + 1)
```

## Proof idea

Induction on `n`. Base case `n = 0` is `simp`. Inductive step uses
`Finset.sum_range_succ` and the induction hypothesis, then closes the resulting
rational-arithmetic identity `n/(n+1) + 1/((n+1)(n+2)) = (n+1)/(n+2)` with
`field_simp; ring` (the denominators `n+1`, `n+2` are nonzero by `positivity`).

## Notes

Explore with the Wolfram oracle before formalizing (exploration only, not proof):
`scripts/wolfram.sh "<atomic query>"`

# Challenge 0008 — Bernoulli Inequality

- **Module:** `MathProof/Challenges/C0008BernoulliInequality.lean`
- **Theorem:** `MathProof.Challenges.C0008BernoulliInequality.bernoulli`
- **Status:** ✅ SOLVED

## Problem

Bernoulli's inequality: for a real number `x ≥ -1` and a natural number `n`,
`1 + n·x ≤ (1 + x)^n`.

## Formal statement

```lean
theorem bernoulli (x : ℝ) (hx : -1 ≤ x) (n : ℕ) : 1 + n * x ≤ (1 + x) ^ n
```

## Notes

Proved directly via the Mathlib lemma `one_add_mul_le_pow`, which gives
`1 + n * a ≤ (1 + a) ^ n` for `-2 ≤ a`. Since `-1 ≤ x` implies `-2 ≤ x`
(via `linarith`), the hypothesis specializes immediately.

Verify: `scripts/check-proof.sh C0008BernoulliInequality bernoulli` → SOLVED.

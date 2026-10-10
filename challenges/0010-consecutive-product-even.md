# Challenge 0010 — Consecutive Product Even

- **Module:** `MathProof/Challenges/C0010ConsecutiveProductEven.lean`
- **Theorem:** `MathProof.Challenges.C0010ConsecutiveProductEven.consecutive_product_even`
- **Status:** ✅ SOLVED

## Problem

Show that the product of two consecutive natural numbers, `n` and `n + 1`, is always even.

## Formal statement

```lean
theorem consecutive_product_even (n : ℕ) : 2 ∣ n * (n + 1)
```

## Notes

Proved directly via `Nat.even_mul_succ_self n : Even (n * (n + 1))` together with
`Even.two_dvd` to convert `Even (n * (n + 1))` into `2 ∣ n * (n + 1)`.

Verify: `scripts/check-proof.sh C0010ConsecutiveProductEven consecutive_product_even` → SOLVED.

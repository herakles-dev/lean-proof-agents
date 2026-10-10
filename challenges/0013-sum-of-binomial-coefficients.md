# Challenge 0013 — Sum of binomial coefficients

- **Module:** `MathProof/Challenges/C0013SumOfBinomialCoefficients.lean`
- **Theorem:** `MathProof.Challenges.C0013SumOfBinomialCoefficients.sum_choose`
- **Status:** ✅ SOLVED

## Problem

The sum of the binomial coefficients along row `n` of Pascal's triangle equals `2 ^ n`:
`C(n,0) + C(n,1) + … + C(n,n) = 2^n`.

## Formal statement

```lean
theorem sum_choose (n : ℕ) : (∑ k ∈ Finset.range (n + 1), Nat.choose n k) = 2 ^ n
```

## Notes

One-line citation of `Nat.sum_range_choose` (Mathlib `Data/Nat/Choose/Sum.lean`). The range
is `n + 1` so it covers `k = 0 … n` (verbatim match to the Mathlib lemma).
Axioms: `[propext, Classical.choice, Quot.sound]` (clean).

# Challenge 0004 — Sum of first n odd numbers is n²

- **Module:** `MathProof/Challenges/C0004SumOfOdds.lean`
- **Theorem:** `MathProof.Challenges.C0004SumOfOdds.sum_odds`
- **Status:** ✅ SOLVED

## Problem

Prove `1 + 3 + 5 + ⋯ + (2n−1) = n²`, i.e. `∑_{i<n} (2i+1) = n²`.

## Formal statement

```lean
theorem sum_odds (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2
```

## Notes

Induction; step: `Finset.sum_range_succ` + ih + `ring`. Clean axioms, no `sorry`.

# Challenge 0005 — Sum of first n squares

- **Module:** `MathProof/Challenges/C0005SumOfSquares.lean`
- **Theorem:** `MathProof.Challenges.C0005SumOfSquares.sum_squares`
- **Status:** ✅ SOLVED

## Problem

Prove `1² + 2² + ⋯ + n² = n(n+1)(2n+1)/6`, stated division-free as
`(∑_{i<n+1} i²)·6 = n(n+1)(2n+1)`.

## Formal statement

```lean
theorem sum_squares (n : ℕ) :
    (∑ i ∈ range (n + 1), i ^ 2) * 6 = n * (n + 1) * (2 * n + 1)
```

## Notes

Induction; step: `Finset.sum_range_succ` + ih + `ring` (cubic identity). Clean axioms, no `sorry`.

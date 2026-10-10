# Challenge 0007 — Sum of first n cubes

- **Module:** `MathProof/Challenges/C0007SumOfCubes.lean`
- **Theorem:** `MathProof.Challenges.C0007SumOfCubes.sum_cubes`
- **Status:** ✅ SOLVED

## Problem

Prove `1³ + 2³ + ⋯ + n³ = (n(n+1)/2)²`, stated division-free as
`(∑_{i<n+1} i³)·4 = (n(n+1))²`.

## Formal statement

```lean
theorem sum_cubes (n : ℕ) : (∑ i ∈ range (n + 1), i ^ 3) * 4 = (n * (n + 1)) ^ 2
```

## Notes

Induction; step: `Finset.sum_range_succ` + ih + `ring` (quartic identity). Clean axioms, no `sorry`.

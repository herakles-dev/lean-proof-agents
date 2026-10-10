# Challenge 0024 — sqrt2 plus sqrt3 irrational

- **Module:** `MathProof/Challenges/C0024Sqrt2PlusSqrt3Irrational.lean`
- **Theorem:** `MathProof.Challenges.C0024Sqrt2PlusSqrt3Irrational.sqrt2_add_sqrt3_irrational`
- **Status:** ✅ SOLVED

## Problem

Show that $\sqrt{2} + \sqrt{3}$ is irrational.

## Formal statement

```lean
theorem sqrt2_add_sqrt3_irrational : Irrational (Real.sqrt 2 + Real.sqrt 3)
```

## Notes

- **A rationality-transfer argument.** There is no single Mathlib lemma for the sum of two
  irrationals (that sum is not generally irrational), so the proof decomposes: assume
  `(q : ℝ) = √2 + √3` for some `q : ℚ`, then isolate `√3 = q − √2` and square both sides.
  Using `(√2)² = 2` and `(√3)² = 3`, the cross term gives `√2 = (q² − 1) / (2q)` — a rational
  number — contradicting `irrational_sqrt_two`.
- `q ≠ 0` falls out of `√2 + √3 > 0` via `positivity`, which is needed for the division step.
- Closing tactics: `field_simp` + `nlinarith` to solve for `√2`, then `push_cast` to match the
  rational witness cast back to `ℝ`.

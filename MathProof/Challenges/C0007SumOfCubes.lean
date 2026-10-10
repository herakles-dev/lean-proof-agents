import MathProof.Basic

/-!
# Challenge C0007 — Sum of the first n cubes

**Statement:** `(1³ + 2³ + ⋯ + n³) · 4 = (n(n+1))²`.
**Status:** SOLVED ✅

Division-free form to stay in ℕ. Induction on `n`; the step unfolds the sum, rewrites by
the hypothesis, and `ring` verifies the identity
`(k(k+1))² + 4(k+1)³ = ((k+1)(k+2))²`.
-/

namespace MathProof.Challenges.C0007SumOfCubes

open Finset

/-- Sum of the first n cubes, division-free: (∑_{i<n+1} i³)·4 = (n(n+1))². -/
theorem sum_cubes (n : ℕ) : (∑ i ∈ range (n + 1), i ^ 3) * 4 = (n * (n + 1)) ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, add_mul, ih]
    ring

end MathProof.Challenges.C0007SumOfCubes

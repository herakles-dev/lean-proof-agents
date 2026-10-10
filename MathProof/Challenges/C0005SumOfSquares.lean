import MathProof.Basic

/-!
# Challenge C0005 — Sum of the first n squares

**Statement:** `(1² + 2² + ⋯ + n²) · 6 = n(n+1)(2n+1)`.
**Status:** SOLVED ✅

Division-free form to stay in ℕ. Induction on `n`; the step unfolds the sum, rewrites by
the hypothesis, and `ring` verifies the cubic identity
`k(k+1)(2k+1) + 6(k+1)² = (k+1)(k+2)(2k+3)`.
-/

namespace MathProof.Challenges.C0005SumOfSquares

open Finset

/-- Sum of the first `n` squares, division-free: `(∑_{i<n+1} i²)·6 = n(n+1)(2n+1)`. -/
theorem sum_squares (n : ℕ) :
    (∑ i ∈ range (n + 1), i ^ 2) * 6 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, add_mul, ih]
    ring

end MathProof.Challenges.C0005SumOfSquares

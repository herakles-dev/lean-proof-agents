import MathProof.Basic

/-!
# Challenge C0006 — Two-variable AM–GM (`2ab ≤ a² + b²`)

**Statement:** for all real `a, b`, `2ab ≤ a² + b²`.
**Status:** SOLVED ✅

A different flavour from the induction warm-ups: a real-analysis inequality. It follows from
`(a − b)² ≥ 0`; `nlinarith` closes it once given that square as a hint.
-/

namespace MathProof.Challenges.C0006Amgm

/-- Two-variable AM–GM / rearrangement inequality: `2ab ≤ a² + b²` over `ℝ`. -/
theorem two_mul_le_add_sq (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

end MathProof.Challenges.C0006Amgm

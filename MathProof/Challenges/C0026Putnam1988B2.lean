import MathProof.Basic

/-!
# Challenge C0026Putnam1988B2 — Putnam 1988 B2 (real inequality; prove-or-disprove)

**Status:** ✅ SOLVED.

**Source:** PutnamBench `putnam_1988_b2` (trishullab/PutnamBench, Apache-2.0). Ground-truth
answer to the prove-or-disprove: **True** (the implication holds). No Mathlib `Archive`
formalization exists (verified) — this is an unaided target.

Statement: for all reals `x, y`, if `y ≥ 0` and `y(y+1) ≤ (x+1)²` then `y(y-1) ≤ x²`.
-/

namespace MathProof.Challenges.C0026Putnam1988B2

/-- The answer to the prove-or-disprove (PutnamBench `putnam_1988_b2_solution`): the claim is true. -/
abbrev putnam_1988_b2_solution : Prop := True

/-- Putnam 1988 B2. -/
theorem putnam_1988_b2 :
    (∀ x y : ℝ, (y ≥ 0 ∧ y * (y + 1) ≤ (x + 1) ^ 2) → (y * (y - 1) ≤ x ^ 2))
      ↔ putnam_1988_b2_solution := by
  rw [iff_true]
  intro x y ⟨hy, h⟩
  -- Split on y ≤ 1 (where y*(y-1) ≤ 0 ≤ x^2 trivially) vs y > 1, then on the sign of x + 1:
  -- in each nontrivial branch an SOS/`nlinarith` certificate closes the goal.
  by_cases hy1 : y ≤ 1
  · nlinarith [sq_nonneg x, mul_nonneg hy (by linarith : (0:ℝ) ≤ 1 - y)]
  · push Not at hy1
    by_cases hx : -1 ≤ x
    · nlinarith [h, hy, hy1, hx, sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - y + 1),
        sq_nonneg (x + 1 - y), sq_nonneg (2 * x - 2 * y + 1), sq_nonneg (2 * y - 2 * x - 1),
        mul_nonneg (by linarith : (0:ℝ) ≤ x + 1) (by linarith : (0:ℝ) ≤ y - 1),
        mul_nonneg (by linarith : (0:ℝ) ≤ y - 1) (by linarith : (0:ℝ) ≤ y - 1)]
    · push Not at hx
      nlinarith [h, hy, hy1, hx, sq_nonneg (x + y + 1), sq_nonneg (x - y - 1),
        sq_nonneg (2 * x + 2 * y + 1),
        mul_nonneg (by linarith : (0:ℝ) ≤ -x - 1) (by linarith : (0:ℝ) ≤ y - 1)]

end MathProof.Challenges.C0026Putnam1988B2

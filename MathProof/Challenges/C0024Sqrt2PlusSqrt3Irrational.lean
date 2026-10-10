import MathProof.Basic

/-!
# Challenge C0024Sqrt2PlusSqrt3Irrational — √2 + √3 is irrational

**Status:** ✅ SOLVED

`Real.sqrt 2 + Real.sqrt 3` is irrational. There is no single Mathlib lemma for it
(the sum of two irrationals is not generally irrational), so it needs a *decomposition*:
from `√2 + √3 = q` derive that `√2` itself is rational (via `(√2+√3)(√3−√2) = 1`),
contradicting `irrational_sqrt_two`.

DEPTH-loop DECOMPOSE-rung target (no Archive shortcut).
-/

namespace MathProof.Challenges.C0024Sqrt2PlusSqrt3Irrational

/-- **√2 + √3 is irrational.** -/
theorem sqrt2_add_sqrt3_irrational : Irrational (Real.sqrt 2 + Real.sqrt 3) := by
  rintro ⟨q, hq⟩
  -- `hq : (q : ℝ) = √2 + √3`
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    rw [hq]; positivity
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  -- from `√3 = q - √2`, square both sides to isolate `√2`.
  have key : Real.sqrt 3 = (q : ℝ) - Real.sqrt 2 := by linarith [hq]
  have hsq : (3 : ℝ) = ((q : ℝ) - Real.sqrt 2) ^ 2 := by rw [← h3, key]
  have hsqrt2eq : Real.sqrt 2 = ((q : ℝ) ^ 2 - 1) / (2 * (q : ℝ)) := by
    field_simp
    nlinarith [hsq, h2]
  -- so `√2` is the cast of the rational `r := (q^2 - 1) / (2*q)`, contradicting irrationality.
  refine irrational_sqrt_two ⟨(q ^ 2 - 1) / (2 * q), ?_⟩
  push_cast
  rw [hsqrt2eq]

end MathProof.Challenges.C0024Sqrt2PlusSqrt3Irrational

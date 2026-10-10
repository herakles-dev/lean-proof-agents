import MathProof.Basic

/-!
# Challenge C0008BernoulliInequality — Bernoulli's inequality

**Status:** ✅ SOLVED

Verify:  `scripts/check-proof.sh C0008BernoulliInequality`
-/

namespace MathProof.Challenges.C0008BernoulliInequality

/-- Bernoulli's inequality: for -1 ≤ x and n : ℕ, 1 + n·x ≤ (1 + x)^n. -/
theorem bernoulli (x : ℝ) (hx : -1 ≤ x) (n : ℕ) : 1 + n * x ≤ (1 + x) ^ n :=
  one_add_mul_le_pow (by linarith) n

end MathProof.Challenges.C0008BernoulliInequality

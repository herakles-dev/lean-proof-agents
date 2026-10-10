import MathProof.Basic

/-!
# Challenge C0008BernoulliInequality — Bernoulli's inequality

**Status:** ✅ SOLVED

Workflow:
1. (optional) explore first:  `scripts/wolfram.sh "<atomic query>"`
2. state the theorem below, keep `sorry` while you work
3. build it:  `lake build MathProof.Challenges.C0008BernoulliInequality`
4. verify done (no sorry, clean axioms):  `scripts/check-proof.sh C0008BernoulliInequality`

Not imported by `MathProof.lean` until `scripts/new-challenge.sh` copies it.
-/

namespace MathProof.Challenges.C0008BernoulliInequality

/-- Bernoulli's inequality: for -1 ≤ x and n : ℕ, 1 + n·x ≤ (1 + x)^n. -/
theorem bernoulli (x : ℝ) (hx : -1 ≤ x) (n : ℕ) : 1 + n * x ≤ (1 + x) ^ n :=
  one_add_mul_le_pow (by linarith) n

end MathProof.Challenges.C0008BernoulliInequality

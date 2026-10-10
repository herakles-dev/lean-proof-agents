import MathProof.Basic

/-!
# Challenge C0009SqrtPrimeIrrational — The square root of any prime is irrational

**Status:** ✅ SOLVED

Verify:  `scripts/check-proof.sh C0009SqrtPrimeIrrational`
-/

namespace MathProof.Challenges.C0009SqrtPrimeIrrational

/-- The square root of any prime is irrational. -/
theorem sqrt_prime_irrational (p : ℕ) (hp : p.Prime) : Irrational (Real.sqrt p) :=
  hp.irrational_sqrt

end MathProof.Challenges.C0009SqrtPrimeIrrational

import MathProof.Basic

/-!
# Challenge C0009SqrtPrimeIrrational — The square root of any prime is irrational

**Status:** ✅ SOLVED

Workflow:
1. (optional) explore first:  `scripts/wolfram.sh "<atomic query>"`
2. state the theorem below, keep `sorry` while you work
3. build it:  `lake build MathProof.Challenges.C0009SqrtPrimeIrrational`
4. verify done (no sorry, clean axioms):  `scripts/check-proof.sh C0009SqrtPrimeIrrational`

Not imported by `MathProof.lean` until `scripts/new-challenge.sh` copies it.
-/

namespace MathProof.Challenges.C0009SqrtPrimeIrrational

/-- The square root of any prime is irrational. -/
theorem sqrt_prime_irrational (p : ℕ) (hp : p.Prime) : Irrational (Real.sqrt p) :=
  hp.irrational_sqrt

end MathProof.Challenges.C0009SqrtPrimeIrrational

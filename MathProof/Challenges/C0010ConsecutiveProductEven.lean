import MathProof.Basic

/-!
# Challenge C0010ConsecutiveProductEven — product of consecutive naturals is even

**Status:** ✅ SOLVED

Verify:  `scripts/check-proof.sh C0010ConsecutiveProductEven`
-/

namespace MathProof.Challenges.C0010ConsecutiveProductEven

/-- The product of two consecutive naturals is even. -/
theorem consecutive_product_even (n : ℕ) : 2 ∣ n * (n + 1) :=
  (Nat.even_mul_succ_self n).two_dvd

end MathProof.Challenges.C0010ConsecutiveProductEven

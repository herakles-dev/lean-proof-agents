import MathProof.Basic

/-!
# Challenge C0010ConsecutiveProductEven — product of consecutive naturals is even

**Status:** ✅ SOLVED

Workflow:
1. (optional) explore first:  `scripts/wolfram.sh "<atomic query>"`
2. state the theorem below, keep `sorry` while you work
3. build it:  `lake build MathProof.Challenges.C0010ConsecutiveProductEven`
4. verify done (no sorry, clean axioms):  `scripts/check-proof.sh C0010ConsecutiveProductEven`

Not imported by `MathProof.lean` until `scripts/new-challenge.sh` copies it.
-/

namespace MathProof.Challenges.C0010ConsecutiveProductEven

/-- The product of two consecutive naturals is even. -/
theorem consecutive_product_even (n : ℕ) : 2 ∣ n * (n + 1) :=
  (Nat.even_mul_succ_self n).two_dvd

end MathProof.Challenges.C0010ConsecutiveProductEven

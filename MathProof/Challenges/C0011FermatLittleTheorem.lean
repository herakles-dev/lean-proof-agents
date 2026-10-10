import MathProof.Basic

/-!
# Challenge C0011FermatLittleTheorem — Fermat's Little Theorem

**Status:** ✅ SOLVED

Verify:  `scripts/check-proof.sh C0011FermatLittleTheorem`
-/

namespace MathProof.Challenges.C0011FermatLittleTheorem

/-- Fermat's Little Theorem, stated in `ZMod p`: for a prime `p` and any
`a : ZMod p`, `a ^ p = a`. -/
theorem fermat_little (p : ℕ) [Fact p.Prime] (a : ZMod p) : a ^ p = a :=
  ZMod.pow_card a

end MathProof.Challenges.C0011FermatLittleTheorem

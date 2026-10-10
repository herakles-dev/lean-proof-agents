import MathProof.Basic

/-!
# Challenge C0011FermatLittleTheorem — Fermat's Little Theorem

**Status:** ✅ SOLVED

Workflow:
1. (optional) explore first:  `scripts/wolfram.sh "<atomic query>"`
2. state the theorem below, keep `sorry` while you work
3. build it:  `lake build MathProof.Challenges.C0011FermatLittleTheorem`
4. verify done (no sorry, clean axioms):  `scripts/check-proof.sh C0011FermatLittleTheorem`

Not imported by `MathProof.lean` until `scripts/new-challenge.sh` copies it.
-/

namespace MathProof.Challenges.C0011FermatLittleTheorem

/-- Fermat's Little Theorem, stated in `ZMod p`: for a prime `p` and any
`a : ZMod p`, `a ^ p = a`. -/
theorem fermat_little (p : ℕ) [Fact p.Prime] (a : ZMod p) : a ^ p = a :=
  ZMod.pow_card a

end MathProof.Challenges.C0011FermatLittleTheorem

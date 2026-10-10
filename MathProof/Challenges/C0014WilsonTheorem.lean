import MathProof.Basic

/-!
# Challenge C0014WilsonTheorem — Wilson's theorem

**Status:** ✅ SOLVED

For a prime `p`, `(p - 1)!` is congruent to `-1` modulo `p`.
-/

namespace MathProof.Challenges.C0014WilsonTheorem

open Nat

/-- **Wilson's theorem**: for a prime `p`, `(p - 1)! ≡ -1 (mod p)`. -/
theorem wilson (p : ℕ) [Fact p.Prime] : ((p - 1)! : ZMod p) = -1 :=
  ZMod.wilsons_lemma p

end MathProof.Challenges.C0014WilsonTheorem

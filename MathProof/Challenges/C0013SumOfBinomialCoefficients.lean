import MathProof.Basic

/-!
# Challenge C0013SumOfBinomialCoefficients — sum of binomial coefficients over a row = 2^n

**Status:** ✅ SOLVED

Workflow:
1. (optional) explore first:  `scripts/wolfram.sh "<atomic query>"`
2. state the theorem below, keep `sorry` while you work
3. build it:  `lake build MathProof.Challenges.C0013SumOfBinomialCoefficients`
4. verify done (no sorry, clean axioms):  `scripts/check-proof.sh C0013SumOfBinomialCoefficients`

Not imported by `MathProof.lean` until `scripts/new-challenge.sh` copies it.
-/

namespace MathProof.Challenges.C0013SumOfBinomialCoefficients

/-- The sum of the binomial coefficients along row `n` of Pascal's triangle is `2 ^ n`. -/
theorem sum_choose (n : ℕ) : (∑ k ∈ Finset.range (n + 1), Nat.choose n k) = 2 ^ n :=
  Nat.sum_range_choose n

end MathProof.Challenges.C0013SumOfBinomialCoefficients

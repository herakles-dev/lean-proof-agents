import MathProof.Basic

/-!
# Challenge C0017TelescopingReciprocals — telescoping sum of reciprocal products

**Status:** ✅ SOLVED

The sum `∑_{k=0}^{n-1} 1/((k+1)(k+2))` telescopes via the partial fraction decomposition
`1/((k+1)(k+2)) = 1/(k+1) - 1/(k+2)`, collapsing to `n/(n+1)`.

Verify:  `scripts/check-proof.sh C0017TelescopingReciprocals`
-/

namespace MathProof.Challenges.C0017TelescopingReciprocals

/-- The telescoping sum of reciprocal products `1/((k+1)(k+2))` for `k = 0, …, n-1`
collapses to `n/(n+1)`. -/
theorem recip_telescope (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 : ℚ) / ((k + 1) * (k + 2))) = n / (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
    have hn2 : (n : ℚ) + 2 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

end MathProof.Challenges.C0017TelescopingReciprocals

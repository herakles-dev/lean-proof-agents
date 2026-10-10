import MathProof.Basic

/-!
# Challenge C0019TelescopingProduct — telescoping product `∏(1 - 1/(k+2)²)`

**Status:** ✅ SOLVED

The product `∏_{k=0}^{n-1} (1 - 1/(k+2)²)` telescopes: each factor
`1 - 1/(k+2)² = ((k+1)(k+3))/(k+2)²`, so adjacent `(k+2)` terms cancel, collapsing to
`(n+2)/(2(n+1))`. Truth-gated over ℚ: n=2→2/3, n=3→5/8, n=4→3/5, n=5→7/12.
Anchor: C0017TelescopingReciprocals (same `Finset.*_range_succ`/`field_simp`/`ring` skeleton).

Workflow:
1. (optional) explore first:  `scripts/wolfram.sh "<atomic query>"`
2. state the theorem below, keep `sorry` while you work
3. build it:  `lake build MathProof.Challenges.C0019TelescopingProduct`
4. verify done (no sorry, clean axioms):  `scripts/check-proof.sh C0019TelescopingProduct`

Not imported by `MathProof.lean` until `scripts/new-challenge.sh` copies it.
-/

namespace MathProof.Challenges.C0019TelescopingProduct

/-- The telescoping product `∏_{k=0}^{n-1} (1 - 1/(k+2)²)` collapses to `(n+2)/(2(n+1))`. -/
theorem telescoping_product (n : ℕ) :
    (∏ k ∈ Finset.range n, (1 - 1 / ((k : ℝ) + 2) ^ 2))
      = ((n : ℝ) + 2) / (2 * ((n : ℝ) + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
      push_cast
      field_simp
      ring

end MathProof.Challenges.C0019TelescopingProduct

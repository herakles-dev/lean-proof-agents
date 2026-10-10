import MathProof.Basic

/-!
# Challenge C0004 — Sum of the first n odd numbers is n²

**Statement:** `1 + 3 + 5 + ⋯ + (2n−1) = n²`, i.e. `∑_{i<n} (2i+1) = n²`.
**Status:** SOLVED ✅

Induction on `n`; the successor step unfolds with `Finset.sum_range_succ`, applies the
induction hypothesis, and `ring` closes `k² + (2k+1) = (k+1)²`.
-/

namespace MathProof.Challenges.C0004SumOfOdds

open Finset

/-- The sum of the first `n` odd numbers equals `n²`. -/
theorem sum_odds (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    ring

end MathProof.Challenges.C0004SumOfOdds

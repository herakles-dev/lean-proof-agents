import MathProof.Basic

/-!
# Challenge C0021InverseSquaresBounded — partial sums of `∑ 1/k²` stay below 2

**Status:** ✅ SOLVED

The Basel partial sums `∑_{k=1}^{n} 1/k²` are bounded above by `2` (they converge to
`π²/6 ≈ 1.645`). The instructive point: a direct induction on `< 2` is too weak — the
inductive hypothesis must be *strengthened* to `≤ 2 - 1/n` (using `1/(n+1)² ≤ 1/n - 1/(n+1)`).
Truth-gated over ℚ: n=1→1, n=2→5/4, n=3→49/36, n=10→≈1.550, all `< 2`.

Verify:  `scripts/check-proof.sh C0021InverseSquaresBounded`
-/

namespace MathProof.Challenges.C0021InverseSquaresBounded

/-- Strengthened bound (auxiliary, shifted to `range (m+1)` so the telescoping residual matches
`Finset.sum_range_succ`'s actual added term): the partial sum of `m+1` terms stays below
`2 - 1/(m+1)`, which is self-propagating under induction (unlike the naive `< 2` bound). -/
theorem sum_inv_sq_le_aux (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), (1 : ℝ) / ((k : ℝ) + 1) ^ 2) ≤ 2 - 1 / ((m : ℝ) + 1) := by
  induction m with
  | zero => simp; norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h1 : (0:ℝ) < (m:ℝ) + 1 := by positivity
    have hstep : (1:ℝ) / ((m:ℝ) + 1 + 1) ^ 2 ≤ 1 / ((m:ℝ) + 1) - 1 / ((m:ℝ) + 1 + 1) := by
      have e : (1:ℝ) / ((m:ℝ) + 1) - 1 / ((m:ℝ) + 1 + 1)
          = 1 / (((m:ℝ) + 1) * ((m:ℝ) + 1 + 1)) := by
        field_simp
        ring
      rw [e]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    push_cast
    linarith [ih, hstep]

/-- The Basel partial sums `∑_{k=1}^{n} 1/k²` are bounded above by `2`. -/
theorem sum_inv_sq_lt_two (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) ^ 2) < 2 := by
  cases n with
  | zero => simp
  | succ m =>
    have H := sum_inv_sq_le_aux m
    have hp : (0:ℝ) < 1 / ((m:ℝ) + 1) := by positivity
    linarith

end MathProof.Challenges.C0021InverseSquaresBounded

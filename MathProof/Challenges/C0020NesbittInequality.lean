import MathProof.Basic

/-!
# Challenge C0020NesbittInequality — Nesbitt's inequality

**Status:** ✅ SOLVED

Classic olympiad inequality: for positive reals `a, b, c`,
`a/(b+c) + b/(a+c) + c/(a+b) ≥ 3/2`, with equality iff `a = b = c`.
Truth-gated over ℚ (equality 3/2 at a=b=c=1; 5/3, 2, 65/42, 57/11 at other points).

Workflow:
1. (optional) explore first:  `scripts/wolfram.sh "<atomic query>"`
2. state the theorem below, keep `sorry` while you work
3. build it:  `lake build MathProof.Challenges.C0020NesbittInequality`
4. verify done (no sorry, clean axioms):  `scripts/check-proof.sh C0020NesbittInequality`

Not imported by `MathProof.lean` until `scripts/new-challenge.sh` copies it.
-/

namespace MathProof.Challenges.C0020NesbittInequality

/-- **Nesbitt's inequality.** For positive reals `a, b, c`,
`3/2 ≤ a/(b+c) + b/(a+c) + c/(a+b)`. -/
theorem nesbitt (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (a + c) + c / (a + b) := by
  have hbc : 0 < b + c := by linarith
  have hac : 0 < a + c := by linarith
  have hab : 0 < a + b := by linarith
  rw [div_add_div _ _ hbc.ne' hac.ne', div_add_div _ _ (mul_pos hbc hac).ne' hab.ne',
    le_div_iff₀ (mul_pos (mul_pos hbc hac) hab)]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
    mul_nonneg (sq_nonneg (a - b)) hc.le, mul_nonneg (sq_nonneg (b - c)) ha.le,
    mul_nonneg (sq_nonneg (a - c)) hb.le]

end MathProof.Challenges.C0020NesbittInequality

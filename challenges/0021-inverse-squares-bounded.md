# Challenge 0021 — Inverse Squares Bounded

- **Module:** `MathProof/Challenges/C0021InverseSquaresBounded.lean`
- **Theorem:** `MathProof.Challenges.C0021InverseSquaresBounded.sum_inv_sq_lt_two`
- **Status:** ✅ SOLVED

## Problem

The Basel partial sums are bounded above by 2: for every $n$,

$$\sum_{k=1}^{n} \frac{1}{k^2} < 2.$$

(The full series converges to $\pi^2/6 \approx 1.645$; this challenge only asks for the uniform
bound $< 2$.)

## Formal statement

```lean
theorem sum_inv_sq_lt_two (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) ^ 2) < 2
```

## Notes

- Truth-gated over ℚ: n=1→1, n=2→5/4, n=3→49/36, n=10→≈1.550 — all `< 2`.
- **The instructive point — "induction hypothesis too weak."** A direct induction on `< 2` is
  information-theoretically stuck: from `S < 2` you cannot conclude `S + 1/(n+1)² < 2`. The fix is
  to *strengthen* the statement to a self-propagating bound and induct on that:
  `∑_{k∈range (m+1)} 1/(k+1)² ≤ 2 − 1/(m+1)` (re-indexed so the `sum_range_succ` residual
  `1/(m+2)²` lines up with `1/(m+1) − 1/(m+2) = 1/((m+1)(m+2))`), then the target follows by
  `cases n` + `positivity` + `linarith`.
- **Solved via the DEPTH loop with a real stall.** Naive prover → BLOCKED → `stall-check` = STALL →
  `proof-trajectory-keeper` returned **GENERALIZE** → re-planned with the strengthened lemma → SOLVED.
  A dead end and the keeper's decision were recorded in the attempt's ledger (not committed to this repo).

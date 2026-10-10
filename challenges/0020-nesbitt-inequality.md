# Challenge 0020 — Nesbitt's Inequality

- **Module:** `MathProof/Challenges/C0020NesbittInequality.lean`
- **Theorem:** `MathProof.Challenges.C0020NesbittInequality.nesbitt`
- **Status:** ✅ SOLVED

## Problem

Nesbitt's inequality. For positive reals $a, b, c$,

$$\frac{a}{b+c} + \frac{b}{a+c} + \frac{c}{a+b} \ge \frac{3}{2},$$

with equality iff $a = b = c$.

## Formal statement

```lean
theorem nesbitt (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (a + c) + c / (a + b)
```

## Notes

- Truth-gated over ℚ (`scripts/lean-eval.sh`): equality `3/2` at `a=b=c=1`; strictly greater
  elsewhere (5/3, 2, 65/42, 57/11). Not a named Mathlib lemma — assembled from primitives.
- **Proof:** show each denominator positive; combine the three fractions with `div_add_div`;
  clear the positive denominator with `le_div_iff₀`; close the degree-3 polynomial inequality
  with `nlinarith` given Schur-weighted SOS hints `mul_nonneg (sq_nonneg (x-y)) z.le`. The
  underlying SOS certificate is `∑ (a+b)(a-b)² ≥ 0`.
- `le_div_iff` is deprecated in this Mathlib pin → `le_div_iff₀` (a build-error the prover fixed).
- Solved via the DEPTH loop (proof-strategist plan + ledger → lean-prover → proof-auditor);
  (ledger not committed). The Sonnet prover closed the SOS step on its first
  real attempt with self-devised hints, so the stall/keeper path was not triggered.

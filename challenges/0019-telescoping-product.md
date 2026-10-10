# Challenge 0019 — Telescoping Product

- **Module:** `MathProof/Challenges/C0019TelescopingProduct.lean`
- **Theorem:** `MathProof.Challenges.C0019TelescopingProduct.telescoping_product`
- **Status:** ✅ SOLVED

## Problem

Show that the finite product

$$\prod_{k=0}^{n-1}\left(1 - \frac{1}{(k+2)^2}\right) = \frac{n+2}{2(n+1)}.$$

Each factor telescopes: $1 - \tfrac{1}{(k+2)^2} = \tfrac{(k+1)(k+3)}{(k+2)^2}$, so adjacent
$(k+2)$ terms cancel and the product collapses to $\tfrac{n+2}{2(n+1)}$.

## Formal statement

```lean
theorem telescoping_product (n : ℕ) :
    (∏ k ∈ Finset.range n, (1 - 1 / ((k : ℝ) + 2) ^ 2))
      = ((n : ℝ) + 2) / (2 * ((n : ℝ) + 1))
```

## Notes

- Truth-gated offline over ℚ before formalizing (`scripts/lean-eval.sh`): n=2→2/3, n=3→5/8,
  n=4→3/5, n=5→7/12 — matches the closed form. (Wolfram/eval is exploration only, never proof.)
- Proof: induction on `n`; base case `simp`; successor via `Finset.prod_range_succ` + IH, then
  `push_cast; field_simp; ring`. Direct port of the telescoping-**sum** anchor C0017 (sum→product).
- Solved via the DEPTH loop (proof-strategist plan + ledger → lean-prover → proof-auditor).
  The ledger file itself is not committed.

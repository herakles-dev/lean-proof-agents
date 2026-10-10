# Challenge 0016 — Factorial Telescoping

- **Module:** `MathProof/Challenges/C0016FactorialTelescoping.lean`
- **Theorem:** `MathProof.Challenges.C0016FactorialTelescoping.factorial_telescope`
- **Status:** ✅ SOLVED

## Problem

Show that the sum `∑_{i=0}^{n-1} i · i!` telescopes to `n! - 1`.

## Formal statement

Stated additively to stay in `ℕ` (avoiding truncated subtraction):

```lean
theorem factorial_telescope (n : ℕ) :
    (∑ i ∈ Finset.range n, i * Nat.factorial i) + 1 = Nat.factorial n
```

## Notes

Proved by induction on `n`. Base case `n = 0`: both sides are `1`, closed by `simp`.
Inductive step: `Finset.sum_range_succ` peels off the last term, `Nat.factorial_succ`
rewrites `(n+1)! = (n+1) * n!`, the induction hypothesis substitutes the telescoped
sum, and `ring` closes the resulting algebraic identity
`n! + n * n! = (n + 1) * n!`.

Verify: `scripts/check-proof.sh C0016FactorialTelescoping factorial_telescope`

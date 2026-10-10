# Challenge 0009 — Sqrt Prime Irrational

- **Module:** `MathProof/Challenges/C0009SqrtPrimeIrrational.lean`
- **Theorem:** `MathProof.Challenges.C0009SqrtPrimeIrrational.sqrt_prime_irrational`
- **Status:** ✅ SOLVED

## Problem

Prove that the square root of any prime natural number is irrational.

## Formal statement

```lean
theorem sqrt_prime_irrational (p : ℕ) (hp : p.Prime) : Irrational (Real.sqrt p)
```

## Notes

Proved directly via the Mathlib lemma `Nat.Prime.irrational_sqrt`, which shows
`Irrational (√p)` for any `p : ℕ` satisfying `Nat.Prime p`.

Verify: `scripts/check-proof.sh C0009SqrtPrimeIrrational sqrt_prime_irrational` → SOLVED, clean
axioms (`propext`, `Classical.choice`, `Quot.sound`).

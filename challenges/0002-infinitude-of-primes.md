# Challenge 0002 — Infinitude of primes (Euclid's theorem)

- **Module:** `MathProof/Challenges/C0002InfinitudeOfPrimes.lean`
- **Theorems:** `MathProof.Challenges.C0002InfinitudeOfPrimes.euclid`, `….infinitude_of_primes`
- **Status:** ✅ SOLVED

## Problem

Prove there is no largest prime — for every bound `n` there is a prime `p ≥ n`, and
equivalently the set of primes is infinite.

## Formal statements

```lean
theorem euclid (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime
theorem infinitude_of_primes : {p : ℕ | p.Prime}.Infinite
```

## Notes

Warm-up #2 (fluency track). Discharged via Mathlib's `Nat.exists_infinite_primes` and
`Nat.infinite_setOfPred_prime`. Axioms clean (`propext, Classical.choice, Quot.sound`), no `sorry`.

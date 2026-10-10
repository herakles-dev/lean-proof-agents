# Challenge 0039 — Erdos 349 Sum Of Distinct Powers Of Two

- **Module:** `MathProof/Challenges/C0039Erdos349SumOfDistinctPowersOfTwo.lean`
- **Theorem:** `MathProof.Challenges.C0039Erdos349SumOfDistinctPowersOfTwo.exists_finsetSum_two_pow`
- **Status:** ✅ SOLVED (axioms: propext, Classical.choice, Quot.sound)

## Problem

Every natural number `k` is a sum of distinct powers of two: there exists a finite set `E` of
exponents such that `k = ∑ i ∈ E, 2 ^ i`. This is the existence half of the standard binary
representation of a natural number, and appears in google-deepmind/formal-conjectures as the
lemma `exists_finsetSum_two_pow` supporting the (still-open) Erdős Problem #349 on additively
complete sequences `⌊t·αⁿ⌋`.

Source: `ErdosProblems/349.lean`, `@[category research solved, AMS 11]`, body `sorry` upstream when this was written (September 2026).
This repo's proof is an independent formalization of the same sub-lemma and is not an upstream
contribution.

## Formal statement

```lean
theorem exists_finsetSum_two_pow (k : ℕ) :
    ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i
```

## Proof sketch

Mathlib already packages this as the equivalence `Nat.equivBitIndices : ℕ ≃ Finset ℕ`
(`Mathlib.Combinatorics.Colex`), witnessed by
`Finset.sum_toFinset_bitIndices_two_pow (n : ℕ) : ∑ i ∈ n.bitIndices.toFinset, 2 ^ i = n`.
Taking `E := k.bitIndices.toFinset` (the finset of set-bit positions of `k`) and flipping that
equation with `.symm` closes the existential in one line — no induction needed.

## Notes

Winning anchor: `Finset.sum_toFinset_bitIndices_two_pow`. Note the un-deprecation date
(2026-05-15) — the older name `Finset.twoPowSum_toFinset_bitIndices` is now a deprecated alias.

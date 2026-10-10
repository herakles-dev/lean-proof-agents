import MathProof.Basic

/-!
# Challenge C0039Erdos349SumOfDistinctPowersOfTwo — Erdős 349, binary expansion lemma

**Status:** ✅ SOLVED (axioms: propext, Classical.choice, Quot.sound).

**Source:** google-deepmind/formal-conjectures, `ErdosProblems/349.lean`, theorem
`exists_finsetSum_two_pow`, tagged `@[category research solved, AMS 11]` with a `sorry` body
(a genuine formalization gap). Toolchain there is Lean v4.33.1 = ours. Statement reproduced
**verbatim**. Upstream attaches this lemma to a `formal_proof using formal_conjectures` pointer
at cepadugato's `erdos-349-integer-characterization-proof` branch (an in-flight community proof
of the broader Erdős #349 characterization). This module is an **independent** formalization of
just this binary-expansion sub-lemma for our own corpus — it is not an upstream PR and does not
race that branch.

**Statement.** Every natural number `k` is a sum of distinct powers of two: there is a finite
set `E` of exponents with `k = ∑ i ∈ E, 2 ^ i`. This is exactly the existence of the standard
binary representation of `k`.

**Proof idea.** Mathlib already has the binary-expansion equivalence
`Nat.equivBitIndices : ℕ ≃ Finset ℕ` (in `Mathlib.Combinatorics.Colex`), witnessed by
`Finset.sum_toFinset_bitIndices_two_pow : ∑ i ∈ n.bitIndices.toFinset, 2 ^ i = n`. Taking
`E := k.bitIndices.toFinset` (the finset of set-bit positions of `k`) and flipping that equation
closes the existential directly — no induction needed.
-/

namespace MathProof.Challenges.C0039Erdos349SumOfDistinctPowersOfTwo

theorem exists_finsetSum_two_pow (k : ℕ) :
    ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i :=
  ⟨k.bitIndices.toFinset, (Finset.sum_toFinset_bitIndices_two_pow k).symm⟩

end MathProof.Challenges.C0039Erdos349SumOfDistinctPowersOfTwo

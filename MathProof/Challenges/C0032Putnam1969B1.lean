import MathProof.Basic

/-!
# Challenge C0032Putnam1969B1 — Putnam 1969 B1 (24 ∣ n+1 ⇒ 24 ∣ σ(n))

**Status:** ✅ SOLVED (cold — Sonnet `lean-prover`, first attempt).

**Source:** PutnamBench `putnam_1969_b1` (trishullab/PutnamBench, Apache-2.0). No Mathlib
`Archive` formalization exists. Statement reproduced **verbatim** from upstream (the
`proof-auditor` diffs against the cache; never weaken it).

Statement: let `n` be a positive integer with `24 ∣ n+1`. Then the sum of all divisors of `n`
is divisible by `24`.
-/

namespace MathProof.Challenges.C0032Putnam1969B1

open Nat

theorem putnam_1969_b1
(n : ℕ)
(hnpos : n > 0)
(hn : 24 ∣ n + 1)
: 24 ∣ ∑ d ∈ divisors n, d := by
  have hnne : n ≠ 0 := hnpos.ne'
  have hcop1 : Nat.Coprime n (n + 1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right n)
  have hcop : Nat.Coprime n 24 := hcop1.coprime_dvd_right hn
  have hsq_lemma : ∀ x : ZMod 24, IsUnit x → x * x = 1 := by decide
  have hunit_sq : ∀ a : ℕ, Nat.Coprime a 24 → (a : ZMod 24) * (a : ZMod 24) = 1 := fun a hacop =>
    hsq_lemma (a : ZMod 24) ((ZMod.isUnit_iff_coprime a 24).mpr hacop)
  have hn24 : (n : ZMod 24) = -1 := by
    have h0 : ((n + 1 : ℕ) : ZMod 24) = 0 := (ZMod.natCast_eq_zero_iff (n + 1) 24).mpr hn
    push_cast at h0
    linear_combination h0
  have hmul_gen : ∀ a ∈ n.divisors, (a : ZMod 24) * ((n / a : ℕ) : ZMod 24) = -1 := by
    intro a ha
    have had : a ∣ n := Nat.dvd_of_mem_divisors ha
    have : (a : ZMod 24) * ((n / a : ℕ) : ZMod 24) = (n : ZMod 24) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' had]
    rw [this, hn24]
  have hsq_gen : ∀ a ∈ n.divisors, (a : ZMod 24) * (a : ZMod 24) = 1 := by
    intro a ha
    have had : a ∣ n := Nat.dvd_of_mem_divisors ha
    exact hunit_sq a (Nat.Coprime.of_dvd_left had hcop)
  have hsum0 : (∑ d ∈ n.divisors, (d : ZMod 24)) = 0 := by
    apply Finset.sum_involution (fun d _ => n / d)
    · intro a ha
      have hmul := hmul_gen a ha
      have hsq := hsq_gen a ha
      have key : ((n / a : ℕ) : ZMod 24) = -(a : ZMod 24) := by
        have h1 : (a : ZMod 24) * ((a : ZMod 24) * ((n / a : ℕ) : ZMod 24)) = (a : ZMod 24) * (-1) := by
          rw [hmul]
        rw [← mul_assoc, hsq, one_mul] at h1
        rw [h1]; ring
      rw [key]; ring
    · intro a ha _
      have hmul := hmul_gen a ha
      have hsq := hsq_gen a ha
      intro heq
      rw [heq] at hmul
      rw [hsq] at hmul
      exact absurd hmul (by decide)
    · intro a ha
      have had : a ∣ n := Nat.dvd_of_mem_divisors ha
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd had, hnne⟩
    · intro a ha
      have had : a ∣ n := Nat.dvd_of_mem_divisors ha
      exact Nat.div_div_self had hnne
  have hcast : ((∑ d ∈ n.divisors, d : ℕ) : ZMod 24) = 0 := by
    rw [Nat.cast_sum]; exact hsum0
  exact (ZMod.natCast_eq_zero_iff _ 24).mp hcast

end MathProof.Challenges.C0032Putnam1969B1

import MathProof.Basic

/-!
# Challenge C0033Putnam1983A1 — Putnam 1983 A1 (count divisors of 10⁴⁰ or 20³⁰)

**Status:** ✅ SOLVED (cold — Sonnet `lean-prover`).

**Source:** PutnamBench `putnam_1983_a1` (trishullab/PutnamBench, Apache-2.0). No Mathlib
`Archive` formalization exists. Statement reproduced **verbatim** from upstream (the
`proof-auditor` diffs against the cache; never weaken it). This is a *determine-and-prove*
problem: fill `putnam_1983_a1_solution` with the correct value, then prove the equality.

Statement: how many positive integers `n` are exact divisors of at least one of `10⁴⁰`, `20³⁰`?
-/

namespace MathProof.Challenges.C0033Putnam1983A1

abbrev putnam_1983_a1_solution : ℕ := 2301

theorem putnam_1983_a1
: {n : ℤ | n > 0 ∧ (n ∣ 10 ^ 40 ∨ n ∣ 20 ^ 30)}.encard = putnam_1983_a1_solution := by
  have p2 : Nat.Prime 2 := by norm_num
  have p5 : Nat.Prime 5 := by norm_num
  -- factor the two bases into their prime powers
  have e10 : (10 : ℕ) ^ 40 = 2 ^ 40 * 5 ^ 40 := by
    have h1 : (10 : ℕ) = 2 * 5 := by norm_num
    rw [h1, mul_pow]
  have e20 : (20 : ℕ) ^ 30 = 2 ^ 60 * 5 ^ 30 := by
    have h1 : (20 : ℕ) = 2 ^ 2 * 5 := by norm_num
    rw [h1, mul_pow, ← pow_mul]
  -- cardinalities of the two divisor sets
  have hcardA : ((10 : ℕ) ^ 40).divisors.card = 1681 := by
    rw [e10, Nat.Coprime.card_divisors_mul
      (Nat.coprime_pow_primes 40 40 p2 p5 (by norm_num)),
      Nat.divisors_prime_pow p2, Nat.divisors_prime_pow p5,
      Finset.card_map, Finset.card_map, Finset.card_range]
  have hcardB : ((20 : ℕ) ^ 30).divisors.card = 1891 := by
    rw [e20, Nat.Coprime.card_divisors_mul
      (Nat.coprime_pow_primes 60 30 p2 p5 (by norm_num)),
      Nat.divisors_prime_pow p2, Nat.divisors_prime_pow p5,
      Finset.card_map, Finset.card_map, Finset.card_range, Finset.card_range]
  -- gcd of the two bases, and cardinality of its divisor set
  have hgcd : Nat.gcd ((10 : ℕ) ^ 40) ((20 : ℕ) ^ 30) = 2 ^ 40 * 5 ^ 30 := by
    rw [e10, e20]
    have f1 : (2 : ℕ) ^ 40 * 5 ^ 40 = (2 ^ 40 * 5 ^ 30) * 5 ^ 10 := by ring
    have f2 : (2 : ℕ) ^ 60 * 5 ^ 30 = (2 ^ 40 * 5 ^ 30) * 2 ^ 20 := by ring
    have cop2 : Nat.gcd ((5:ℕ) ^ 10) (2 ^ 20) = 1 :=
      Nat.coprime_pow_primes 10 20 p5 p2 (by norm_num)
    rw [f1, f2, Nat.gcd_mul_left, cop2, mul_one]
  have hcardI :
      (((10 : ℕ) ^ 40).divisors ∩ ((20 : ℕ) ^ 30).divisors).card = 1271 := by
    have hinter : ((10 : ℕ) ^ 40).divisors ∩ ((20 : ℕ) ^ 30).divisors
        = (Nat.gcd ((10 : ℕ) ^ 40) ((20 : ℕ) ^ 30)).divisors := by
      ext x
      simp only [Finset.mem_inter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hxa, _⟩, ⟨hxb, _⟩⟩
        exact ⟨Nat.dvd_gcd hxa hxb, Nat.gcd_ne_zero_left (by positivity)⟩
      · rintro ⟨hx, _⟩
        exact ⟨⟨hx.trans (Nat.gcd_dvd_left _ _), by positivity⟩,
               ⟨hx.trans (Nat.gcd_dvd_right _ _), by positivity⟩⟩
    rw [hinter, hgcd, Nat.Coprime.card_divisors_mul
      (Nat.coprime_pow_primes 40 30 p2 p5 (by norm_num)),
      Nat.divisors_prime_pow p2, Nat.divisors_prime_pow p5,
      Finset.card_map, Finset.card_map, Finset.card_range, Finset.card_range]
  have hcardS :
      (((10 : ℕ) ^ 40).divisors ∪ ((20 : ℕ) ^ 30).divisors).card = 2301 := by
    have hunion := Finset.card_union_add_card_inter
      (((10 : ℕ) ^ 40).divisors) (((20 : ℕ) ^ 30).divisors)
    omega
  -- rewrite the integer solution set as the image of this Finset under the ℕ → ℤ cast
  have hcast10 : (10 : ℤ) ^ 40 = ((10 ^ 40 : ℕ) : ℤ) := by norm_cast
  have hcast20 : (20 : ℤ) ^ 30 = ((20 ^ 30 : ℕ) : ℤ) := by norm_cast
  have hset : {n : ℤ | n > 0 ∧ (n ∣ 10 ^ 40 ∨ n ∣ 20 ^ 30)}
      = (Nat.cast : ℕ → ℤ) '' (↑(((10 : ℕ) ^ 40).divisors ∪ ((20 : ℕ) ^ 30).divisors) : Set ℕ) := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe, Finset.mem_union,
      Nat.mem_divisors]
    constructor
    · rintro ⟨hpos, hdvd⟩
      refine ⟨n.natAbs, ?_, Int.natAbs_of_nonneg hpos.le⟩
      rcases hdvd with h | h
      · rw [hcast10, Int.dvd_natCast] at h
        exact Or.inl ⟨h, by norm_num⟩
      · rw [hcast20, Int.dvd_natCast] at h
        exact Or.inr ⟨h, by norm_num⟩
    · rintro ⟨m, hm, rfl⟩
      refine ⟨?_, ?_⟩
      · rcases hm with h | h
        · exact_mod_cast Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr h)
        · exact_mod_cast Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr h)
      · rcases hm with ⟨hd, _⟩ | ⟨hd, _⟩
        · exact Or.inl (by rw [hcast10]; exact_mod_cast hd)
        · exact Or.inr (by rw [hcast20]; exact_mod_cast hd)
  rw [hset, Function.Injective.encard_image Nat.cast_injective,
    Set.encard_coe_eq_coe_finsetCard, hcardS]

end MathProof.Challenges.C0033Putnam1983A1

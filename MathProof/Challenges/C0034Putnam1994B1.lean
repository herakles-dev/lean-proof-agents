import MathProof.Basic

/-!
# Challenge C0034Putnam1994B1 — Putnam 1994 B1 (integers within 250 of exactly 15 squares)

**Status:** ✅ SOLVED.

**Source:** PutnamBench `putnam_1994_b1` (trishullab/PutnamBench, Apache-2.0). No Mathlib
`Archive` formalization exists. Statement reproduced **verbatim** from upstream (the
`proof-auditor` diffs against the cache; never weaken it). *Determine-and-prove*: fill
`putnam_1994_b1_solution` with the correct set, then prove the ↔.

Statement: find all positive integers `n` within `250` of exactly `15` perfect squares.
-/

namespace MathProof.Challenges.C0034Putnam1994B1

abbrev putnam_1994_b1_solution : Set ℤ := {n : ℤ | (315 ≤ n ∧ n ≤ 325) ∨ (332 ≤ n ∧ n ≤ 350)}

/-- Translate the `|n - m^2| ≤ 250` set from `ℤ` to a subtraction-free `ℕ` predicate. -/
private lemma set_eq (N : ℕ) :
    {m : ℕ | |(N : ℤ) - (m : ℤ) ^ 2| ≤ 250} =
      {m : ℕ | N ≤ m ^ 2 + 250 ∧ m ^ 2 ≤ N + 250} := by
  ext m
  simp only [Set.mem_ofPred_eq, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have : (N : ℤ) ≤ ((m ^ 2 + 250 : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this
    · have : ((m ^ 2 : ℕ) : ℤ) ≤ ((N + 250 : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this
  · rintro ⟨h1, h2⟩
    have h1' : (N : ℤ) ≤ ((m ^ 2 + 250 : ℕ) : ℤ) := by exact_mod_cast h1
    have h2' : ((m ^ 2 : ℕ) : ℤ) ≤ ((N + 250 : ℕ) : ℤ) := by exact_mod_cast h2
    push_cast at h1' h2'
    constructor <;> linarith

/-- The lower-bound threshold: `N ≤ m^2 + 250` iff `m` is at least `sqrt (N - 251) + 1`,
for `N ≥ 251` (so `N - 251` is a genuine, non-truncated subtraction). -/
private lemma lo_iff (N : ℕ) (hN : 251 ≤ N) (m : ℕ) :
    N ≤ m ^ 2 + 250 ↔ Nat.sqrt (N - 251) + 1 ≤ m := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hm : m ≤ Nat.sqrt (N - 251) := by omega
    have := Nat.le_sqrt'.1 hm
    omega
  · intro h
    by_contra hc
    push Not at hc
    have hm2 : m ^ 2 ≤ N - 251 := by omega
    have := Nat.le_sqrt'.2 hm2
    omega

/-- The count of squares within `250` of `N`, for `N ≥ 251`, as a `Finset.Icc`. -/
private lemma icc_eq_big (N : ℕ) (hN : 251 ≤ N) :
    {m : ℕ | N ≤ m ^ 2 + 250 ∧ m ^ 2 ≤ N + 250} =
      (↑(Finset.Icc (Nat.sqrt (N - 251) + 1) (Nat.sqrt (N + 250))) : Set ℕ) := by
  ext m
  simp only [Set.mem_ofPred_eq, Finset.coe_Icc, Set.mem_Icc]
  rw [lo_iff N hN m, Nat.le_sqrt']

/-- The count of squares within `250` of `N`, for `0 < N ≤ 250`, as a `Finset.Icc` from `0`. -/
private lemma icc_eq_small (N : ℕ) (hN2 : N ≤ 250) :
    {m : ℕ | N ≤ m ^ 2 + 250 ∧ m ^ 2 ≤ N + 250} =
      (↑(Finset.Icc 0 (Nat.sqrt (N + 250))) : Set ℕ) := by
  ext m
  simp only [Set.mem_ofPred_eq, Finset.coe_Icc, Set.mem_Icc, Nat.zero_le, true_and]
  constructor
  · rintro ⟨_, h2⟩
    exact Nat.le_sqrt'.2 h2
  · intro h
    exact ⟨by omega, Nat.le_sqrt'.1 h⟩

private lemma count_ne_15_of_small (N : ℕ) (hN1 : 0 < N) (hN2 : N ≤ 250) :
    ({m : ℕ | N ≤ m ^ 2 + 250 ∧ m ^ 2 ≤ N + 250} : Set ℕ).encard ≠ 15 := by
  rw [icc_eq_small N hN2, Set.encard_coe_eq_coe_finsetCard, Nat.card_Icc]
  have hmono : Nat.sqrt 251 ≤ Nat.sqrt (N + 250) := Nat.sqrt_le_sqrt (by omega)
  have h251 : Nat.sqrt 251 = 15 := by norm_num
  intro hcontra
  have : (Nat.sqrt (N + 250) + 1 - 0 : ℕ) = 15 := by exact_mod_cast hcontra
  omega

private lemma range_of_count_eq_15_big (N : ℕ) (hN : 251 ≤ N)
    (hcard : ({m : ℕ | N ≤ m ^ 2 + 250 ∧ m ^ 2 ≤ N + 250} : Set ℕ).encard = 15) :
    (315 ≤ N ∧ N ≤ 325) ∨ (332 ≤ N ∧ N ≤ 350) := by
  rw [icc_eq_big N hN, Set.encard_coe_eq_coe_finsetCard, Nat.card_Icc] at hcard
  have heq : (Nat.sqrt (N + 250) + 1 - (Nat.sqrt (N - 251) + 1) : ℕ) = 15 := by
    exact_mod_cast hcard
  have hb1 : Nat.sqrt (N - 251) ^ 2 ≤ N - 251 := Nat.sqrt_le' (N - 251)
  have hb2 : N - 251 < (Nat.sqrt (N - 251) + 1) ^ 2 := by
    simpa using Nat.lt_succ_sqrt' (N - 251)
  have hb3 : Nat.sqrt (N + 250) ^ 2 ≤ N + 250 := Nat.sqrt_le' (N + 250)
  have hb4 : N + 250 < (Nat.sqrt (N + 250) + 1) ^ 2 := by
    simpa using Nat.lt_succ_sqrt' (N + 250)
  generalize hk : Nat.sqrt (N - 251) = k at heq hb1 hb2
  generalize hj : Nat.sqrt (N + 250) = j at heq hb3 hb4
  have hA : k ^ 2 + 251 ≤ N := by omega
  have hB : N < (k + 1) ^ 2 + 251 := by omega
  have hjk : j = k + 15 := by omega
  rw [hjk] at hb3 hb4
  have hk_ge : 8 ≤ k := by nlinarith [hA, hb4]
  have hk_le : k ≤ 9 := by nlinarith [hB, hb3]
  interval_cases k <;> omega

private lemma count_eq_15_of_big (N : ℕ) (hN : 251 ≤ N)
    (hrange : (315 ≤ N ∧ N ≤ 325) ∨ (332 ≤ N ∧ N ≤ 350)) :
    ({m : ℕ | N ≤ m ^ 2 + 250 ∧ m ^ 2 ≤ N + 250} : Set ℕ).encard = 15 := by
  rw [icc_eq_big N hN, Set.encard_coe_eq_coe_finsetCard, Nat.card_Icc]
  rcases hrange with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : Nat.sqrt (N - 251) = 8 :=
      ((Nat.eq_sqrt' (a := 8) (n := N - 251)).mpr ⟨by norm_num; omega, by norm_num; omega⟩).symm
    have e2 : Nat.sqrt (N + 250) = 23 :=
      ((Nat.eq_sqrt' (a := 23) (n := N + 250)).mpr ⟨by norm_num; omega, by norm_num; omega⟩).symm
    rw [e1, e2]; norm_num
  · have e1 : Nat.sqrt (N - 251) = 9 :=
      ((Nat.eq_sqrt' (a := 9) (n := N - 251)).mpr ⟨by norm_num; omega, by norm_num; omega⟩).symm
    have e2 : Nat.sqrt (N + 250) = 24 :=
      ((Nat.eq_sqrt' (a := 24) (n := N + 250)).mpr ⟨by norm_num; omega, by norm_num; omega⟩).symm
    rw [e1, e2]; norm_num

theorem putnam_1994_b1
    (n : ℤ) :
    n ∈ putnam_1994_b1_solution ↔
    (0 < n ∧ {m : ℕ | |n - m ^ 2| ≤ 250}.encard = 15) := by
  have hset : ∀ N : ℕ, {m : ℕ | |(N : ℤ) - (m : ℤ) ^ 2| ≤ 250} =
      {m : ℕ | N ≤ m ^ 2 + 250 ∧ m ^ 2 ≤ N + 250} := set_eq
  constructor
  · intro hn
    have hn' : (315 ≤ n ∧ n ≤ 325) ∨ (332 ≤ n ∧ n ≤ 350) := hn
    have hpos : 0 < n := by rcases hn' with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    refine ⟨hpos, ?_⟩
    have hNn : ((n.toNat : ℤ)) = n := Int.toNat_of_nonneg hpos.le
    have hrw : {m : ℕ | |n - (m : ℤ) ^ 2| ≤ 250} =
        {m : ℕ | n.toNat ≤ m ^ 2 + 250 ∧ m ^ 2 ≤ n.toNat + 250} := by
      rw [← hNn]; exact hset n.toNat
    rw [hrw]
    apply count_eq_15_of_big n.toNat (by omega) (by omega)
  · rintro ⟨hpos, hcard⟩
    have hNn : ((n.toNat : ℤ)) = n := Int.toNat_of_nonneg hpos.le
    have hrw : {m : ℕ | |n - (m : ℤ) ^ 2| ≤ 250} =
        {m : ℕ | n.toNat ≤ m ^ 2 + 250 ∧ m ^ 2 ≤ n.toNat + 250} := by
      rw [← hNn]; exact hset n.toNat
    rw [hrw] at hcard
    rcases Nat.lt_or_ge n.toNat 251 with h250 | h251
    · exact absurd hcard (count_ne_15_of_small n.toNat (by omega) (by omega))
    · have hr := range_of_count_eq_15_big n.toNat h251 hcard
      rcases hr with ⟨a, b⟩ | ⟨a, b⟩
      · left; omega
      · right; omega

end MathProof.Challenges.C0034Putnam1994B1

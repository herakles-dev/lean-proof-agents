import MathProof.Basic

/-!
# Challenge C0028Putnam2004B1 — Putnam 2004 B1 (rational root ⇒ Horner partial sums are integers)

**Status:** ✅ SOLVED.

**Source:** PutnamBench `putnam_2004_b1` (trishullab/PutnamBench, Apache-2.0). No Mathlib
`Archive` formalization exists — an unaided, *harder* ceiling-test target.

Statement: for `P ∈ ℤ[X]` of degree `n` with a rational root `r`, each of the `n` Horner-style
partial sums `∑_{j≤i} c_{n-j} r^{i+1-j}` (i.e. `c_n r`, `c_n r² + c_{n-1} r`, …) is an integer.
The math needs the rational-root fact (`den r ∣ leadingCoeff`) plus a Horner induction — no single
Mathlib lemma closes it.
-/

namespace MathProof.Challenges.C0028Putnam2004B1

open Finset

/-- Clearing denominators: if `r = p / q` (as rationals) with `k ≤ m`, then
`c • r ^ k * q ^ m` (as a rational) is the cast of the integer `c * p ^ k * q ^ (m - k)`.
This one lemma is reused both to clear denominators in the root equation (`sgA`) and to relate
a Horner partial sum to its integer numerator (`sgB`). -/
private lemma term_cast (c p q : ℤ) (k m : ℕ) (hk : k ≤ m) (hq : (q : ℚ) ≠ 0) :
    (c : ℚ) * ((p : ℚ) / (q : ℚ)) ^ k * (q : ℚ) ^ m
      = ((c * p ^ k * q ^ (m - k) : ℤ) : ℚ) := by
  have e1 : (q : ℚ) ^ m = (q : ℚ) ^ k * (q : ℚ) ^ (m - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  have hqk : (q : ℚ) ^ k ≠ 0 := pow_ne_zero k hq
  rw [div_pow, e1]
  push_cast
  field_simp

/-- The crux divisibility: reindexing the tail of the cleared-denominator root equation shows
`q ^ (i+1)` divides `p ^ (n-1-i)` times the (integer) numerator of the `i`-th Horner partial
sum. -/
private lemma crux_dvd (n i : ℕ) (c : ℕ → ℤ) (p q : ℤ) (hi : i < n)
    (hSum : ∑ k ∈ Finset.range (n + 1), c k * p ^ k * q ^ (n - k) = 0) :
    q ^ (i + 1) ∣ p ^ (n - 1 - i) * ∑ j ∈ Finset.range (i + 1), c (n - j) * p ^ (i + 1 - j) * q ^ j := by
  -- Reindex the sum over `range (i+1)` (in `j`) to the sum over `Ico (n-i) (n+1)` (in `k = n - j`).
  have hreindex :
      p ^ (n - 1 - i) * ∑ j ∈ Finset.range (i + 1), c (n - j) * p ^ (i + 1 - j) * q ^ j
        = ∑ k ∈ Finset.Ico (n - i) (n + 1), c k * p ^ k * q ^ (n - k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_nbij' (fun j => n - j) (fun k => n - k)
    · intro j hj
      simp only [Finset.mem_range] at hj
      simp only [Finset.mem_Ico]
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      simp only [Finset.mem_range]
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      have hexp : (n - 1 - i) + (i + 1 - j) = n - j := by omega
      have hsub : n - (n - j) = j := by omega
      rw [hsub]
      calc p ^ (n - 1 - i) * (c (n - j) * p ^ (i + 1 - j) * q ^ j)
          = c (n - j) * (p ^ (i + 1 - j) * p ^ (n - 1 - i)) * q ^ j := by ring
        _ = c (n - j) * p ^ ((i + 1 - j) + (n - 1 - i)) * q ^ j := by rw [pow_add]
        _ = c (n - j) * p ^ (n - j) * q ^ j := by rw [show (i + 1 - j) + (n - 1 - i) = n - j by omega]
  -- Split the full (zero) sum into the head `range (n-i)` and the tail `Ico (n-i) (n+1)`.
  have hsplit :
      ∑ k ∈ Finset.range (n - i), c k * p ^ k * q ^ (n - k)
        + ∑ k ∈ Finset.Ico (n - i) (n + 1), c k * p ^ k * q ^ (n - k)
        = ∑ k ∈ Finset.range (n + 1), c k * p ^ k * q ^ (n - k) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)
  have htail : ∑ k ∈ Finset.Ico (n - i) (n + 1), c k * p ^ k * q ^ (n - k)
      = - ∑ k ∈ Finset.range (n - i), c k * p ^ k * q ^ (n - k) := by
    rw [hSum] at hsplit
    linarith [hsplit]
  rw [hreindex, htail]
  apply Dvd.dvd.neg_right
  apply Finset.dvd_sum
  intro k hk
  simp only [Finset.mem_range] at hk
  have : q ^ (i + 1) ∣ q ^ (n - k) := pow_dvd_pow q (by omega)
  exact this.mul_left (c k * p ^ k)

theorem putnam_2004_b1
    (n : ℕ) (P : Polynomial ℤ) (r : ℚ)
    (Pdeg : P.degree = n)
    (Preq0 : Polynomial.aeval r P = 0) :
    ∀ i ∈ Finset.range n, ∃ m : ℤ,
      m = ∑ j ∈ Finset.range (i + 1), (P.coeff (n - j) * r ^ (i + 1 - j)) := by
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  set p : ℤ := r.num with hp
  set q : ℤ := (r.den : ℤ) with hq
  have hqpos : 0 < q := by rw [hq]; exact_mod_cast r.pos
  have hqne : (q : ℚ) ≠ 0 := by
    have : (q : ℚ) ≠ 0 := by exact_mod_cast hqpos.ne'
    exact this
  have hcop : IsCoprime p q := by rw [hp, hq]; exact Rat.isCoprime_num_den r
  have hrpq : r = (p : ℚ) / (q : ℚ) := by rw [hp, hq]; exact (Rat.num_div_den r).symm
  -- sgA: clear denominators in the root equation.
  have hdeg : P.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some Pdeg
  have haeval0 : ∑ k ∈ Finset.range (n + 1), (P.coeff k : ℚ) * r ^ k = 0 := by
    have h1 := Polynomial.aeval_eq_sum_range (R := ℤ) (S := ℚ) (p := P) r
    rw [hdeg] at h1
    simp only [Algebra.smul_def, algebraMap_int_eq, eq_intCast] at h1
    rw [← h1]; exact Preq0
  have hSumZ : ∑ k ∈ Finset.range (n + 1), P.coeff k * p ^ k * q ^ (n - k) = 0 := by
    have h2 : (∑ k ∈ Finset.range (n + 1), (P.coeff k : ℚ) * r ^ k) * (q : ℚ) ^ n = 0 := by
      rw [haeval0]; ring
    rw [Finset.sum_mul] at h2
    have h3 : ∀ k ∈ Finset.range (n + 1),
        (P.coeff k : ℚ) * r ^ k * (q : ℚ) ^ n
          = ((P.coeff k * p ^ k * q ^ (n - k) : ℤ) : ℚ) := by
      intro k hk
      have hkn : k ≤ n := by
        simp only [Finset.mem_range] at hk; omega
      rw [hrpq]; exact term_cast (P.coeff k) p q k n hkn hqne
    rw [Finset.sum_congr rfl h3] at h2
    rw [← Int.cast_sum] at h2
    exact_mod_cast h2
  -- sgC: the crux divisibility.
  have hdvd := crux_dvd n i P.coeff p q hi' hSumZ
  -- sgD: peel off the coprime factor.
  have hcop' : IsCoprime (q ^ (i + 1)) (p ^ (n - 1 - i)) := hcop.symm.pow
  have hdvdA : q ^ (i + 1) ∣ ∑ j ∈ Finset.range (i + 1), P.coeff (n - j) * p ^ (i + 1 - j) * q ^ j :=
    hcop'.dvd_of_dvd_mul_left hdvd
  obtain ⟨m, hm⟩ := hdvdA
  -- sgB: relate the rational Horner sum to its integer numerator.
  have hsB : (∑ j ∈ Finset.range (i + 1), (P.coeff (n - j) : ℚ) * r ^ (i + 1 - j)) * (q : ℚ) ^ (i + 1)
      = ((∑ j ∈ Finset.range (i + 1), P.coeff (n - j) * p ^ (i + 1 - j) * q ^ j : ℤ) : ℚ) := by
    rw [Finset.sum_mul]
    have h4 : ∀ j ∈ Finset.range (i + 1),
        (P.coeff (n - j) : ℚ) * r ^ (i + 1 - j) * (q : ℚ) ^ (i + 1)
          = ((P.coeff (n - j) * p ^ (i + 1 - j) * q ^ j : ℤ) : ℚ) := by
      intro j hj
      have hjle : i + 1 - j ≤ i + 1 := Nat.sub_le _ _
      have hjeq : i + 1 - (i + 1 - j) = j := by
        simp only [Finset.mem_range] at hj; omega
      rw [hrpq]
      have := term_cast (P.coeff (n - j)) p q (i + 1 - j) (i + 1) hjle hqne
      rwa [hjeq] at this
    rw [Finset.sum_congr rfl h4, ← Int.cast_sum]
  refine ⟨m, ?_⟩
  have hqi1ne : (q : ℚ) ^ (i + 1) ≠ 0 := pow_ne_zero _ hqne
  have : (∑ j ∈ Finset.range (i + 1), (P.coeff (n - j) : ℚ) * r ^ (i + 1 - j)) * (q : ℚ) ^ (i + 1)
      = (m : ℚ) * (q : ℚ) ^ (i + 1) := by
    rw [hsB, hm]; push_cast; ring
  have := mul_right_cancel₀ hqi1ne this
  exact_mod_cast this.symm

end MathProof.Challenges.C0028Putnam2004B1

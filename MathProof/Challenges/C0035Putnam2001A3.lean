import MathProof.Basic

/-!
# Challenge C0035Putnam2001A3 — Putnam 2001 A3 (when Pₘ(x)=x⁴−(2m+4)x²+(m−2)² factors over ℤ)

**Status:** ✅ SOLVED (cold — Sonnet `lean-prover`).

**Source:** PutnamBench `putnam_2001_a3` (trishullab/PutnamBench, Apache-2.0). No Mathlib
`Archive` formalization exists. Statement reproduced **verbatim** from upstream (the
`proof-auditor` diffs against the cache; never weaken it). *Determine-and-prove*: fill
`putnam_2001_a3_solution` with the correct set, then prove the equality.

Statement: for which integers `m` is `Pₘ(x) = x⁴ − (2m+4)x² + (m−2)²` a product of two
non-constant polynomials with integer coefficients?
-/

namespace MathProof.Challenges.C0035Putnam2001A3

open Polynomial Set

abbrev putnam_2001_a3_solution : Set ℤ := {m : ℤ | ∃ k : ℤ, k^2 = m ∨ 2*k^2 = m}
-- upstream answer: {m : ℤ | ∃ k : ℤ, k^2 = m ∨ 2*k^2 = m}

/-! ## Helper lemmas -/

/-- If `2 ∣ n^2` then `2 ∣ n`, for `n : ℤ` (prime `2`). -/
private lemma two_dvd_of_dvd_sq {n : ℤ} (h : (2 : ℤ) ∣ n ^ 2) : (2 : ℤ) ∣ n :=
  Int.prime_two.dvd_of_dvd_pow h

/-- Infinite-descent lemma: `s² = 2r²` forces `r = 0` (the classical irrationality-of-√2
argument, done over `ℤ` by strong induction on `r.natAbs`). -/
private lemma eq_zero_of_sq_eq_two_mul_sq :
    ∀ n : ℕ, ∀ s r : ℤ, r.natAbs = n → s ^ 2 = 2 * r ^ 2 → r = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s r hrn hsr
    rcases eq_or_ne r 0 with hr0 | hr0
    · exact hr0
    · exfalso
      have h2s : (2 : ℤ) ∣ s := two_dvd_of_dvd_sq ⟨r ^ 2, hsr⟩
      obtain ⟨t, ht⟩ := h2s
      have hs2 : s ^ 2 = 4 * t ^ 2 := by rw [ht]; ring
      have ht2 : r ^ 2 = 2 * t ^ 2 := by linarith [hsr, hs2]
      have h2r : (2 : ℤ) ∣ r := two_dvd_of_dvd_sq ⟨t ^ 2, ht2⟩
      obtain ⟨u, hu⟩ := h2r
      have hune : u ≠ 0 := by rintro rfl; simp at hu; exact hr0 hu
      have hr2 : r ^ 2 = 4 * u ^ 2 := by rw [hu]; ring
      have hut : t ^ 2 = 2 * u ^ 2 := by linarith [ht2, hr2]
      have hu_lt : u.natAbs < n := by
        have hmul : r.natAbs = 2 * u.natAbs := by
          rw [hu, Int.natAbs_mul]; norm_num
        have : 0 < u.natAbs := Int.natAbs_pos.mpr hune
        omega
      have huz : u = 0 := ih u.natAbs hu_lt t u rfl hut
      exact hune huz

/-- `d² = 32m` forces `m` to be twice a perfect square (three rounds of "square even ⇒
base even", no infinite descent needed since `32` is fixed). -/
private lemma exists_of_sq_eq_32_mul {d m : ℤ} (h : d ^ 2 = 32 * m) : ∃ k : ℤ, m = 2 * k ^ 2 := by
  have h2 : (2 : ℤ) ∣ d := two_dvd_of_dvd_sq ⟨16 * m, by linarith⟩
  obtain ⟨e, he⟩ := h2
  have hd2 : d ^ 2 = 4 * e ^ 2 := by rw [he]; ring
  have he2 : e ^ 2 = 8 * m := by linarith [h, hd2]
  have h2' : (2 : ℤ) ∣ e := two_dvd_of_dvd_sq ⟨4 * m, by linarith⟩
  obtain ⟨f, hf⟩ := h2'
  have he2' : e ^ 2 = 4 * f ^ 2 := by rw [hf]; ring
  have hf2 : f ^ 2 = 2 * m := by linarith [he2, he2']
  have h2'' : (2 : ℤ) ∣ f := two_dvd_of_dvd_sq ⟨m, by linarith⟩
  obtain ⟨g, hg⟩ := h2''
  have hf2' : f ^ 2 = 4 * g ^ 2 := by rw [hg]; ring
  exact ⟨g, by linarith [hf2, hf2']⟩

/-- A polynomial of `natDegree ≤ 2` is determined by its first three coefficients. -/
private lemma eq_C_add_C_mul_X_add_C_mul_X_sq {p : Polynomial ℤ} (h : p.natDegree ≤ 2) :
    p = C (p.coeff 0) + C (p.coeff 1) * X + C (p.coeff 2) * X ^ 2 := by
  have key : ∀ n : ℕ,
      (C (p.coeff 0) + C (p.coeff 1) * X + C (p.coeff 2) * X ^ 2).coeff n =
        if n = 0 then p.coeff 0 else if n = 1 then p.coeff 1 else if n = 2 then p.coeff 2 else 0 := by
    intro n
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X]
    rcases n with _ | _ | _ | n <;> simp
  ext n
  rw [key n]
  match n with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | (n + 3) =>
    have hlt : p.natDegree < n + 3 := by omega
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]

/-- Sufficiency: `m = k²` gives the "conjugate quadratics" factorization. -/
private lemma factors_of_sq (k : ℤ) :
    (Polynomial.X : Polynomial ℤ) ^ 4 - C (2 * k ^ 2 + 4) * X ^ 2 + C ((k ^ 2 - 2) ^ 2)
      = (X ^ 2 + C (2 * k) * X + C (k ^ 2 - 2)) * (X ^ 2 - C (2 * k) * X + C (k ^ 2 - 2)) := by
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

/-- Sufficiency: `m = 2k²` gives the "difference of biquadratics" factorization. -/
private lemma factors_of_two_mul_sq (k : ℤ) :
    (Polynomial.X : Polynomial ℤ) ^ 4 - C (2 * (2 * k ^ 2) + 4) * X ^ 2 +
        C (((2 * k ^ 2) - 2) ^ 2)
      = (X ^ 2 - C (2 * (k - 1) ^ 2)) * (X ^ 2 - C (2 * (k + 1) ^ 2)) := by
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one]
  ring

private lemma sq_ne_eight (x : ℤ) : x ^ 2 ≠ 8 := by
  intro h
  have h1 : x < 3 := by nlinarith [sq_nonneg (x - 3)]
  have h2 : -3 < x := by nlinarith [sq_nonneg (x + 3)]
  interval_cases x <;> norm_num at h

/-- Necessity, linear-factor case: if `a` (of matching-degree complementary factor `b`) has
`natDegree 1`, `Pₘ` has an integer root, forcing `m = 2`. -/
private lemma m_eq_two_of_natDegree_eq_one {m : ℤ} {a b : Polynomial ℤ}
    (hab : (X : Polynomial ℤ) ^ 4 - C (2 * m + 4) * X ^ 2 + C ((m - 2) ^ 2) = a * b)
    (ha1 : a.natDegree = 1) (hdeg : a.natDegree + b.natDegree = 4) : m = 2 := by
  obtain ⟨p, q, hapq⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one (le_of_eq ha1)
  have hp_eq : a.coeff 1 = p := by
    rw [hapq]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_C]
    norm_num
  have h4 : (a * b).coeff (a.natDegree + b.natDegree) = a.leadingCoeff * b.leadingCoeff :=
    Polynomial.coeff_mul_degree_add_degree a b
  rw [hdeg, ← hab] at h4
  have hQ4 : ((X : Polynomial ℤ) ^ 4 - C (2 * m + 4) * X ^ 2 + C ((m - 2) ^ 2)).coeff 4 = 1 := by
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_C_mul]
    norm_num
  rw [hQ4] at h4
  have haLead : a.leadingCoeff = p := by
    rw [Polynomial.leadingCoeff, ha1, hp_eq]
  rw [haLead] at h4
  have hp2 : p ^ 2 = 1 := by
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h4.symm with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rw [h1] <;> ring
  set r := -q * p with hr_def
  have haval : a.eval r = 0 := by
    rw [hapq]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [hr_def]
    linear_combination -q * hp2
  have hQval : ((X : Polynomial ℤ) ^ 4 - C (2 * m + 4) * X ^ 2 + C ((m - 2) ^ 2)).eval r = 0 := by
    rw [hab, Polynomial.eval_mul, haval, zero_mul]
  have hQval' : r ^ 4 - (2 * m + 4) * r ^ 2 + (m - 2) ^ 2 = 0 := by
    simpa [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X] using hQval
  have hsq : (m - r ^ 2 - 2) ^ 2 = 2 * (2 * r) ^ 2 := by linear_combination hQval'
  have h2r0 : 2 * r = 0 :=
    eq_zero_of_sq_eq_two_mul_sq (2 * r).natAbs (m - r ^ 2 - 2) (2 * r) rfl hsq
  have hr0 : r = 0 := by omega
  rw [hr0] at hQval'
  nlinarith [hQval']

/-- Necessity, quadratic-quadratic case. -/
private lemma exists_of_natDegree_eq_two {m : ℤ} {a b : Polynomial ℤ}
    (hab : (X : Polynomial ℤ) ^ 4 - C (2 * m + 4) * X ^ 2 + C ((m - 2) ^ 2) = a * b)
    (ha2 : a.natDegree = 2) (hb2 : b.natDegree = 2) :
    ∃ k : ℤ, k ^ 2 = m ∨ 2 * k ^ 2 = m := by
  have haeq := eq_C_add_C_mul_X_add_C_mul_X_sq (le_of_eq ha2)
  have hbeq := eq_C_add_C_mul_X_add_C_mul_X_sq (le_of_eq hb2)
  rw [haeq, hbeq] at hab
  set a0 := a.coeff 0
  set a1 := a.coeff 1
  set a2 := a.coeff 2
  set b0 := b.coeff 0
  set b1 := b.coeff 1
  set b2 := b.coeff 2
  have hexpand : (C a0 + C a1 * X + C a2 * X ^ 2) * (C b0 + C b1 * X + C b2 * X ^ 2) =
      C (a0 * b0) + C (a0 * b1 + a1 * b0) * X + C (a0 * b2 + a1 * b1 + a2 * b0) * X ^ 2 +
        C (a1 * b2 + a2 * b1) * X ^ 3 + C (a2 * b2) * X ^ 4 := by
    simp only [map_add, map_mul]
    ring
  rw [hexpand] at hab
  have e0 : (m - 2) ^ 2 = a0 * b0 := by
    have h := congrArg (Polynomial.coeff · 0) hab
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X] at h
    simpa using h
  have e1 : (0 : ℤ) = a0 * b1 + a1 * b0 := by
    have h := congrArg (Polynomial.coeff · 1) hab
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X] at h
    simpa using h
  have e2 : -(2 * m + 4) = a0 * b2 + a1 * b1 + a2 * b0 := by
    have h := congrArg (Polynomial.coeff · 2) hab
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X] at h
    simpa using h
  have e3 : (0 : ℤ) = a1 * b2 + a2 * b1 := by
    have h := congrArg (Polynomial.coeff · 3) hab
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X] at h
    simpa using h
  have e4 : (1 : ℤ) = a2 * b2 := by
    have h := congrArg (Polynomial.coeff · 4) hab
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X] at h
    simpa using h
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp e4.symm with ⟨ha2v, hb2v⟩ | ⟨ha2v, hb2v⟩
  · -- a2 = 1, b2 = 1
    rw [ha2v, hb2v] at e2 e3
    have hb1 : b1 = -a1 := by linarith [e3]
    rw [hb1] at e1 e2
    have e1' : a1 * (b0 - a0) = 0 := by linear_combination -e1
    rcases mul_eq_zero.mp e1' with ha1 | hdiff
    · rw [ha1] at e2
      have hsum : a0 + b0 = -(2 * m + 4) := by linarith [e2]
      have hsq : (a0 - b0) ^ 2 = 32 * m := by
        linear_combination (a0 + b0 - 2 * m - 4) * hsum + 4 * e0
      obtain ⟨k, hk⟩ := exists_of_sq_eq_32_mul hsq
      exact ⟨k, Or.inr hk.symm⟩
    · have hc : a0 = b0 := by linarith [hdiff]
      have e0' : b0 ^ 2 = (m - 2) ^ 2 := by linear_combination -e0 - b0 * hc
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp e0' with hcm | hcm
      · -- b0 = m - 2 ⟹ a1² = 4m
        have ha1sq : a1 ^ 2 = 4 * m := by linear_combination e2 + hc + 2 * hcm
        have h2a1 : (2 : ℤ) ∣ a1 := two_dvd_of_dvd_sq ⟨2 * m, by linarith [ha1sq]⟩
        obtain ⟨k, hk⟩ := h2a1
        have hksq : a1 ^ 2 = 4 * k ^ 2 := by linear_combination (a1 + 2 * k) * hk
        exact ⟨k, Or.inl (by linarith [ha1sq, hksq])⟩
      · -- b0 = 2 - m ⟹ a1² = 8, contradiction
        exact absurd (show a1 ^ 2 = 8 by linear_combination e2 + hc + 2 * hcm) (sq_ne_eight a1)
  · -- a2 = -1, b2 = -1
    rw [ha2v, hb2v] at e2 e3
    have hb1 : b1 = -a1 := by linarith [e3]
    rw [hb1] at e1 e2
    have e1' : a1 * (b0 - a0) = 0 := by linear_combination -e1
    rcases mul_eq_zero.mp e1' with ha1 | hdiff
    · rw [ha1] at e2
      have hsum : a0 + b0 = 2 * m + 4 := by linarith [e2]
      have hsq : (a0 - b0) ^ 2 = 32 * m := by
        linear_combination (a0 + b0 + 2 * m + 4) * hsum + 4 * e0
      obtain ⟨k, hk⟩ := exists_of_sq_eq_32_mul hsq
      exact ⟨k, Or.inr hk.symm⟩
    · have hc : a0 = b0 := by linarith [hdiff]
      have e0' : b0 ^ 2 = (m - 2) ^ 2 := by linear_combination -e0 - b0 * hc
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp e0' with hcm | hcm
      · -- b0 = m - 2 ⟹ a1² = 8, contradiction (flipped vs. the a2 = 1 branch)
        exact absurd (show a1 ^ 2 = 8 by linear_combination e2 - hc - 2 * hcm) (sq_ne_eight a1)
      · -- b0 = 2 - m ⟹ a1² = 4m
        have ha1sq : a1 ^ 2 = 4 * m := by linear_combination e2 - hc - 2 * hcm
        have h2a1 : (2 : ℤ) ∣ a1 := two_dvd_of_dvd_sq ⟨2 * m, by linarith [ha1sq]⟩
        obtain ⟨k, hk⟩ := h2a1
        have hksq : a1 ^ 2 = 4 * k ^ 2 := by linear_combination (a1 + 2 * k) * hk
        exact ⟨k, Or.inl (by linarith [ha1sq, hksq])⟩

theorem putnam_2001_a3
(P : ℤ → Polynomial ℤ)
(hP : P = fun m : ℤ => (Polynomial.X)^4 - (Polynomial.C (2*m + 4))*(Polynomial.X)^2 + Polynomial.C ((m - 2)^2))
: {m : ℤ | ∃ a b, P m = a * b ∧
(∃ n ∈ Ici 1, a.coeff n ≠ 0) ∧ (∃ n ∈ Ici 1, b.coeff n ≠ 0)} = putnam_2001_a3_solution := by
  subst hP
  ext m
  simp only [Set.mem_ofPred_eq, putnam_2001_a3_solution]
  constructor
  · rintro ⟨a, b, hab, ⟨na, hna1, hna2⟩, ⟨nb, hnb1, hnb2⟩⟩
    have ha0 : a ≠ 0 := fun h => hna2 (by rw [h]; simp)
    have hb0 : b ≠ 0 := fun h => hnb2 (by rw [h]; simp)
    have hadeg1 : 1 ≤ a.natDegree := le_trans hna1 (Polynomial.le_natDegree_of_ne_zero hna2)
    have hbdeg1 : 1 ≤ b.natDegree := le_trans hnb1 (Polynomial.le_natDegree_of_ne_zero hnb2)
    have hQdeg : ((X : Polynomial ℤ) ^ 4 - C (2 * m + 4) * X ^ 2 + C ((m - 2) ^ 2)).natDegree
        = 4 := by
      compute_degree!
    have hprod_deg : (a * b).natDegree = 4 := by rw [← hab]; exact hQdeg
    have hsum : a.natDegree + b.natDegree = 4 := by
      rw [Polynomial.natDegree_mul ha0 hb0] at hprod_deg; exact hprod_deg
    have hcase : a.natDegree = 1 ∨ a.natDegree = 2 ∨ a.natDegree = 3 := by omega
    rcases hcase with h1 | h2 | h3
    · have hm2 := m_eq_two_of_natDegree_eq_one hab h1 hsum
      exact ⟨1, Or.inr (by rw [hm2]; ring)⟩
    · have hb2 : b.natDegree = 2 := by omega
      exact exists_of_natDegree_eq_two hab h2 hb2
    · have hb1 : b.natDegree = 1 := by omega
      have hab' : (X : Polynomial ℤ) ^ 4 - C (2 * m + 4) * X ^ 2 + C ((m - 2) ^ 2) = b * a := by
        rw [hab, mul_comm]
      have hm2 := m_eq_two_of_natDegree_eq_one hab' hb1 (by omega)
      exact ⟨1, Or.inr (by rw [hm2]; ring)⟩
  · rintro ⟨k, hk | hk⟩
    · subst hk
      refine ⟨X ^ 2 + C (2 * k) * X + C (k ^ 2 - 2), X ^ 2 - C (2 * k) * X + C (k ^ 2 - 2),
        factors_of_sq k, ⟨2, by norm_num [Set.mem_Ici], ?_⟩, ⟨2, by norm_num [Set.mem_Ici], ?_⟩⟩
      · simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
          Polynomial.coeff_X, Polynomial.coeff_C]
        norm_num
      · simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
          Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]
        norm_num
    · subst hk
      refine ⟨X ^ 2 - C (2 * (k - 1) ^ 2), X ^ 2 - C (2 * (k + 1) ^ 2),
        factors_of_two_mul_sq k, ⟨2, by norm_num [Set.mem_Ici], ?_⟩,
        ⟨2, by norm_num [Set.mem_Ici], ?_⟩⟩
      · simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
        norm_num
      · simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
        norm_num

end MathProof.Challenges.C0035Putnam2001A3

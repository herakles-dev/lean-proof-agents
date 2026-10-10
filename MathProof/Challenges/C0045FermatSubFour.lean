import MathProof.Basic

set_option autoImplicit false

/-!
# Challenge C0045 — Fermat's right-triangle theorem, quartic `−` form `x⁴ − y⁴ = z²`

**Status:** ✅ SOLVED.

The `−` mirror of Mathlib's `not_fermat_42` (`a⁴ + b⁴ ≠ c²`, `Mathlib/NumberTheory/FLT/Four.lean`)
and the explicit form of **Fermat's right-triangle theorem** (no Pythagorean triangle has square
area). A genuine Mathlib gap; together with C0043's `no_four_squares_in_ap` it completes the
right-triangle theorem family.

**Faithful statement (anti-vacuity).** The naive `a⁴ − b⁴ ≠ c²` is *false* — the trivial family
`a = ±b, c = 0` satisfies it. The real content is that those are the *only* solutions: for nonzero
`a, b`, `a⁴ − b⁴ = c²` forces `c = 0`.

**Proof route.** `a⁴ − b⁴ = c²` ⟹ `c² + (b²)² = (a²)²`, a Pythagorean triple with hypotenuse `a²`.
Take a minimal counterexample (measured by `a.natAbs`); it is coprime. Classify the triple; the
parity of `b` gives two forks, each producing a strictly smaller solution of the *same* equation:

* `b` odd (`c` even): classify `(b², c, a²)`. With `b² = m²−n²`, `a² = m²+n²` we get
  `(a·b)² = a²·b² = m⁴ − n⁴`, a solution `(m, n, a·b)` with `m.natAbs < a.natAbs`.
* `b` even (`c` odd): classify `(c, b², a²)`, then classify `a² = p²+q²` (WLOG `p` odd), then
  `(b/2)² = r·s·(r²−s²)` with the three factors pairwise coprime, hence each a square:
  `r = i²`, `s² = j⁴`, `r²−s² = ±k²`, giving `i⁴ − j⁴ = ±k²`, a solution with smaller `a.natAbs`.

A structural clone of `Fermat42.not_minimal` with `+ → −`.
-/

namespace MathProof.Challenges.C0045FermatSubFour

/-- A nontrivial solution of `a⁴ − b⁴ = c²`. -/
private def FS (a b c : ℤ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 - b ^ 4 = c ^ 2 ∧ c ≠ 0

/-- A minimal solution (smallest `a.natAbs`). -/
private def Min (a b c : ℤ) : Prop :=
  FS a b c ∧ ∀ a1 b1 c1 : ℤ, FS a1 b1 c1 → a.natAbs ≤ a1.natAbs

/-- If there is a solution there is a minimal one. -/
private theorem exists_minimal {a b c : ℤ} (h : FS a b c) : ∃ a0 b0 c0, Min a0 b0 c0 := by
  classical
  let S : Set ℕ := { n | ∃ s : ℤ × ℤ × ℤ, FS s.1 s.2.1 s.2.2 ∧ n = Int.natAbs s.1 }
  have hne : S.Nonempty := ⟨a.natAbs, ⟨(a, b, c), h, rfl⟩⟩
  obtain ⟨s0, hs0, hs1⟩ := Nat.find_spec hne
  refine ⟨s0.1, s0.2.1, s0.2.2, hs0, ?_⟩
  intro a1 b1 c1 h1
  rw [← hs1]
  exact Nat.find_min' hne ⟨(a1, b1, c1), h1, rfl⟩

/-- A minimal solution is coprime. -/
private theorem coprime_of_minimal {a b c : ℤ} (h : Min a b c) : IsCoprime a b := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  by_contra hab
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hab
  obtain ⟨a1, rfl⟩ := Int.natCast_dvd.mpr hpa
  obtain ⟨b1, rfl⟩ := Int.natCast_dvd.mpr hpb
  have hpc : (p : ℤ) ^ 2 ∣ c := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero, ← h.1.2.2.1]
    exact ⟨a1 ^ 4 - b1 ^ 4, by ring⟩
  obtain ⟨c1, rfl⟩ := hpc
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hf : FS a1 b1 c1 := by
    refine ⟨right_ne_zero_of_mul h.1.1, right_ne_zero_of_mul h.1.2.1, ?_,
      right_ne_zero_of_mul h.1.2.2.2⟩
    apply (mul_right_inj' (pow_ne_zero 4 hp0)).mp
    linear_combination h.1.2.2.1
  apply Nat.le_lt_asymm (h.2 _ _ _ hf)
  rw [Int.natAbs_mul, lt_mul_iff_one_lt_left, Int.natAbs_natCast]
  · exact hp.one_lt
  · exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.2 hf.1)

/-- Absolute-value normalization: solutions only depend on `|a|, |b|, |c|`. -/
private theorem FS_abs {a b c : ℤ} (h : FS a b c) : FS |a| |b| |c| := by
  obtain ⟨ha, hb, he, hc⟩ := h
  refine ⟨abs_ne_zero.mpr ha, abs_ne_zero.mpr hb, ?_, abs_ne_zero.mpr hc⟩
  have e1 : |a| ^ 4 = a ^ 4 := by rw [show |a| ^ 4 = (|a| ^ 2) ^ 2 by ring, sq_abs]; ring
  have e2 : |b| ^ 4 = b ^ 4 := by rw [show |b| ^ 4 = (|b| ^ 2) ^ 2 by ring, sq_abs]; ring
  have e3 : |c| ^ 2 = c ^ 2 := sq_abs c
  rw [e1, e2, e3]; exact he

/-- The hard fork (`b` even). Given the second-level Pythagorean data `a² = P²+Q²`, `b² = 2PQ`
with `P` odd, coprime and nonzero, classify `a² = P²+Q²` and produce a strictly smaller solution
of `x⁴ − y⁴ = z²`, contradicting minimality. -/
private theorem caseB_tail {a b P Q : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hmin2 : ∀ a1 b1 c1 : ℤ, FS a1 b1 c1 → a.natAbs ≤ a1.natAbs)
    (hqa : a ^ 2 = P ^ 2 + Q ^ 2) (hqb : b ^ 2 = 2 * P * Q)
    (hgcdPQ : Int.gcd P Q = 1) (hPodd : P % 2 = 1)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) : False := by
  have htri2 : PythagoreanTriple P Q a := by delta PythagoreanTriple; linear_combination -hqa
  obtain ⟨r, s, hr1, hr2, hr3, hr4, _hr5, hr6⟩ := htri2.coprime_classification' hgcdPQ hPodd ha
  -- P = r²−s², Q = 2rs, a = r²+s², gcd r s = 1, 0 ≤ r
  have hrne : r ≠ 0 := by intro h; apply hQ0; rw [hr2, h]; ring
  have hsne : s ≠ 0 := by intro h; apply hQ0; rw [hr2, h]; ring
  have hdne : r ^ 2 - s ^ 2 ≠ 0 := by rw [← hr1]; exact hP0
  have hrpos : 0 < r := lt_of_le_of_ne hr6 (Ne.symm hrne)
  -- (b/2)² = r · s · (r²−s²)
  have hbe : (2 : ℤ) ∣ b := by
    have h4 : b ^ 2 = (2 : ℤ) ^ 2 * (r * s * (r ^ 2 - s ^ 2)) := by rw [hqb, hr1, hr2]; ring
    exact (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨r * s * (r ^ 2 - s ^ 2), h4⟩
  obtain ⟨b', rfl⟩ := hbe
  have hb'2 : b' ^ 2 = r * s * (r ^ 2 - s ^ 2) := by
    have h5 : 4 * b' ^ 2 = 4 * (r * s * (r ^ 2 - s ^ 2)) := by
      rw [hr1, hr2] at hqb; linear_combination hqb
    linarith
  -- pairwise coprimality of the three factors
  have cop_rs : IsCoprime r s := Int.isCoprime_iff_gcd_eq_one.mpr hr4
  have cop_r_d : IsCoprime r (r ^ 2 - s ^ 2) := by
    have h1 : IsCoprime r (-(s ^ 2)) := (cop_rs.pow_right (n := 2)).neg_right
    have h2 := h1.add_mul_left_right r
    rwa [show -(s ^ 2) + r * r = r ^ 2 - s ^ 2 by ring] at h2
  have cop_s_d : IsCoprime s (r ^ 2 - s ^ 2) := by
    have h1 : IsCoprime s (r ^ 2) := cop_rs.symm.pow_right (n := 2)
    have h2 := h1.add_mul_left_right (-s)
    rwa [show r ^ 2 + s * -s = r ^ 2 - s ^ 2 by ring] at h2
  -- each factor is ± a square
  obtain ⟨i, hi⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp (cop_rs.mul_right cop_r_d))
    (show r * (s * (r ^ 2 - s ^ 2)) = b' ^ 2 by rw [hb'2]; ring)
  obtain ⟨j, hj⟩ := Int.sq_of_gcd_eq_one
    (Int.isCoprime_iff_gcd_eq_one.mp (cop_rs.symm.mul_right cop_s_d))
    (show s * (r * (r ^ 2 - s ^ 2)) = b' ^ 2 by rw [hb'2]; ring)
  obtain ⟨k, hk⟩ := Int.sq_of_gcd_eq_one
    (Int.isCoprime_iff_gcd_eq_one.mp (cop_r_d.symm.mul_right cop_s_d.symm))
    (show (r ^ 2 - s ^ 2) * (r * s) = b' ^ 2 by rw [hb'2]; ring)
  have hine : i ≠ 0 := by intro h; apply hrne; rcases hi with e | e <;> rw [e, h] <;> ring
  have hjne : j ≠ 0 := by intro h; apply hsne; rcases hj with e | e <;> rw [e, h] <;> ring
  have hkne : k ≠ 0 := by intro h; apply hdne; rcases hk with e | e <;> rw [e, h] <;> ring
  -- resolve signs where positivity forces them
  have hri : r = i ^ 2 := by
    rcases hi with e | e
    · exact e
    · exfalso; rw [e] at hrpos; nlinarith [sq_nonneg i]
  have hsj : s ^ 2 = j ^ 4 := by rcases hj with e | e <;> rw [e] <;> ring
  have haij : a = i ^ 4 + j ^ 4 := by rw [hr3, hri, hsj]; ring
  rcases hk with hkp | hkn
  · -- r²−s² = k² : solution (i, j, k)
    have heqnew : i ^ 4 - j ^ 4 = k ^ 2 := by
      have hstep : i ^ 4 - j ^ 4 = r ^ 2 - s ^ 2 := by
        rw [← hsj, show i ^ 4 = (i ^ 2) ^ 2 by ring, ← hri]
      rw [hstep]; exact hkp
    have hmeas : i.natAbs < a.natAbs := by
      apply Int.ofNat_lt.mp
      rw [Int.natAbs_of_nonneg (le_of_lt ha)]
      have hj4 : (0 : ℤ) < j ^ 4 := by
        rw [show j ^ 4 = (j ^ 2) ^ 2 by ring]; exact sq_pos_of_ne_zero (pow_ne_zero 2 hjne)
      calc (i.natAbs : ℤ) ≤ i ^ 2 := Int.natAbs_le_self_sq i
        _ ≤ (i ^ 2) ^ 2 := Int.le_self_sq _
        _ = i ^ 4 := by ring
        _ < i ^ 4 + j ^ 4 := by linarith
        _ = a := haij.symm
    exact absurd (hmin2 i j k ⟨hine, hjne, heqnew, hkne⟩) (not_le.mpr hmeas)
  · -- r²−s² = −k² : solution (j, i, k)
    have heqnew : j ^ 4 - i ^ 4 = k ^ 2 := by
      have hstep : j ^ 4 - i ^ 4 = -(r ^ 2 - s ^ 2) := by
        rw [← hsj, show i ^ 4 = (i ^ 2) ^ 2 by ring, ← hri]; ring
      rw [hstep, hkn]; ring
    have hmeas : j.natAbs < a.natAbs := by
      apply Int.ofNat_lt.mp
      rw [Int.natAbs_of_nonneg (le_of_lt ha)]
      have hi4 : (0 : ℤ) < i ^ 4 := by
        rw [show i ^ 4 = (i ^ 2) ^ 2 by ring]; exact sq_pos_of_ne_zero (pow_ne_zero 2 hine)
      calc (j.natAbs : ℤ) ≤ j ^ 2 := Int.natAbs_le_self_sq j
        _ ≤ (j ^ 2) ^ 2 := Int.le_self_sq _
        _ = j ^ 4 := by ring
        _ < i ^ 4 + j ^ 4 := by linarith
        _ = a := haij.symm
    exact absurd (hmin2 j i k ⟨hjne, hine, heqnew, hkne⟩) (not_le.mpr hmeas)

/-- The descent: a minimal positive solution is impossible. -/
private theorem descent {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (_hc : 0 < c)
    (hmin : Min a b c) : False := by
  obtain ⟨hfs, hmin2⟩ := hmin
  obtain ⟨ha0, hb0, heq, hc0⟩ := hfs
  have hcop : IsCoprime a b := coprime_of_minimal ⟨⟨ha0, hb0, heq, hc0⟩, hmin2⟩
  have ha2 : (0 : ℤ) < a ^ 2 := pow_pos ha 2
  -- b² is coprime to c
  have hcop_b2_c : IsCoprime (b ^ 2) c := by
    have h2 : IsCoprime (b ^ 2) (a ^ 4) := hcop.symm.pow
    have h3 := h2.add_mul_left_right (-(b ^ 2))
    have he2 : a ^ 4 + b ^ 2 * -(b ^ 2) = c ^ 2 := by linear_combination heq
    rw [he2] at h3
    exact (IsCoprime.pow_right_iff (by norm_num)).mp h3
  rcases Int.emod_two_eq_zero_or_one b with hbev | hbodd
  · -- Case B: b even, c odd
    have hgcd : Int.gcd c (b ^ 2) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop_b2_c.symm
    have hco : c % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one c with h0 | h1
      · exfalso
        have hcd : (2 : ℤ) ∣ c := Int.dvd_of_emod_eq_zero h0
        have hbd : (2 : ℤ) ∣ b ^ 2 :=
          (Int.dvd_of_emod_eq_zero hbev).trans (dvd_pow_self b two_ne_zero)
        have hdvd : (2 : ℤ) ∣ (Int.gcd c (b ^ 2) : ℤ) := Int.dvd_coe_gcd hcd hbd
        rw [hgcd] at hdvd; norm_num at hdvd
      · exact h1
    have htri : PythagoreanTriple c (b ^ 2) (a ^ 2) := by
      delta PythagoreanTriple; linear_combination -heq
    obtain ⟨p, q, hp1, hp2, hp3, hp4, hp5, _hp6⟩ := htri.coprime_classification' hgcd hco ha2
    -- c = p²−q², b² = 2pq, a² = p²+q²
    have hpq0 : p ≠ 0 ∧ q ≠ 0 := by
      have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb0
      rw [hp2] at hb2
      constructor
      · intro h0; apply hb2; rw [h0]; ring
      · intro h0; apply hb2; rw [h0]; ring
    rcases hp5 with ⟨_, hqo⟩ | ⟨hpo, _⟩
    · -- p even, q odd : apply the tail with the pair swapped
      exact caseB_tail ha hb hmin2 (by linear_combination hp3) (by linear_combination hp2)
        (by rw [Int.gcd_comm]; exact hp4) hqo hpq0.2 hpq0.1
    · -- p odd, q even
      exact caseB_tail ha hb hmin2 hp3 hp2 hp4 hpo hpq0.1 hpq0.2
  · -- Case A: b odd, c even
    have hgcd : Int.gcd (b ^ 2) c = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop_b2_c
    have hpar : b ^ 2 % 2 = 1 := by rw [sq, Int.mul_emod, hbodd]; decide
    have htri : PythagoreanTriple (b ^ 2) c (a ^ 2) := by
      delta PythagoreanTriple; linear_combination -heq
    obtain ⟨m, n, hm1, hm2, hm3, _hm4, _hm5, _hm6⟩ := htri.coprime_classification' hgcd hpar ha2
    -- b² = m²−n², c = 2mn, a² = m²+n²
    have hmn0 : m ≠ 0 ∧ n ≠ 0 := by
      constructor
      · intro h0; apply hc0; rw [hm2, h0]; ring
      · intro h0; apply hc0; rw [hm2, h0]; ring
    have hnew : FS m n (a * b) := by
      refine ⟨hmn0.1, hmn0.2, ?_, mul_ne_zero ha0 hb0⟩
      have hval : (a * b) ^ 2 = m ^ 4 - n ^ 4 := by
        rw [show (a * b) ^ 2 = a ^ 2 * b ^ 2 by ring, hm3, hm1]; ring
      exact hval.symm
    have hlt : m.natAbs < a.natAbs := by
      apply Int.natAbs_lt_iff_sq_lt.mpr
      rw [hm3]; linarith [sq_pos_of_ne_zero hmn0.2]
    exact absurd (hmin2 m n (a * b) hnew) (not_le.mpr hlt)

private theorem not_FS (a b c : ℤ) : ¬ FS a b c := by
  intro h
  obtain ⟨a0, b0, c0, hfs0, hmin2⟩ := exists_minimal h
  have hmin_abs : Min |a0| |b0| |c0| :=
    ⟨FS_abs hfs0, fun a1 b1 c1 h1 => by rw [Int.natAbs_abs]; exact hmin2 a1 b1 c1 h1⟩
  exact descent (abs_pos.mpr hfs0.1) (abs_pos.mpr hfs0.2.1) (abs_pos.mpr hfs0.2.2.2) hmin_abs

/-- **Fermat's right-triangle theorem (quartic `−` form).** For nonzero integers `a, b`, the
equation `a⁴ − b⁴ = c²` has only the trivial solutions `c = 0` (equivalently `|a| = |b|`). -/
theorem fermat_sub_four (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (h : a ^ 4 - b ^ 4 = c ^ 2) :
    c = 0 := by
  by_contra hc
  exact not_FS a b c ⟨ha, hb, h, hc⟩

/-- Headline corollary: `a⁴ − b⁴ = c²` has no solution with all of `a, b, c` nonzero. -/
theorem no_nontrivial_fermat_sub_four :
    ¬ ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ^ 4 - b ^ 4 = c ^ 2 := by
  rintro ⟨a, b, c, ha, hb, hc, h⟩
  exact not_FS a b c ⟨ha, hb, h, hc⟩

end MathProof.Challenges.C0045FermatSubFour

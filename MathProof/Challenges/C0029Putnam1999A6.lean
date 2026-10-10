import MathProof.Basic

/-!
# Challenge C0029Putnam1999A6 — Putnam 1999 A6 (recurrence with division ⇒ n ∣ aₙ)

**Status:** ✅ SOLVED (Sonnet, single round — see `PROOF_PATTERNS.md` for the recipe).

**Source:** PutnamBench `putnam_1999_a6` (trishullab/PutnamBench, Apache-2.0). No Mathlib
`Archive` formalization exists. Statement reproduced **verbatim** from upstream (the
`proof-auditor` diffs against the cache; never weaken it).

Statement: the real sequence `a` with `a₁=1, a₂=2, a₃=24` and, for `n≥4`,
`aₙ = (6 aₙ₋₁² aₙ₋₃ − 8 aₙ₋₁ aₙ₋₂²) / (aₙ₋₂ aₙ₋₃)`, satisfies `n ∣ aₙ` for all `n ≥ 1`
(i.e. `aₙ` is an integer multiple of `n`).

**Why this is the escalation vehicle (no Mathlib spine):** the crux is the hidden reduction
`bₙ := aₙ/aₙ₋₁ = 2ⁿ⁻¹(2ⁿ⁻¹−1)` (from the linear recurrence `bₙ = 6bₙ₋₁ − 8bₙ₋₂`, roots 2 & 4),
giving the closed form `aₙ = 2^{n(n−1)/2} · ∏_{k=1}^{n−1}(2ᵏ−1)`; then `n ∣ aₙ` needs an
order-of-2 / prime-power number-theoretic argument. No single Mathlib lemma closes it.
-/

namespace MathProof.Challenges.C0029Putnam1999A6

/-! ## Closed form -/

/-- Closed form for `aₘ`: `A m = ∏_{k=1}^{m-1} 2^k (2^k - 1)`.  `A 1 = 1, A 2 = 2, A 3 = 24`. -/
def A (m : ℕ) : ℕ := ∏ k ∈ Finset.Icc 1 (m - 1), 2 ^ k * (2 ^ k - 1)

lemma A_one : A 1 = 1 := by decide

lemma A_two : A 2 = 2 := by decide

lemma A_three : A 3 = 24 := by decide

/-- Every factor `2^k (2^k - 1)` (for `k ≥ 1`) is positive, hence `A m > 0`. -/
lemma A_pos (m : ℕ) (_hm : 1 ≤ m) : 0 < A m := by
  apply Finset.prod_pos
  intro k hk
  simp only [Finset.mem_Icc] at hk
  have h2 : 2 ≤ 2 ^ k := by
    calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk.1
  have : 0 < 2 ^ k - 1 := by omega
  positivity

/-- The one-step recurrence for `A`, as natural numbers (no truncation issues since
`2^(m-1) ≥ 1`). -/
lemma A_succ (m : ℕ) (hm : 2 ≤ m) :
    A m = A (m - 1) * (2 ^ (m - 1) * (2 ^ (m - 1) - 1)) := by
  unfold A
  have e1 : (m - 1) - 1 = m - 2 := by omega
  rw [e1]
  have e2 : m - 1 = (m - 2) + 1 := by omega
  rw [e2]
  exact Finset.prod_Icc_succ_top (by omega) _

/-- The `A_succ` recurrence, cast to `ℤ` (needed because the crux identity below needs
integer subtraction). -/
lemma A_succ_cast (m : ℕ) (hm : 2 ≤ m) :
    (A m : ℤ) = (A (m - 1) : ℤ) * ((2:ℤ) ^ (m - 1) * ((2:ℤ) ^ (m - 1) - 1)) := by
  have h := A_succ m hm
  have hpow : (1:ℕ) ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
  zify [hpow] at h
  linarith [h]

/-- The hidden linear recurrence `bₙ = 6 bₙ₋₁ − 8 bₙ₋₂` for `bⱼ := 2^j(2^j−1)`, coming from
the characteristic roots `2, 4` of the original problem's division step. -/
lemma b_identity (m : ℕ) (hm : 3 ≤ m) :
    (2:ℤ) ^ (m - 1) * ((2:ℤ) ^ (m - 1) - 1) =
      6 * ((2:ℤ) ^ (m - 2) * ((2:ℤ) ^ (m - 2) - 1))
        - 8 * ((2:ℤ) ^ (m - 3) * ((2:ℤ) ^ (m - 3) - 1)) := by
  have e1 : m - 1 = (m - 3) + 2 := by omega
  have e2 : m - 2 = (m - 3) + 1 := by omega
  rw [e1, e2, pow_add, pow_add]
  ring

/-- The MECHANICAL plumbing identity: assembling `A_succ_cast` three times with `b_identity`
gives the integer identity that (after clearing denominators) is exactly the recurrence
`putnam_1999_a6.hange4` needs at the closed-form level. -/
lemma key_id (n : ℕ) (hn : 4 ≤ n) :
    (A n : ℤ) * A (n - 2) * A (n - 3) + 8 * A (n - 1) * (A (n - 2))^2
      = 6 * (A (n - 1))^2 * A (n - 3) := by
  have hAn : (A n : ℤ) = A (n - 1) * (2 ^ (n - 1) * (2 ^ (n - 1) - 1)) := A_succ_cast n (by omega)
  have hA1 : (A (n - 1) : ℤ) = A (n - 2) * (2 ^ (n - 2) * (2 ^ (n - 2) - 1)) := by
    have h := A_succ_cast (n - 1) (by omega)
    rwa [show (n - 1) - 1 = n - 2 from by omega] at h
  have hA2 : (A (n - 2) : ℤ) = A (n - 3) * (2 ^ (n - 3) * (2 ^ (n - 3) - 1)) := by
    have h := A_succ_cast (n - 2) (by omega)
    rwa [show (n - 2) - 1 = n - 3 from by omega] at h
  have hb := b_identity n (by omega)
  rw [hAn, hb, hA1, hA2]
  ring

/-! ## Crux: `m ∣ A m` -/

/-- For every prime `p`, `p ^ (m.factorization p) ∣ A m`.  Two cases: `p = 2` uses the top
factor `2^(m-1)` directly (its exponent bound comes from `Nat.factorization_lt`); `p` odd uses
Euler's theorem (`2^φ(p^e) ≡ 1 [MOD p^e]`) to locate a factor `2^φ(p^e)(2^φ(p^e)-1)` inside the
product, with `φ(p^e) ∈ [1, m-1]` since `φ(p^e) < p^e ≤ m`. -/
lemma prime_pow_dvd_A (m : ℕ) (hm : 1 ≤ m) (p : ℕ) (hp : p.Prime) :
    p ^ (m.factorization p) ∣ A m := by
  set e := m.factorization p with he_def
  by_cases he0 : e = 0
  · simp [he0]
  · have hm0 : m ≠ 0 := by omega
    have he1 : 1 ≤ e := by omega
    have hlt : e < m := by rw [he_def]; exact Nat.factorization_lt p hm0
    have hle : e ≤ m - 1 := by omega
    by_cases hp2 : p = 2
    · subst hp2
      have hmem : (m - 1) ∈ Finset.Icc 1 (m - 1) := by rw [Finset.mem_Icc]; omega
      have hfac : (2:ℕ) ^ (m - 1) ∣ A m :=
        (dvd_mul_right (2 ^ (m - 1)) (2 ^ (m - 1) - 1)).trans
          (Finset.dvd_prod_of_mem (fun k => 2 ^ k * (2 ^ k - 1)) hmem)
      exact (pow_dvd_pow 2 hle).trans hfac
    · have hcop2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
      have hcop : Nat.Coprime 2 (p ^ e) := hcop2p.pow_right e
      have heuler : (2:ℕ) ^ (Nat.totient (p ^ e)) ≡ 1 [MOD p ^ e] := Nat.ModEq.pow_totient hcop
      have hpe1 : 1 < p ^ e := by
        have h1 : p ^ 1 ≤ p ^ e := Nat.pow_le_pow_right hp.one_lt.le he1
        rw [pow_one] at h1
        exact hp.one_lt.trans_le h1
      have hpe_dvd_m : p ^ e ∣ m := by rw [he_def]; exact Nat.ordProj_dvd m p
      have hpe_le_m : p ^ e ≤ m := Nat.le_of_dvd (by omega) hpe_dvd_m
      have hphi_lt : Nat.totient (p ^ e) < p ^ e := Nat.totient_lt (p ^ e) hpe1
      have hphi_pos : 0 < Nat.totient (p ^ e) := Nat.totient_pos.mpr (by omega)
      have hmem : Nat.totient (p ^ e) ∈ Finset.Icc 1 (m - 1) := by
        rw [Finset.mem_Icc]; omega
      have hdvd1 : p ^ e ∣ 2 ^ (Nat.totient (p ^ e)) - 1 :=
        (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp heuler.symm
      exact (hdvd1.mul_left _).trans
        (Finset.dvd_prod_of_mem (fun k => 2 ^ k * (2 ^ k - 1)) hmem)

/-- Assembling `prime_pow_dvd_A` over all primes via `ordProj_dvd_ordProj_iff_dvd`. -/
lemma dvd_A (m : ℕ) (hm : 1 ≤ m) : m ∣ A m := by
  have hm0 : m ≠ 0 := by omega
  have hAm0 : A m ≠ 0 := (A_pos m hm).ne'
  rw [← Nat.ordProj_dvd_ordProj_iff_dvd hm0 hAm0]
  intro p
  by_cases hp : p.Prime
  · rw [Nat.pow_dvd_pow_iff_le_right hp.one_lt]
    exact (hp.pow_dvd_iff_le_factorization hAm0).mp (prime_pow_dvd_A m hm p hp)
  · simp [hp]

/-! ## Closed-form identification -/

/-- `a m` equals the closed form `A m`, for all `m ≥ 1`, by strong induction with a 3-step
lookback (base cases `m ≤ 3`, recursive step `m ≥ 4` via `hange4` + `key_id`). -/
lemma A_eq_a (a : ℤ → ℝ) (ha1 : a 1 = 1) (ha2 : a 2 = 2) (ha3 : a 3 = 24)
    (hange4 : ∀ n : ℕ, n ≥ 4 →
      a n = (6 * (a (n - 1))^2 * (a (n - 3)) - 8 * (a (n - 1)) * (a (n - 2))^2)
              / (a (n - 2) * a (n - 3))) :
    ∀ m : ℕ, 1 ≤ m → a (m : ℤ) = (A m : ℝ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm1
  by_cases hm3 : m ≤ 3
  · interval_cases m
    · simpa [A_one] using ha1
    · simpa [A_two] using ha2
    · simpa [A_three] using ha3
  · have hm4 : 4 ≤ m := by omega
    have ih1 : a ((m - 1 : ℕ) : ℤ) = (A (m - 1) : ℝ) := ih (m - 1) (by omega) (by omega)
    have ih2 : a ((m - 2 : ℕ) : ℤ) = (A (m - 2) : ℝ) := ih (m - 2) (by omega) (by omega)
    have ih3 : a ((m - 3 : ℕ) : ℤ) = (A (m - 3) : ℝ) := ih (m - 3) (by omega) (by omega)
    have hrec := hange4 m hm4
    have e1 : ((m:ℤ) - 1) = ((m - 1 : ℕ) : ℤ) := by omega
    have e2 : ((m:ℤ) - 2) = ((m - 2 : ℕ) : ℤ) := by omega
    have e3 : ((m:ℤ) - 3) = ((m - 3 : ℕ) : ℤ) := by omega
    rw [e1, e2, e3, ih1, ih2, ih3] at hrec
    rw [hrec]
    have hd2 : (A (m - 2) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (A_pos (m - 2) (by omega)).ne'
    have hd3 : (A (m - 3) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (A_pos (m - 3) (by omega)).ne'
    rw [div_eq_iff (mul_ne_zero hd2 hd3)]
    have hkey := key_id m hm4
    have hkeyR : (A m : ℝ) * (A (m - 2)) * (A (m - 3)) + 8 * (A (m - 1)) * (A (m - 2))^2
        = 6 * (A (m - 1))^2 * (A (m - 3)) := by exact_mod_cast hkey
    linear_combination -hkeyR

/-! ## Assembly -/

theorem putnam_1999_a6
(a : ℤ → ℝ)
(ha1 : a 1 = 1)
(ha2 : a 2 = 2)
(ha3 : a 3 = 24)
(hange4 : ∀ n : ℕ, n ≥ 4 → a n = (6 * (a (n - 1))^2 * (a (n - 3)) - 8 * (a (n - 1)) * (a (n - 2))^2)/(a (n - 2) * a (n - 3)))
: ∀ n, n ≥ 1 → (∃ k : ℤ, a n = k * n) := by
  intro n hn1
  lift n to ℕ using (by omega : (0:ℤ) ≤ n) with m
  have hm1 : 1 ≤ m := by exact_mod_cast hn1
  have heq : a (m : ℤ) = (A m : ℝ) := A_eq_a a ha1 ha2 ha3 hange4 m hm1
  have hdvd : m ∣ A m := dvd_A m hm1
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨(c:ℤ), ?_⟩
  rw [heq, hc]
  push_cast
  ring

end MathProof.Challenges.C0029Putnam1999A6

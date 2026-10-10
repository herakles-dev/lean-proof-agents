import MathProof.Basic

set_option autoImplicit false

/-! Assembled by scripts/bank.sh from swarm bank C0048Dvd210NPow13.
    Self-contained: bank cross-references were bare names in a shared namespace, so
    inlining them under one namespace preserves resolution. MUST pass check-proof.sh. -/

namespace MathProof.Challenges.C0048Dvd210NPow13

-- ── leaf: Dvd2 ──


theorem dvd2 (n : ℤ) : (2 : ℤ) ∣ n ^ 13 - n := by
  have key : ∀ x : ZMod 2, x ^ 13 = x := by decide
  have h2 : ((n ^ 13 - n : ℤ) : ZMod 2) = 0 := by
    push_cast
    rw [key]
    ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (n ^ 13 - n) 2).mp h2


-- ── leaf: Dvd3 ──


theorem dvd3 (n : ℤ) : (3 : ℤ) ∣ n ^ 13 - n := by
  have h : ((n ^ 13 - n : ℤ) : ZMod 3) = 0 := by
    push_cast
    generalize (n : ZMod 3) = x
    revert x
    decide
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (n ^ 13 - n) 3).mp h


-- ── leaf: Dvd5 ──


theorem dvd5 (n : ℤ) : (5 : ℤ) ∣ n ^ 13 - n := by
  have h : ((n ^ 13 - n : ℤ) : ZMod 5) = 0 := by
    push_cast
    have key : ∀ x : ZMod 5, x ^ 13 - x = 0 := by decide
    exact key (n : ZMod 5)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (n ^ 13 - n) 5).mp h


-- ── leaf: Dvd6 ──


theorem dvd6 (n : ℤ) : (6 : ℤ) ∣ n ^ 13 - n := by
  have hcop : IsCoprime (2 : ℤ) 3 := by
    refine ⟨-1, 1, ?_⟩
    ring
  have h6 : (2 : ℤ) * 3 ∣ n ^ 13 - n := hcop.mul_dvd (dvd2 n) (dvd3 n)
  norm_num at h6
  exact h6


-- ── leaf: Dvd7 ──


theorem dvd7 (n : ℤ) : (7 : ℤ) ∣ n ^ 13 - n := by
  have h : ((n ^ 13 - n : ℤ) : ZMod 7) = 0 := by
    push_cast
    have key : ∀ x : ZMod 7, x ^ 13 - x = 0 := by decide
    exact key (n : ZMod 7)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (n ^ 13 - n) 7).mp h


-- ── leaf: Dvd35 ──


theorem dvd35 (n : ℤ) : (35 : ℤ) ∣ n ^ 13 - n := by
  have h5 := dvd5 n
  have h7 := dvd7 n
  have hcop : IsCoprime (5 : ℤ) 7 := ⟨3, -2, by norm_num⟩
  have hmul := hcop.mul_dvd h5 h7
  norm_num at hmul
  exact hmul


-- ── leaf: Dvd210 ──


theorem dvd210 (n : ℤ) : (210 : ℤ) ∣ n ^ 13 - n := by
  have h6 := dvd6 n
  have h35 := dvd35 n
  have hcop : IsCoprime (6 : ℤ) 35 := ⟨6, -1, by norm_num⟩
  have hmul := hcop.mul_dvd h6 h35
  norm_num at hmul
  exact hmul


end MathProof.Challenges.C0048Dvd210NPow13

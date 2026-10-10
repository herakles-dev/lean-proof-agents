import MathProof.Basic

set_option autoImplicit false

/-! Assembled by scripts/bank.sh from swarm bank C0046Pow5Dvd30.
    Self-contained: bank cross-references were bare names in a shared namespace, so
    inlining them under one namespace preserves resolution. MUST pass check-proof.sh. -/

namespace MathProof.Challenges.C0046ThirtyDividesNPow5MinusN

-- ── leaf: DvdFive ──


/-- 5 divides n^5 - n (Fermat little, p=5). -/
theorem dvd_five (n : ℤ) : (5 : ℤ) ∣ n ^ 5 - n := by
  have hfun : ∀ m : ZMod 5, m ^ 5 - m = 0 := by decide
  have h : ((n ^ 5 - n : ℤ) : ZMod 5) = 0 := by
    push_cast
    simpa using hfun (n : ZMod 5)
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (n ^ 5 - n) 5).mp h


-- ── leaf: DvdThree ──


/-- 3 divides n^5 - n. -/
theorem dvd_three (n : ℤ) : (3 : ℤ) ∣ n ^ 5 - n := by
  have hfun : ∀ m : ZMod 3, m ^ 5 - m = 0 := by decide
  have h : ((n ^ 5 - n : ℤ) : ZMod 3) = 0 := by
    push_cast
    simpa using hfun (n : ZMod 3)
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (n ^ 5 - n) 3).mp h


-- ── leaf: DvdTwo ──


/-- 2 divides n^5 - n (Fermat little, p=2). -/
theorem dvd_two (n : ℤ) : (2 : ℤ) ∣ n ^ 5 - n := by
  have hfun : ∀ m : ZMod 2, m ^ 5 - m = 0 := by decide
  have h : ((n ^ 5 - n : ℤ) : ZMod 2) = 0 := by
    push_cast
    simpa using hfun (n : ZMod 2)
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (n ^ 5 - n) 2).mp h


-- ── leaf: Main ──


/-- 30 ∣ n^5 - n: combine 2∣, 3∣, 5∣ by pairwise coprimality (30 = 2·3·5). -/
theorem challenge_statement (n : ℤ) : (30 : ℤ) ∣ n ^ 5 - n := by
  have c1 : IsCoprime (2 : ℤ) 3 := by rw [Int.isCoprime_iff_gcd_eq_one]; decide
  have c2 : IsCoprime (2 * 3 : ℤ) 5 := by rw [Int.isCoprime_iff_gcd_eq_one]; decide
  have h6  : (2 * 3 : ℤ) ∣ n ^ 5 - n := c1.mul_dvd (dvd_two n) (dvd_three n)
  have h30 : (2 * 3 * 5 : ℤ) ∣ n ^ 5 - n := c2.mul_dvd h6 (dvd_five n)
  norm_num at h30
  exact h30


end MathProof.Challenges.C0046ThirtyDividesNPow5MinusN

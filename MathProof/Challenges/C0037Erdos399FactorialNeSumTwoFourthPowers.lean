import MathProof.Basic

/-!
# Challenge C0037Erdos399FactorialNeSumTwoFourthPowers — Erdős 399 (Cambie's coprime variant)

**Status:** ✅ SOLVED (axioms: propext, Classical.choice, Quot.sound).

**Source:** google-deepmind/formal-conjectures, `ErdosProblems/399.lean`, theorem
`erdos_399.variants.cambie`, tagged `@[category research solved, AMS 11]` with a `sorry` body
(a genuine formalization gap — a KNOWN-true Erdős result whose proof is not yet formalized).
Toolchain there is Lean v4.33.1 = ours. Statement reproduced **verbatim** (imports adapted to
`MathProof.Basic`); the goal is a machine-checked proof → an upstream PR recognition win.

**Statement.** For coprime `x, y` with `x·y > 1`, a factorial is never `x⁴ + y⁴`.
(Cambie's observation refines Erdős #399: the unrestricted problem — which also allows the form
`n! + yᵏ = xᵏ` — does have solutions, e.g. `10! + 36⁴ = 48⁴` (i.e. `10! = 48⁴ − 36⁴`, with
`gcd(48,36) = 12` non-coprime). The coprime **sum** form proved here is the impossible one.)

**Proof idea (elementary, mod 8).** `x⁴ mod 8 ∈ {0,1}` (0 if `x` even, 1 if `x` odd). Coprimality
forbids `x,y` both even, so `x⁴ + y⁴ mod 8 ∈ {1,2}` — never `0`. For `n ≥ 4`, `8 ∣ n!`
(`4! = 24` and `4! ∣ n!`), so `n!` and `x⁴+y⁴` differ mod 8. For `n ≤ 3`, `n! ≤ 6`, while
`x·y > 1` forces `max x y ≥ 2` so `x⁴ + y⁴ ≥ 16 > 6`.
-/

namespace MathProof.Challenges.C0037Erdos399FactorialNeSumTwoFourthPowers

open Nat

theorem erdos_399_cambie {n x y : ℕ} (hxy : x.Coprime y) (h1 : 1 < x * y) :
    n ! ≠ x ^ 4 + y ^ 4 := by
  intro heq
  rcases Nat.lt_or_ge n 4 with hn | hn
  · -- n < 4: n! ≤ 6, but x*y > 1 forces x^4 + y^4 ≥ 16.
    have hfact_le : n ! ≤ 6 := by
      interval_cases n <;> decide
    have hxy2 : 2 ≤ x ∨ 2 ≤ y := by
      by_contra hc
      push Not at hc
      obtain ⟨hx, hy⟩ := hc
      interval_cases x <;> interval_cases y <;> omega
    have hbig : 16 ≤ x ^ 4 + y ^ 4 := by
      rcases hxy2 with hx | hy
      · have h16 : (2 : ℕ) ^ 4 ≤ x ^ 4 := Nat.pow_le_pow_left hx 4
        omega
      · have h16 : (2 : ℕ) ^ 4 ≤ y ^ 4 := Nat.pow_le_pow_left hy 4
        omega
    omega
  · -- 4 ≤ n: 8 ∣ n !, but coprimality forbids x, y both even, so 8 ∤ x^4 + y^4.
    have h4le : (4 : ℕ) ! ∣ n ! := Nat.factorial_dvd_factorial hn
    have h8 : (8 : ℕ) ∣ n ! := dvd_trans (by decide) h4le
    have h8' : (8 : ℕ) ∣ (x ^ 4 + y ^ 4) := by rw [← heq]; exact h8
    have hnotboth2 : x % 2 = 1 ∨ y % 2 = 1 := by
      by_contra hc
      push Not at hc
      obtain ⟨hx0, hy0⟩ := hc
      have hx0' : x % 2 = 0 := by omega
      have hy0' : y % 2 = 0 := by omega
      have hx2 : (2 : ℕ) ∣ x := Nat.dvd_of_mod_eq_zero hx0'
      have hy2 : (2 : ℕ) ∣ y := Nat.dvd_of_mod_eq_zero hy0'
      have hg : (2 : ℕ) ∣ Nat.gcd x y := Nat.dvd_gcd hx2 hy2
      rw [(hxy : Nat.gcd x y = 1)] at hg
      norm_num at hg
    have parity4 : ∀ z : ℕ, z ^ 4 % 8 = z % 2 := by
      intro z
      rcases Nat.even_or_odd z with ⟨k, hk⟩ | ⟨k, hk⟩
      · subst hk
        have heqz : (k + k) ^ 4 = 8 * (2 * k ^ 4) := by ring
        rw [heqz]; omega
      · subst hk
        have heqz : (2 * k + 1) ^ 4 = 8 * (2 * k ^ 4 + 4 * k ^ 3 + 3 * k ^ 2 + k) + 1 := by ring
        rw [heqz]; omega
    have hx4 := parity4 x
    have hy4 := parity4 y
    omega

end MathProof.Challenges.C0037Erdos399FactorialNeSumTwoFourthPowers

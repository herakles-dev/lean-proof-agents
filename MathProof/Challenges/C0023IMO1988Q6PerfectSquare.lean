/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

The notice above is the one carried by Mathlib's `Archive/Imo/Imo1988Q6.lean`, which this file
is ported from. Changes made here: the imports, the namespace, this header, the docstring of
`imo1988_q6`, and the omission of the original's closing `example`. The two theorems and their
proofs are unchanged.
-/
import MathProof.Basic

/-!
# Challenge C0023IMO1988Q6PerfectSquare — IMO 1988 Q6 (Vieta jumping)

**Status:** ✅ SOLVED

If `a b : ℕ` and `a*b + 1 ∣ a² + b²`, then the quotient `(a² + b²)/(a*b + 1)` is a
perfect square. The famous IMO 1988 Q6; the standard proof is *constant-descent Vieta
jumping* (minimal counterexample + infinite descent).

**This module is a port, not original work.** The statement and both proofs are from Mathlib's
`Archive/Imo/Imo1988Q6.lean` by Johan Commelin (see the notice at the top of this file). The
Archive is a separate library target and cannot be imported, so the file was copied here and
used as a ceiling test for the trajectory DEPTH loop.

Build:  `lake build MathProof.Challenges.C0023IMO1988Q6PerfectSquare`
Verify: `scripts/check-proof.sh C0023IMO1988Q6PerfectSquare imo1988_q6`
-/

attribute [local simp] sq

namespace MathProof.Challenges.C0023IMO1988Q6PerfectSquare

/-- Constant descent Vieta jumping.

This proof technique allows one to prove an arbitrary proposition `claim`,
by running a descent argument on a hyperbola `H` in the first quadrant of the plane,
under the following conditions:

* `h₀`     : There exists an integral point `(x,y)` on the hyperbola `H`.
* `H_symm` : The hyperbola has a symmetry along the diagonal in the plane.
* `H_zero` : If an integral point `(x,0)` lies on the hyperbola `H`, then `claim` is true.
* `H_diag` : If an integral point `(x,x)` lies on the hyperbola `H`, then `claim` is true.
* `H_desc` : If `(x,y)` is an integral point on the hyperbola `H`,
  with `x < y` then there exists a “smaller” point on `H`: a point `(x',y')` with `x' < y' ≤ x`.

For reasons of usability, the hyperbola `H` is implemented as an arbitrary predicate.
(In question 6 of IMO1988, where this proof technique was first developed,
the predicate `claim` would be `∃ (d : ℕ), d ^ 2 = k` for some natural number `k`,
and the predicate `H` would be `fun a b ↦ a * a + b * b = (a * b + 1) * k`.)

To ensure that the predicate `H` actually describes a hyperbola,
the user must provide arguments `B` and `C` that are used as coefficients for a quadratic equation.
Finally, `H_quad` is the proof obligation that the quadratic equation
  `(y:ℤ) * y - B x * y + C x = 0`
describes the same hyperbola as the predicate `H`.

For extra flexibility, one must provide a predicate `base` on the integral points in the plane.
In the descent step `H_desc` this will give the user the additional assumption that
the point `(x,y)` does not lie in this base locus.
The user must provide a proof that the proposition `claim` is true
if there exists an integral point `(x,y)` on the hyperbola `H` that lies in the base locus.
If such a base locus is not necessary, once can simply let it be `fun x y ↦ False`.
-/
theorem constant_descent_vieta_jumping (x y : ℕ) {claim : Prop} {H : ℕ → ℕ → Prop} (h₀ : H x y)
    (B : ℕ → ℤ) (C : ℕ → ℤ) (base : ℕ → ℕ → Prop)
    (H_quad : ∀ {x y}, H x y ↔ (y : ℤ) * y - B x * y + C x = 0) (H_symm : ∀ {x y}, H x y ↔ H y x)
    (H_zero : ∀ {x}, H x 0 → claim) (H_diag : ∀ {x}, H x x → claim)
    (H_desc : ∀ {x y}, 0 < x → x < y → ¬base x y → H x y →
      ∀ y', y' * y' - B x * y' + C x = 0 → y' = B x - y → y' * y = C x → 0 ≤ y' ∧ y' ≤ x)
    (H_base : ∀ {x y}, H x y → base x y → claim) : claim := by
  -- First of all, we may assume that x ≤ y.
  -- We justify this using H_symm.
  wlog hxy : x ≤ y
  · rw [H_symm] at h₀; apply this y x h₀ B C base _ _ _ _ _ _ (le_of_not_ge hxy); assumption'
  -- In fact, we can easily deal with the case x = y.
  by_cases x_eq_y : x = y
  · subst x_eq_y; exact H_diag h₀
  -- Hence we may assume that x < y.
  replace hxy : x < y := lt_of_le_of_ne hxy x_eq_y
  clear x_eq_y
  -- Consider the upper branch of the hyperbola defined by H.
  let upper_branch : Set (ℕ × ℕ) := {p | H p.1 p.2 ∧ p.1 < p.2}
  -- Note that the point p = (x,y) lies on the upper branch.
  let p : ℕ × ℕ := ⟨x, y⟩
  have hp : p ∈ upper_branch := ⟨h₀, hxy⟩
  -- We also consider the exceptional set of solutions (a,b) that satisfy
  -- a = 0 or a = b or B a = b or B a = b + a or that lie in the base locus.
  let exceptional : Set (ℕ × ℕ) :=
    {p | H p.1 p.2 ∧ (base p.1 p.2 ∨ p.1 = 0 ∨ p.1 = p.2 ∨ B p.1 = p.2 ∨ B p.1 = p.2 + p.1)}
  -- Let S be the projection of the upper branch on to the y-axis
  -- after removing the exceptional locus.
  let S : Set ℕ := Prod.snd '' (upper_branch \ exceptional)
  -- The strategy is to show that the exceptional locus in nonempty
  -- by running a descent argument that starts with the given point p = (x,y).
  -- Our assumptions ensure that we can then prove the claim.
  suffices exc : exceptional.Nonempty by
    -- Suppose that there exists an element in the exceptional locus.
    simp only [Set.Nonempty, Prod.exists, Set.mem_ofPred_eq, exceptional] at exc
    -- Let (a,b) be such an element, and consider all the possible cases.
    rcases exc with ⟨a, b, hH, hb⟩
    rcases hb with (_ | rfl | rfl | hB | hB)
    -- The first three cases are rather easy to solve.
    · solve_by_elim
    · rw [H_symm] at hH; solve_by_elim
    · solve_by_elim
    -- The final two cases are very similar.
    all_goals
      -- Consider the quadratic equation that (a,b) satisfies.
      rw [H_quad] at hH
      -- We find the other root of the equation, and Vieta's formulas.
      rcases vieta_formula_quadratic hH with ⟨c, h_root, hV₁, hV₂⟩
      -- By substitutions we find that b = 0 or b = a.
      simp only [hB, add_eq_left, add_right_inj] at hV₁
      subst hV₁
      rw [← Int.ofNat_zero] at *
      rw [← H_quad] at h_root
      -- And hence we are done by H_zero and H_diag.
      solve_by_elim
  -- To finish the main proof, we need to show that the exceptional locus is nonempty.
  -- So we assume that the exceptional locus is empty, and work towards deriving a contradiction.
  rw [Set.nonempty_iff_ne_empty]
  intro exceptional_empty
  -- Observe that S is nonempty.
  have S_nonempty : S.Nonempty := by
    -- It contains the image of p.
    use p.2
    apply Set.mem_image_of_mem
    -- After all, we assumed that the exceptional locus is empty.
    rwa [exceptional_empty, Set.sdiff_empty]
  -- We are now set for an infinite descent argument.
  -- Let m be the smallest element of the nonempty set S.
  obtain ⟨m, m_mem, m_min⟩ := Nat.lt_wfRel.wf.has_min S S_nonempty
  -- It suffices to show that there is point (a,b) with b ∈ S and b < m.
  rsuffices ⟨p', p'_mem, p'_small⟩ : ∃ p' : ℕ × ℕ, p'.2 ∈ S ∧ p'.2 < m
  · solve_by_elim
  -- Let (m_x, m_y) be a point on the upper branch that projects to m ∈ S
  -- and that does not lie in the exceptional locus.
  rcases m_mem with ⟨⟨mx, my⟩, ⟨⟨hHm, mx_lt_my⟩, h_base⟩, m_eq⟩
  -- This means that m_y = m,
  -- and the conditions H(m_x, m_y) and m_x < m_y are satisfied.
  simp only at mx_lt_my hHm m_eq
  simp only [exceptional, hHm, Set.mem_ofPred_eq, true_and] at h_base
  push Not at h_base
  -- Finally, it also means that (m_x, m_y) does not lie in the base locus,
  -- that m_x ≠ 0, m_x ≠ m_y, B(m_x) ≠ m_y, and B(m_x) ≠ m_x + m_y.
  rcases h_base with ⟨h_base, hmx, hm_diag, hm_B₁, hm_B₂⟩
  replace hmx : 0 < mx := pos_iff_ne_zero.mpr hmx
  -- Consider the quadratic equation that (m_x, m_y) satisfies.
  have h_quad := hHm
  rw [H_quad] at h_quad
  -- We find the other root of the equation, and Vieta's formulas.
  rcases vieta_formula_quadratic h_quad with ⟨c, h_root, hV₁, hV₂⟩
  -- Now we rewrite Vieta's formulas a bit, and apply the descent step.
  replace hV₁ : c = B mx - my := eq_sub_of_add_eq' hV₁
  rw [mul_comm] at hV₂
  have Hc := H_desc hmx mx_lt_my h_base hHm c h_root hV₁ hV₂
  -- This means that we may assume that c ≥ 0 and c ≤ m_x.
  obtain ⟨c_nonneg, c_lt⟩ := Hc
  -- In other words, c is a natural number.
  lift c to ℕ using c_nonneg
  -- Recall that we are trying find a point (a,b) such that b ∈ S and b < m.
  -- We claim that p' = (c, m_x) does the job.
  let p' : ℕ × ℕ := ⟨c, mx⟩
  use p'
  -- The second condition is rather easy to check, so we do that first.
  constructor; swap
  · rwa [m_eq] at mx_lt_my
  -- Now we need to show that p' projects onto S. In other words, that c ∈ S.
  -- We do that, by showing that it lies in the upper branch
  -- (which is sufficient, because we assumed that the exceptional locus is empty).
  apply Set.mem_image_of_mem
  rw [exceptional_empty, Set.sdiff_empty]
  -- Now we are ready to prove that p' = (c, m_x) lies on the upper branch.
  -- We need to check two conditions: H(c, m_x) and c < m_x.
  constructor
  · -- The first condition is not so hard. After all, c is the other root of the quadratic equation.
    rw [H_symm, H_quad]
    simpa using h_root
  · -- For the second condition, we note that it suffices to check that c ≠ m_x.
    suffices hc : c ≠ mx from lt_of_le_of_ne (mod_cast c_lt) hc
    -- However, recall that B(m_x) ≠ m_x + m_y.
    -- If c = m_x, we can prove B(m_x) = m_x + m_y.
    contrapose hm_B₂
    subst c
    simp [hV₁]
    -- Hence p' = (c, m_x) lies on the upper branch, and we are done.

/-- **IMO 1988 Q6.** If `a b : ℕ` and `a*b + 1` divides `a² + b²`, then the quotient
`(a² + b²)/(a*b + 1)` is a perfect square. -/
theorem imo1988_q6 {a b : ℕ} (h : a * b + 1 ∣ a ^ 2 + b ^ 2) :
    ∃ d, d ^ 2 = (a ^ 2 + b ^ 2) / (a * b + 1) := by
  rcases h with ⟨k, hk⟩
  rw [hk, Nat.mul_div_cancel_left _ (Nat.succ_pos (a * b))]
  simp only [sq] at hk
  apply constant_descent_vieta_jumping a b (H := fun a b => a * a + b * b = (a * b + 1) * k)
      hk (fun x => k * x) (fun x => x * x - k) fun _ _ => False <;>
    clear hk a b
  · -- We will now show that the fibers of the solution set are described by a quadratic equation.
    intro x y
    rw [← Int.natCast_inj, ← sub_eq_zero]
    apply eq_iff_eq_cancel_right.2
    simp; ring
  · -- Show that the solution set is symmetric in a and b.
    intro x y
    simp [add_comm (x * x), mul_comm x]
  · -- Show that the claim is true if b = 0.
    suffices ∀ a, a * a = k → ∃ d, d * d = k by simpa
    rintro x rfl; use x
  · -- Show that the claim is true if a = b.
    intro x hx
    suffices k ≤ 1 by
      rw [Nat.le_add_one_iff, Nat.le_zero] at this
      rcases this with (rfl | rfl)
      · use 0; simp
      · use 1; simp
    contrapose! hx with k_lt_one
    apply ne_of_lt
    calc
      x * x + x * x = x * x * 2 := by rw [mul_two]
      _ ≤ x * x * k := Nat.mul_le_mul_left (x * x) k_lt_one
      _ < (x * x + 1) * k := by linarith
  · -- Show the descent step.
    intro x y hx x_lt_y _ _ z h_root _ hV₀
    constructor
    · have hpos : 0 < z * z + x * x := by
        apply add_pos_of_nonneg_of_pos
        · apply mul_self_nonneg
        · apply mul_pos <;> exact mod_cast hx
      have hzx : z * z + x * x = (z * x + 1) * k := by
        rw [← sub_eq_zero, ← h_root]
        ring
      rw [hzx] at hpos
      replace hpos : 0 < z * x + 1 := pos_of_mul_pos_left hpos (Int.natCast_nonneg k)
      replace hpos : 0 ≤ z * x := Int.le_of_lt_add_one hpos
      apply nonneg_of_mul_nonneg_left hpos (mod_cast hx)
    · contrapose! hV₀ with x_lt_z
      apply ne_of_gt
      calc
        z * y > x * x := by apply mul_lt_mul' <;> lia
        _ ≥ x * x - k := sub_le_self _ (Int.natCast_nonneg k)
  · -- There is no base case in this application of Vieta jumping.
    simp

end MathProof.Challenges.C0023IMO1988Q6PerfectSquare

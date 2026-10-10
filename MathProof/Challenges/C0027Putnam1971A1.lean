import MathProof.Basic

open Set

/-!
# Challenge C0027Putnam1971A1 — Putnam 1971 A1 (3-D lattice-point pigeonhole)

**Status:** ✅ SOLVED.

**Source:** PutnamBench `putnam_1971_a1` (trishullab/PutnamBench, Apache-2.0). No Mathlib
`Archive` formalization exists (verified) — a genuine *unaided* ceiling-test target.

Math (why it's true): the 9 points fall into the `2×2×2 = 8` parity classes of
`(ℤ/2)³`; by pigeonhole two distinct points `P ≠ Q` share a parity class, so their
midpoint has integer coordinates and (at `t = 1/2 ∈ Ioo 0 1`) lies in the interior of
segment `PQ`. Elementary, but the finite-pigeonhole-over-`Set.ncard` + real-coordinate
membership makes it a heavy formalization.
-/

namespace MathProof.Challenges.C0027Putnam1971A1

/-- Putnam 1971 A1. -/
theorem putnam_1971_a1
    (S : Set (ℤ × ℤ × ℤ)) (hS : S.ncard = 9)
    (L : (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) → Set (ℝ × ℝ × ℝ))
    (hL : L = fun ((a, b, c), (d, e, f)) =>
      {(t * a + (1 - t) * d, t * b + (1 - t) * e, t * c + (1 - t) * f) | t ∈ Ioo (0 : ℝ) 1}) :
    ∃ x y z : ℤ, ∃ P Q : ℤ × ℤ × ℤ, P ∈ S ∧ Q ∈ S ∧ P ≠ Q ∧
      ((x : ℝ), (y : ℝ), (z : ℝ)) ∈ L (P, Q) := by
  -- sg2: pigeonhole the 9 points into the 8 parity classes of (ZMod 2)³.
  obtain ⟨P, hP, Q, hQ, hPQ, hEq⟩ :
      ∃ P ∈ S, ∃ Q ∈ S, P ≠ Q ∧
        (fun p : ℤ × ℤ × ℤ => ((p.1 : ZMod 2), (p.2.1 : ZMod 2), (p.2.2 : ZMod 2))) P
        = (fun p : ℤ × ℤ × ℤ => ((p.1 : ZMod 2), (p.2.1 : ZMod 2), (p.2.2 : ZMod 2))) Q := by
    refine Set.exists_ne_map_eq_of_ncard_lt_of_maps_to (s := S) (t := Set.univ)
      ?_ (fun a _ => Set.mem_univ _)
    rw [Set.ncard_univ]; simp [hS]
  obtain ⟨a, b, c⟩ := P
  obtain ⟨d, e, f⟩ := Q
  simp only [Prod.mk.injEq] at hEq
  obtain ⟨h1, h2, h3⟩ := hEq
  -- sg3: same parity per coordinate ⇒ integer midpoint witness.
  have mid : ∀ u v : ℤ, (u : ZMod 2) = (v : ZMod 2) → ∃ k : ℤ, u + v = 2 * k := by
    intro u v h
    have hz : ((u - v : ℤ) : ZMod 2) = 0 := by push_cast; rw [h]; ring
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    obtain ⟨j, hj⟩ := hz
    exact ⟨j + v, by push_cast at hj ⊢; linarith⟩
  obtain ⟨x, hx⟩ := mid a d h1
  obtain ⟨y, hy⟩ := mid b e h2
  obtain ⟨z, hz⟩ := mid c f h3
  -- sg4: the integer midpoint lies in L(P, Q) at parameter t = 1/2.
  refine ⟨x, y, z, (a, b, c), (d, e, f), hP, hQ, hPQ, ?_⟩
  subst hL
  refine ⟨1 / 2, by constructor <;> norm_num, ?_⟩
  have hx' : (a : ℝ) + d = 2 * x := by exact_mod_cast hx
  have hy' : (b : ℝ) + e = 2 * y := by exact_mod_cast hy
  have hz' : (c : ℝ) + f = 2 * z := by exact_mod_cast hz
  ext <;> dsimp <;> linarith

end MathProof.Challenges.C0027Putnam1971A1

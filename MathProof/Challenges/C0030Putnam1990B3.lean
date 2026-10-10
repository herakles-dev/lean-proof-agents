import MathProof.Basic

/-!
# Challenge C0030Putnam1990B3 — Putnam 1990 B3 (commuting square-entry 2×2 matrices, pigeonhole)

**Status:** ✅ SOLVED.

**Source:** PutnamBench `putnam_1990_b3` (trishullab/PutnamBench, Apache-2.0). No Mathlib
`Archive` formalization exists. Statement reproduced **verbatim** from upstream (the
`proof-auditor` diffs against the cache; never weaken it).

Statement: let `S` be a set of `2×2` matrices over `ℕ` whose entries are all perfect squares
`≤ 200`. If `S.encard > 50387` (`= 15⁴ − 15² − 15 + 2`) then `S` contains two distinct
commuting elements.

## Proof idea

Colour each matrix `M` by a value in `Fin 15 × Fin 15 × Fin 15 × Fin 15` (the four
entry-square-indices `p,q,r,s = idx(M₀₀),idx(M₀₁),idx(M₁₀),idx(M₁₁)`, where `idx = Nat.sqrt`
capped at 14), with two "sink" colours for two always-commuting cliques so the palette drops
below `50388`:

* **diagonal** matrices (`q=0 ∧ r=0`, i.e. `M₀₁=M₁₀=0`) → sink `(0,0,0,0)` — pairwise commute;
* **pencil** matrices (`r=0 ∧ p=s`, i.e. `M₁₀=0 ∧ M₀₀=M₁₁`, `aI+bE₁₂`) → sink `(0,1,0,0)` —
  pairwise commute (`E₁₂²=0`);
* everything else → its own tuple `(p,q,r,s)`, landing in `{r≠0} ∪ {r=0 ∧ q≠0 ∧ p≠s}`.

The palette `tgt` has `≤ 15·15·14·15 + (15·15−15)·14 + 2 = 47250 + 2940 + 2 = 50192 ≤ 50387`
colours, so `Set.exists_ne_map_eq_of_encard_lt_of_maps_to` yields distinct `A ≠ B ∈ S` with the
same colour. Equal colour forces both diagonal or both pencil (else-colours are injective and the
two sinks are distinct), hence they commute.
-/

namespace MathProof.Challenges.C0030Putnam1990B3

open Matrix Finset

/-- Every entry allowed by `hS` is one of the 15 squares `0,1,4,…,196`. -/
private lemma entries_mem_sq (n : ℕ) (h1 : ∃ x : ℤ, (n : ℤ) = x ^ 2) (h2 : n ≤ 200) :
    ∃ k : ℕ, k < 15 ∧ n = k ^ 2 := by
  obtain ⟨x, hx⟩ := h1
  refine ⟨x.natAbs, ?_, ?_⟩
  · by_contra hk
    rw [not_lt] at hk
    have : (15 : ℕ) ^ 2 ≤ x.natAbs ^ 2 := Nat.pow_le_pow_left hk 2
    have hn : n = x.natAbs ^ 2 := by
      have := Int.natAbs_pow_two x
      exact_mod_cast hx.trans this.symm
    omega
  · have := Int.natAbs_pow_two x
    exact_mod_cast hx.trans this.symm

/-- Index of a natural number as one of the 15 square-roots `0..14` (`Nat.sqrt`, capped). -/
private def idx (n : ℕ) : Fin 15 := ⟨min (Nat.sqrt n) 14, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- On a valid entry, `idx` recovers the square-root: `(idx n)² = n`. -/
private lemma idx_val_sq {n : ℕ} (h1 : ∃ x : ℤ, (n : ℤ) = x ^ 2) (h2 : n ≤ 200) :
    ((idx n : Fin 15) : ℕ) ^ 2 = n := by
  obtain ⟨k, hk15, hkn⟩ := entries_mem_sq n h1 h2
  have hsqrt : Nat.sqrt n = k := by rw [hkn, Nat.sqrt_eq']
  have hval : ((idx n : Fin 15) : ℕ) = k := by
    simp only [idx]
    rw [hsqrt, Nat.min_eq_left (by omega : k ≤ 14)]
  rw [hval, ← hkn]

/-- The colouring function. -/
private def f (M : Matrix (Fin 2) (Fin 2) ℕ) : Fin 15 × Fin 15 × Fin 15 × Fin 15 :=
  if idx (M 0 1) = 0 ∧ idx (M 1 0) = 0 then (0, 0, 0, 0)
  else if idx (M 1 0) = 0 ∧ idx (M 0 0) = idx (M 1 1) then (0, 1, 0, 0)
  else (idx (M 0 0), idx (M 0 1), idx (M 1 0), idx (M 1 1))

/-- Palette piece: `r ≠ 0` tuples. -/
private def tA : Finset (Fin 15 × Fin 15 × Fin 15 × Fin 15) :=
  Finset.univ ×ˢ (Finset.univ ×ˢ ((Finset.univ.erase (0 : Fin 15)) ×ˢ Finset.univ))

/-- Palette piece: `r = 0`, `q ≠ 0`, `p ≠ s` tuples. -/
private def tB : Finset (Fin 15 × Fin 15 × Fin 15 × Fin 15) :=
  (Finset.univ.offDiag ×ˢ (Finset.univ.erase (0 : Fin 15))).image
    (fun x => (x.1.1, x.2, (0 : Fin 15), x.1.2))

/-- Palette piece: the two sink colours. -/
private def tC : Finset (Fin 15 × Fin 15 × Fin 15 × Fin 15) := {(0, 0, 0, 0), (0, 1, 0, 0)}

private def tgt : Finset (Fin 15 × Fin 15 × Fin 15 × Fin 15) := tA ∪ tB ∪ tC

private lemma tA_card : tA.card = 47250 := by
  rw [tA, Finset.card_product, Finset.card_product, Finset.card_product,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin 15))]
  simp only [Finset.card_univ, Fintype.card_fin]

private lemma tB_card_le : tB.card ≤ 2940 := by
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, Finset.offDiag_card,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin 15))]
  simp only [Finset.card_univ, Fintype.card_fin]
  norm_num

private lemma tC_card_le : tC.card ≤ 2 :=
  (Finset.card_insert_le _ _).trans (by rw [Finset.card_singleton])

private lemma tgt_card_le : tgt.card ≤ 50387 := by
  unfold tgt
  refine (Finset.card_union_le _ _).trans ?_
  refine (add_le_add (Finset.card_union_le _ _) (le_refl tC.card)).trans ?_
  have h1 := tA_card
  have h2 := tB_card_le
  have h3 := tC_card_le
  omega

set_option maxRecDepth 4000 in
/-- `f` maps every matrix into the target palette (by construction, no validity needed). -/
private lemma f_mapsTo (M : Matrix (Fin 2) (Fin 2) ℕ) : f M ∈ tgt := by
  have hmem : f M ∈ tA ∨ f M ∈ tB ∨ f M ∈ tC := by
    unfold f
    split_ifs with hd hp
    · exact Or.inr (Or.inr (by simp [tC]))
    · exact Or.inr (Or.inr (by simp [tC]))
    · by_cases hr : idx (M 1 0) = 0
      · -- r = 0 ⇒ q ≠ 0 and p ≠ s
        refine Or.inr (Or.inl ?_)
        have hq : idx (M 0 1) ≠ 0 := fun h => hd ⟨h, hr⟩
        have hps : idx (M 0 0) ≠ idx (M 1 1) := fun h => hp ⟨hr, h⟩
        rw [tB, Finset.mem_image]
        refine ⟨((idx (M 0 0), idx (M 1 1)), idx (M 0 1)), ?_, ?_⟩
        · rw [Finset.mem_product, Finset.mem_offDiag]
          exact ⟨⟨Finset.mem_univ _, Finset.mem_univ _, hps⟩,
            Finset.mem_erase.mpr ⟨hq, Finset.mem_univ _⟩⟩
        · simp [hr]
      · -- r ≠ 0
        refine Or.inl ?_
        rw [tA, Finset.mem_product, Finset.mem_product, Finset.mem_product]
        exact ⟨Finset.mem_univ _, Finset.mem_univ _,
          Finset.mem_erase.mpr ⟨hr, Finset.mem_univ _⟩, Finset.mem_univ _⟩
  rcases hmem with h | h | h
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
  · exact Finset.mem_union_right _ h

set_option linter.unusedSimpArgs false in
/-- Diagonal matrices commute. -/
private lemma commute_of_diag {A B : Matrix (Fin 2) (Fin 2) ℕ}
    (hA01 : A 0 1 = 0) (hA10 : A 1 0 = 0) (hB01 : B 0 1 = 0) (hB10 : B 1 0 = 0) :
    A * B = B * A := by
  have e00 : (A * B) 0 0 = (B * A) 0 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hA01, hA10, hB01, hB10]; ring
  have e01 : (A * B) 0 1 = (B * A) 0 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hA01, hA10, hB01, hB10]; ring
  have e10 : (A * B) 1 0 = (B * A) 1 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hA01, hA10, hB01, hB10]; ring
  have e11 : (A * B) 1 1 = (B * A) 1 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hA01, hA10, hB01, hB10]; ring
  refine Matrix.ext (fun i j => ?_)
  fin_cases i <;> fin_cases j
  · exact e00
  · exact e01
  · exact e10
  · exact e11

set_option linter.unusedSimpArgs false in
/-- Pencil matrices (`aI + bE₁₂`) commute. -/
private lemma commute_of_pencil {A B : Matrix (Fin 2) (Fin 2) ℕ}
    (hA10 : A 1 0 = 0) (hA : A 0 0 = A 1 1) (hB10 : B 1 0 = 0) (hB : B 0 0 = B 1 1) :
    A * B = B * A := by
  have e00 : (A * B) 0 0 = (B * A) 0 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hA10, hB10, hA, hB]; ring
  have e01 : (A * B) 0 1 = (B * A) 0 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hA10, hB10, hA, hB]; ring
  have e10 : (A * B) 1 0 = (B * A) 1 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hA10, hB10, hA, hB]; ring
  have e11 : (A * B) 1 1 = (B * A) 1 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hA10, hB10, hA, hB]; ring
  refine Matrix.ext (fun i j => ?_)
  fin_cases i <;> fin_cases j
  · exact e00
  · exact e01
  · exact e10
  · exact e11

set_option maxRecDepth 4000 in
theorem putnam_1990_b3
(S : Set (Matrix (Fin 2) (Fin 2) ℕ))
(hS : ∀ A ∈ S, ∀ i j : Fin 2, (∃ x : ℤ, A i j = x ^ 2) ∧ A i j ≤ 200)
: (S.encard > 50387) → (∃ A ∈ S, ∃ B ∈ S, A ≠ B ∧ A * B = B * A) := by
  intro hcard
  have hlt : (↑tgt : Set (Fin 15 × Fin 15 × Fin 15 × Fin 15)).encard < S.encard := by
    rw [Set.encard_coe_eq_coe_finsetCard]
    calc (tgt.card : ℕ∞) ≤ (50387 : ℕ∞) := by exact_mod_cast tgt_card_le
      _ < S.encard := hcard
  have hmaps : Set.MapsTo f S ↑tgt := fun M _ => f_mapsTo M
  obtain ⟨A, hA, B, hB, hne, hfab⟩ :=
    Set.exists_ne_map_eq_of_encard_lt_of_maps_to hlt hmaps
  refine ⟨A, hA, B, hB, hne, ?_⟩
  -- Recover entries from indices for both A and B.
  have hAsq : ∀ i j, ((idx (A i j) : Fin 15) : ℕ) ^ 2 = A i j :=
    fun i j => idx_val_sq (hS A hA i j).1 (hS A hA i j).2
  have hBsq : ∀ i j, ((idx (B i j) : Fin 15) : ℕ) ^ 2 = B i j :=
    fun i j => idx_val_sq (hS B hB i j).1 (hS B hB i j).2
  -- Classify A, then B; only diag/diag and pencil/pencil survive.
  by_cases hdA : idx (A 0 1) = 0 ∧ idx (A 1 0) = 0
  · -- A diagonal
    have hfA : f A = ((0 : Fin 15), (0 : Fin 15), (0 : Fin 15), (0 : Fin 15)) := by
      unfold f; rw [if_pos hdA]
    by_cases hdB : idx (B 0 1) = 0 ∧ idx (B 1 0) = 0
    · -- both diagonal
      apply commute_of_diag
      · have h := hAsq 0 1; rw [hdA.1] at h; simpa using h.symm
      · have h := hAsq 1 0; rw [hdA.2] at h; simpa using h.symm
      · have h := hBsq 0 1; rw [hdB.1] at h; simpa using h.symm
      · have h := hBsq 1 0; rw [hdB.2] at h; simpa using h.symm
    · by_cases hpB : idx (B 1 0) = 0 ∧ idx (B 0 0) = idx (B 1 1)
      · -- B pencil: colours (0,0,0,0) ≠ (0,1,0,0)
        exfalso
        have hfB : f B = ((0 : Fin 15), (1 : Fin 15), (0 : Fin 15), (0 : Fin 15)) := by
          unfold f; rw [if_neg hdB, if_pos hpB]
        rw [hfA, hfB] at hfab; exact absurd hfab (by decide)
      · -- B else: (0,0,0,0) = tuple ⇒ B diagonal, contra hdB
        exfalso
        have hfB : f B = (idx (B 0 0), idx (B 0 1), idx (B 1 0), idx (B 1 1)) := by
          unfold f; rw [if_neg hdB, if_neg hpB]
        rw [hfA, hfB] at hfab
        simp only [Prod.mk.injEq] at hfab
        exact hdB ⟨hfab.2.1.symm, hfab.2.2.1.symm⟩
  · by_cases hpA : idx (A 1 0) = 0 ∧ idx (A 0 0) = idx (A 1 1)
    · -- A pencil
      have hfA : f A = ((0 : Fin 15), (1 : Fin 15), (0 : Fin 15), (0 : Fin 15)) := by
        unfold f; rw [if_neg hdA, if_pos hpA]
      by_cases hdB : idx (B 0 1) = 0 ∧ idx (B 1 0) = 0
      · -- B diagonal: (0,1,0,0) ≠ (0,0,0,0)
        exfalso
        have hfB : f B = ((0 : Fin 15), (0 : Fin 15), (0 : Fin 15), (0 : Fin 15)) := by
          unfold f; rw [if_pos hdB]
        rw [hfA, hfB] at hfab; exact absurd hfab (by decide)
      · by_cases hpB : idx (B 1 0) = 0 ∧ idx (B 0 0) = idx (B 1 1)
        · -- both pencil
          apply commute_of_pencil
          · have h := hAsq 1 0; rw [hpA.1] at h; simpa using h.symm
          · have h00 := hAsq 0 0; have h11 := hAsq 1 1; rw [← h00, ← h11, hpA.2]
          · have h := hBsq 1 0; rw [hpB.1] at h; simpa using h.symm
          · have h00 := hBsq 0 0; have h11 := hBsq 1 1; rw [← h00, ← h11, hpB.2]
        · -- B else: (0,1,0,0) = tuple ⇒ B pencil, contra hpB
          exfalso
          have hfB : f B = (idx (B 0 0), idx (B 0 1), idx (B 1 0), idx (B 1 1)) := by
            unfold f; rw [if_neg hdB, if_neg hpB]
          rw [hfA, hfB] at hfab
          simp only [Prod.mk.injEq] at hfab
          exact hpB ⟨hfab.2.2.1.symm, by rw [hfab.1.symm, hfab.2.2.2.symm]⟩
    · -- A else
      have hfA : f A = (idx (A 0 0), idx (A 0 1), idx (A 1 0), idx (A 1 1)) := by
        unfold f; rw [if_neg hdA, if_neg hpA]
      by_cases hdB : idx (B 0 1) = 0 ∧ idx (B 1 0) = 0
      · -- B diagonal: tuple = (0,0,0,0) ⇒ A diagonal, contra hdA
        exfalso
        have hfB : f B = ((0 : Fin 15), (0 : Fin 15), (0 : Fin 15), (0 : Fin 15)) := by
          unfold f; rw [if_pos hdB]
        rw [hfA, hfB] at hfab
        simp only [Prod.mk.injEq] at hfab
        exact hdA ⟨hfab.2.1, hfab.2.2.1⟩
      · by_cases hpB : idx (B 1 0) = 0 ∧ idx (B 0 0) = idx (B 1 1)
        · -- B pencil: tuple = (0,1,0,0) ⇒ A pencil, contra hpA
          exfalso
          have hfB : f B = ((0 : Fin 15), (1 : Fin 15), (0 : Fin 15), (0 : Fin 15)) := by
            unfold f; rw [if_neg hdB, if_pos hpB]
          rw [hfA, hfB] at hfab
          simp only [Prod.mk.injEq] at hfab
          exact hpA ⟨hfab.2.2.1, by rw [hfab.1, hfab.2.2.2]⟩
        · -- both else: equal tuples ⇒ A = B, contra hne
          exfalso; apply hne
          have hfB : f B = (idx (B 0 0), idx (B 0 1), idx (B 1 0), idx (B 1 1)) := by
            unfold f; rw [if_neg hdB, if_neg hpB]
          rw [hfA, hfB] at hfab
          simp only [Prod.mk.injEq] at hfab
          obtain ⟨e0, e1, e2, e3⟩ := hfab
          ext i j
          fin_cases i <;> fin_cases j
          · exact (by rw [← hAsq 0 0, ← hBsq 0 0, e0] : A 0 0 = B 0 0)
          · exact (by rw [← hAsq 0 1, ← hBsq 0 1, e1] : A 0 1 = B 0 1)
          · exact (by rw [← hAsq 1 0, ← hBsq 1 0, e2] : A 1 0 = B 1 0)
          · exact (by rw [← hAsq 1 1, ← hBsq 1 1, e3] : A 1 1 = B 1 1)

end MathProof.Challenges.C0030Putnam1990B3

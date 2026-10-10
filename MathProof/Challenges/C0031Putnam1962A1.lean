import MathProof.Basic

/-!
# Challenge C0031Putnam1962A1 — Putnam 1962 A1 (five points ⇒ a convex quadrilateral)

**Status:** ✅ SOLVED.

**Source:** PutnamBench `putnam_1962_a1` (trishullab/PutnamBench, Apache-2.0). No Mathlib
`Archive` formalization exists. Statement reproduced **verbatim** from upstream (the
`proof-auditor` diffs against the cache; never weaken it).

Statement: given five points in a plane, no three of which lie on a straight line, some four
of these points form the vertices of a convex quadrilateral (the "Happy Ending" problem, n=5).
-/

namespace MathProof.Challenges.C0031Putnam1962A1

open Set

/-- If `t` is an extreme point of `S'` (not in the hull of the rest of `S'`), and `T ⊆ S'`
contains `t`, then `t` is also an extreme point of `T`. Subset monotonicity of `convexHull`. -/
private lemma extreme_mono {S' T : Set (ℝ × ℝ)} {t : ℝ × ℝ} (hsub : T ⊆ S')
    (ht : t ∉ convexHull ℝ (S' \ {t})) : t ∉ convexHull ℝ (T \ {t}) := fun hmem =>
  ht (convexHull_mono (Set.sdiff_subset_sdiff_left hsub) hmem)

/-- Finite Krein–Milman: for a finite point set, its convex hull equals the convex hull of the
extreme points of that hull (the closure in the general theorem is removable since the extreme
points are finite, so their hull is already closed). Copied from sibling challenge C0036. -/
private lemma finite_convexHull_eq_convexHull_extremePoints
    (S : Set (ℝ × ℝ)) (hS : S.Finite) :
    convexHull ℝ S = convexHull ℝ ((convexHull ℝ S).extremePoints ℝ) := by
  have hE'fin : ((convexHull ℝ S).extremePoints ℝ).Finite :=
    hS.subset extremePoints_convexHull_subset
  have hkm : closure (convexHull ℝ ((convexHull ℝ S).extremePoints ℝ)) = convexHull ℝ S :=
    closure_convexHull_extremePoints (hS.isCompact_convexHull ℝ) (convex_convexHull ℝ S)
  rw [(hE'fin.isClosed_convexHull ℝ).closure_eq] at hkm
  exact hkm.symm

/-- If the 2×2 "cross product" of `Q - P` and `X - P` vanishes, the three points are collinear. -/
private lemma collinear_of_cross_zero {P X Q : ℝ × ℝ} (hPQ : P ≠ Q)
    (hcross : (Q.1 - P.1) * (X.2 - P.2) - (Q.2 - P.2) * (X.1 - P.1) = 0) :
    Collinear ℝ ({X, P, Q} : Set (ℝ × ℝ)) := by
  rw [collinear_iff_of_mem (show P ∈ ({X, P, Q} : Set (ℝ × ℝ)) by simp)]
  refine ⟨Q - P, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · by_cases h1 : Q.1 - P.1 = 0
    · have h2 : Q.2 - P.2 ≠ 0 := fun h2 => hPQ (Prod.ext (by linarith) (by linarith))
      have hX1 : p.1 - P.1 = 0 := by
        have : (Q.2 - P.2) * (p.1 - P.1) = 0 := by rw [h1] at hcross; linarith
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h h2
        · exact h
      refine ⟨(p.2 - P.2) / (Q.2 - P.2), ?_⟩
      apply Prod.ext
      · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_sub]
        rw [h1]; linarith [hX1]
      · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_sub]
        field_simp; ring
    · refine ⟨(p.1 - P.1) / (Q.1 - P.1), ?_⟩
      apply Prod.ext
      · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_sub]
        field_simp; ring
      · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_sub]
        field_simp; linear_combination hcross
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

/-- Convex-position engine. Given two extreme points `A, B` of `S`, two further points `P, Q ∈ S`,
all four distinct, with `A` and `B` **strictly on the same side** of the line `PQ` (encoded by the
signed area / cross product being positive), the four points `{A, B, P, Q}` are the vertices of a
convex quadrilateral. `A, B` are handled by extremality (they cannot lie in the hull of the other
three); `P, Q` by the linear functional `L x := (Q.1-P.1)*x.2 - (Q.2-P.2)*x.1`, constant on line
`PQ` and strictly larger at `A, B`. -/
private lemma quad_from_pair (S : Set (ℝ × ℝ)) (A B P Q : ℝ × ℝ)
    (hAS : A ∈ S) (hBS : B ∈ S) (hPS : P ∈ S) (hQS : Q ∈ S)
    (hAex : A ∉ convexHull ℝ (S \ {A})) (hBex : B ∉ convexHull ℝ (S \ {B}))
    (hAB : A ≠ B) (hAP : A ≠ P) (hAQ : A ≠ Q) (hBP : B ≠ P) (hBQ : B ≠ Q) (hPQ : P ≠ Q)
    (hdA : 0 < (Q.1 - P.1) * (A.2 - P.2) - (Q.2 - P.2) * (A.1 - P.1))
    (hdB : 0 < (Q.1 - P.1) * (B.2 - P.2) - (Q.2 - P.2) * (B.1 - P.1)) :
    ∃ T ⊆ S, T.ncard = 4 ∧ ¬∃ t ∈ T, t ∈ convexHull ℝ (T \ {t}) := by
  have hTsub : ({A, B, P, Q} : Set (ℝ × ℝ)) ⊆ S := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  refine ⟨{A, B, P, Q}, hTsub, ?_, ?_⟩
  · rw [Set.ncard_insert_of_notMem (by simp [hAB, hAP, hAQ]),
        Set.ncard_insert_of_notMem (by simp [hBP, hBQ]),
        Set.ncard_insert_of_notMem (by simp [hPQ]),
        Set.ncard_singleton]
  · have hnA : A ∉ convexHull ℝ (({A, B, P, Q} : Set (ℝ × ℝ)) \ {A}) := extreme_mono hTsub hAex
    have hnB : B ∉ convexHull ℝ (({A, B, P, Q} : Set (ℝ × ℝ)) \ {B}) := extreme_mono hTsub hBex
    have hnP : P ∉ convexHull ℝ (({A, B, P, Q} : Set (ℝ × ℝ)) \ {P}) := by
      have hset : ({A, B, P, Q} : Set (ℝ × ℝ)) \ {P} = ({A, B, Q} : Set (ℝ × ℝ)) := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h, hne⟩; tauto
        · rintro (rfl | rfl | rfl)
          · exact ⟨Or.inl rfl, hAP⟩
          · exact ⟨Or.inr (Or.inl rfl), hBP⟩
          · exact ⟨Or.inr (Or.inr (Or.inr rfl)), fun h => hPQ h.symm⟩
      rw [hset,
          show ({A, B, Q} : Set (ℝ × ℝ)) = (({A, B, Q} : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) by simp,
          Finset.mem_convexHull']
      rintro ⟨w, hw0, hw1, hcomb⟩
      rw [Finset.sum_insert (by simp [hAB, hAQ]), Finset.sum_insert (by simp [hBQ]),
          Finset.sum_singleton] at hw1 hcomb
      have hwA : 0 ≤ w A := hw0 A (by simp)
      have hwB : 0 ≤ w B := hw0 B (by simp)
      rw [Prod.ext_iff] at hcomb
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hcomb
      obtain ⟨hx, hy⟩ := hcomb
      have hkey : w A * ((Q.1 - P.1) * (A.2 - P.2) - (Q.2 - P.2) * (A.1 - P.1))
          + w B * ((Q.1 - P.1) * (B.2 - P.2) - (Q.2 - P.2) * (B.1 - P.1)) = 0 := by
        linear_combination (Q.1 - P.1) * hy - (Q.2 - P.2) * hx
          - ((Q.1 - P.1) * P.2 - (Q.2 - P.2) * P.1) * hw1
      have hwA0 : w A = 0 :=
        le_antisymm (by nlinarith [hkey, mul_nonneg hwB hdB.le, hdA]) hwA
      have hwB0 : w B = 0 :=
        le_antisymm (by nlinarith [hkey, mul_nonneg hwA hdA.le, hdB]) hwB
      have hwQ1 : w Q = 1 := by linarith [hw1]
      apply hPQ
      rw [hwA0, hwB0, hwQ1] at hx hy
      simp only [zero_mul, one_mul, zero_add] at hx hy
      exact Prod.ext hx.symm hy.symm
    have hnQ : Q ∉ convexHull ℝ (({A, B, P, Q} : Set (ℝ × ℝ)) \ {Q}) := by
      have hset : ({A, B, P, Q} : Set (ℝ × ℝ)) \ {Q} = ({A, B, P} : Set (ℝ × ℝ)) := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h, hne⟩; tauto
        · rintro (rfl | rfl | rfl)
          · exact ⟨Or.inl rfl, hAQ⟩
          · exact ⟨Or.inr (Or.inl rfl), hBQ⟩
          · exact ⟨Or.inr (Or.inr (Or.inl rfl)), hPQ⟩
      rw [hset,
          show ({A, B, P} : Set (ℝ × ℝ)) = (({A, B, P} : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) by simp,
          Finset.mem_convexHull']
      rintro ⟨w, hw0, hw1, hcomb⟩
      rw [Finset.sum_insert (by simp [hAB, hAP]), Finset.sum_insert (by simp [hBP]),
          Finset.sum_singleton] at hw1 hcomb
      have hwA : 0 ≤ w A := hw0 A (by simp)
      have hwB : 0 ≤ w B := hw0 B (by simp)
      rw [Prod.ext_iff] at hcomb
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hcomb
      obtain ⟨hx, hy⟩ := hcomb
      have hkey : w A * ((Q.1 - P.1) * (A.2 - P.2) - (Q.2 - P.2) * (A.1 - P.1))
          + w B * ((Q.1 - P.1) * (B.2 - P.2) - (Q.2 - P.2) * (B.1 - P.1)) = 0 := by
        linear_combination (Q.1 - P.1) * hy - (Q.2 - P.2) * hx
          - ((Q.1 - P.1) * P.2 - (Q.2 - P.2) * P.1) * hw1
      have hwA0 : w A = 0 :=
        le_antisymm (by nlinarith [hkey, mul_nonneg hwB hdB.le, hdA]) hwA
      have hwB0 : w B = 0 :=
        le_antisymm (by nlinarith [hkey, mul_nonneg hwA hdA.le, hdB]) hwB
      have hwP1 : w P = 1 := by linarith [hw1]
      apply hPQ.symm
      rw [hwA0, hwB0, hwP1] at hx hy
      simp only [zero_mul, one_mul, zero_add] at hx hy
      exact Prod.ext hx.symm hy.symm
    rintro ⟨t, htT, htconv⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at htT
    rcases htT with rfl | rfl | rfl | rfl
    · exact hnA htconv
    · exact hnB htconv
    · exact hnP htconv
    · exact hnQ htconv

theorem putnam_1962_a1
(S : Set (ℝ × ℝ))
(hS : S.ncard = 5)
(hnoncol : ∀ s ⊆ S, s.ncard = 3 → ¬Collinear ℝ s)
: ∃ T ⊆ S, T.ncard = 4 ∧ ¬∃ t ∈ T, t ∈ convexHull ℝ (T \ {t}) := by
  have hSfin : S.Finite := by
    rcases S.finite_or_infinite with hfin | hinf
    · exact hfin
    · simp [hinf.ncard] at hS
  -- The extreme points of `S`: points not in the convex hull of the rest.
  set E : Set (ℝ × ℝ) := {x ∈ S | x ∉ convexHull ℝ (S \ {x})} with hE_def
  have hEsub : E ⊆ S := fun x hx => hx.1
  have hEfin : E.Finite := hSfin.subset hEsub
  by_cases h4 : 4 ≤ E.ncard
  · -- Hull has ≥ 4 vertices: any 4 extreme points of `S` are extreme points of themselves
    -- (subset-monotonicity of `convexHull`), i.e. already a convex quadrilateral.
    obtain ⟨T, hTE, hT4⟩ := Set.exists_subset_card_eq h4
    have hTS : T ⊆ S := hTE.trans hEsub
    refine ⟨T, hTS, hT4, ?_⟩
    rintro ⟨t, htT, htconv⟩
    have htE := hTE htT
    exact extreme_mono hTS htE.2 htconv
  · -- Hull triangle case: the hull's extreme points `E'` number exactly 3 (≤ 3 since `E' ⊆ E`;
    -- ≥ 3 since otherwise `S ⊆ convexHull E'` would be collinear, contradicting `hnoncol`).
    -- The other two points `P, Q` sit off the triangle; the line `PQ` has two of the three
    -- vertices strictly on one side, and those two together with `P, Q` bound a convex quad.
    rw [not_le] at h4
    set E' : Set (ℝ × ℝ) := (convexHull ℝ S).extremePoints ℝ with hE'def
    have hE'S : E' ⊆ S := extremePoints_convexHull_subset
    have hE'fin : E'.Finite := hSfin.subset hE'S
    have hE'E : E' ⊆ E := by
      intro x hx
      have hmem := ((convex_convexHull ℝ S).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff).1 hx
      exact ⟨hE'S hx, extreme_mono (subset_convexHull ℝ S) hmem.2⟩
    have hle3 : E'.ncard ≤ 3 := by
      have h := Set.ncard_le_ncard hE'E hEfin
      omega
    have hge3 : 3 ≤ E'.ncard := by
      by_contra hlt
      rw [not_le] at hlt
      have hcolE' : Collinear ℝ E' := by
        have hcases : E'.ncard = 0 ∨ E'.ncard = 1 ∨ E'.ncard = 2 := by omega
        rcases hcases with h | h | h
        · rw [Set.ncard_eq_zero hE'fin] at h; rw [h]; exact collinear_empty ℝ (ℝ × ℝ)
        · obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h; rw [ha]; exact collinear_singleton ℝ a
        · obtain ⟨a, b, _, hab⟩ := Set.ncard_eq_two.1 h; rw [hab]; exact collinear_pair ℝ a b
      have hcolCH : Collinear ℝ (convexHull ℝ E') := by
        have hvs : vectorSpan ℝ (convexHull ℝ E') = vectorSpan ℝ E' := by
          rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
        rw [collinear_iff_rank_le_one, hvs, ← collinear_iff_rank_le_one]
        exact hcolE'
      have hScol : Collinear ℝ S := by
        have heq := finite_convexHull_eq_convexHull_extremePoints S hSfin
        rw [← hE'def] at heq
        have hSCH : S ⊆ convexHull ℝ E' := by rw [← heq]; exact subset_convexHull ℝ S
        exact hcolCH.subset hSCH
      obtain ⟨T, hTS, hT3⟩ := Set.exists_subset_card_eq (show (3 : ℕ) ≤ S.ncard by rw [hS]; norm_num)
      exact hnoncol T hTS hT3 (hScol.subset hTS)
    have hE'3 : E'.ncard = 3 := le_antisymm hle3 hge3
    obtain ⟨X, Y, Z, hXY, hXZ, hYZ, hXYZ⟩ := Set.ncard_eq_three.1 hE'3
    have hXE' : X ∈ E' := by rw [hXYZ]; simp
    have hYE' : Y ∈ E' := by rw [hXYZ]; simp
    have hZE' : Z ∈ E' := by rw [hXYZ]; simp
    have hXS := hE'S hXE'
    have hYS := hE'S hYE'
    have hZS := hE'S hZE'
    have hXex := (hE'E hXE').2
    have hYex := (hE'E hYE').2
    have hZex := (hE'E hZE').2
    have hdiff2 : (S \ E').ncard = 2 := by rw [Set.ncard_sdiff hE'S hE'fin, hS, hE'3]
    obtain ⟨P, Q, hPQ, hPQeq⟩ := Set.ncard_eq_two.1 hdiff2
    have hPmem : P ∈ S \ E' := by rw [hPQeq]; simp
    have hQmem : Q ∈ S \ E' := by rw [hPQeq]; simp
    have hPS := hPmem.1
    have hQS := hQmem.1
    have hPnotE' := hPmem.2
    have hQnotE' := hQmem.2
    have hXP : X ≠ P := fun h => hPnotE' (h ▸ hXE')
    have hXQ : X ≠ Q := fun h => hQnotE' (h ▸ hXE')
    have hYP : Y ≠ P := fun h => hPnotE' (h ▸ hYE')
    have hYQ : Y ≠ Q := fun h => hQnotE' (h ▸ hYE')
    have hZP : Z ≠ P := fun h => hPnotE' (h ▸ hZE')
    have hZQ : Z ≠ Q := fun h => hQnotE' (h ▸ hZE')
    -- Each vertex is off the line `PQ` (else three points of `S` would be collinear).
    have mkcross : ∀ W : ℝ × ℝ, W ∈ S → W ≠ P → W ≠ Q →
        (Q.1 - P.1) * (W.2 - P.2) - (Q.2 - P.2) * (W.1 - P.1) ≠ 0 := by
      intro W hWS hWP hWQ hz
      have hsub : ({W, P, Q} : Set (ℝ × ℝ)) ⊆ S := by
        intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl <;> assumption
      have hcard : ({W, P, Q} : Set (ℝ × ℝ)).ncard = 3 :=
        Set.ncard_eq_three.2 ⟨W, P, Q, hWP, hWQ, hPQ, rfl⟩
      exact hnoncol _ hsub hcard (collinear_of_cross_zero hPQ hz)
    have hcX := mkcross X hXS hXP hXQ
    have hcY := mkcross Y hYS hYP hYQ
    have hcZ := mkcross Z hZS hZP hZQ
    -- Same-side pair `⇒` convex quadrilateral; `P, Q` swapped when the shared side is negative.
    have goPos : ∀ A B : ℝ × ℝ, A ∈ S → B ∈ S →
        A ∉ convexHull ℝ (S \ {A}) → B ∉ convexHull ℝ (S \ {B}) →
        A ≠ B → A ≠ P → A ≠ Q → B ≠ P → B ≠ Q →
        0 < (Q.1 - P.1) * (A.2 - P.2) - (Q.2 - P.2) * (A.1 - P.1) →
        0 < (Q.1 - P.1) * (B.2 - P.2) - (Q.2 - P.2) * (B.1 - P.1) →
        ∃ T ⊆ S, T.ncard = 4 ∧ ¬∃ t ∈ T, t ∈ convexHull ℝ (T \ {t}) :=
      fun A B hAS hBS hAe hBe hAB hAP hAQ hBP hBQ hcA hcB =>
        quad_from_pair S A B P Q hAS hBS hPS hQS hAe hBe hAB hAP hAQ hBP hBQ hPQ hcA hcB
    have goNeg : ∀ A B : ℝ × ℝ, A ∈ S → B ∈ S →
        A ∉ convexHull ℝ (S \ {A}) → B ∉ convexHull ℝ (S \ {B}) →
        A ≠ B → A ≠ P → A ≠ Q → B ≠ P → B ≠ Q →
        (Q.1 - P.1) * (A.2 - P.2) - (Q.2 - P.2) * (A.1 - P.1) < 0 →
        (Q.1 - P.1) * (B.2 - P.2) - (Q.2 - P.2) * (B.1 - P.1) < 0 →
        ∃ T ⊆ S, T.ncard = 4 ∧ ¬∃ t ∈ T, t ∈ convexHull ℝ (T \ {t}) :=
      fun A B hAS hBS hAe hBe hAB hAP hAQ hBP hBQ hcA hcB =>
        quad_from_pair S A B Q P hAS hBS hQS hPS hAe hBe hAB hAQ hAP hBQ hBP (Ne.symm hPQ)
          (by have h : (P.1 - Q.1) * (A.2 - Q.2) - (P.2 - Q.2) * (A.1 - Q.1)
                = -((Q.1 - P.1) * (A.2 - P.2) - (Q.2 - P.2) * (A.1 - P.1)) := by ring
              rw [h]; linarith [hcA])
          (by have h : (P.1 - Q.1) * (B.2 - Q.2) - (P.2 - Q.2) * (B.1 - Q.1)
                = -((Q.1 - P.1) * (B.2 - P.2) - (Q.2 - P.2) * (B.1 - P.1)) := by ring
              rw [h]; linarith [hcB])
    rcases lt_or_gt_of_ne hcX with hX | hX <;>
      rcases lt_or_gt_of_ne hcY with hY | hY <;>
        rcases lt_or_gt_of_ne hcZ with hZ | hZ
    · exact goNeg X Y hXS hYS hXex hYex hXY hXP hXQ hYP hYQ hX hY
    · exact goNeg X Y hXS hYS hXex hYex hXY hXP hXQ hYP hYQ hX hY
    · exact goNeg X Z hXS hZS hXex hZex hXZ hXP hXQ hZP hZQ hX hZ
    · exact goPos Y Z hYS hZS hYex hZex hYZ hYP hYQ hZP hZQ hY hZ
    · exact goNeg Y Z hYS hZS hYex hZex hYZ hYP hYQ hZP hZQ hY hZ
    · exact goPos X Z hXS hZS hXex hZex hXZ hXP hXQ hZP hZQ hX hZ
    · exact goPos X Y hXS hYS hXex hYex hXY hXP hXQ hYP hYQ hX hY
    · exact goPos X Y hXS hYS hXex hYex hXY hXP hXQ hYP hYQ hX hY

end MathProof.Challenges.C0031Putnam1962A1

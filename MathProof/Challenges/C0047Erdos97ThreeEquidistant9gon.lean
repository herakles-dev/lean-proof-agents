import MathProof.Basic

set_option autoImplicit false

open Real
open scoped Classical

/-! Assembled by scripts/bank.sh from swarm bank C0047Danzer.
    Self-contained: bank cross-references were bare names in a shared namespace, so
    inlining them under one namespace preserves resolution. MUST pass check-proof.sh. -/

namespace MathProof.Challenges.C0047Erdos97ThreeEquidistant9gon

-- ── leaf: Witness ──



/-- **Replicated verbatim** from `FormalConjecturesForMathlib/Geometry/2d.lean`.
`ConvexIndep S` means every point of `S` is extremal — not in the convex hull of the rest. -/
def ConvexIndep (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

/-- **Replicated verbatim** from `FormalConjectures/ErdosProblems/97.lean`. -/
def HasNEquidistantPointsAt (n : ℕ) (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (p : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∃ r : ℝ, r > 0 ∧ (A.filter fun q ↦ dist p q = r).card ≥ n

/-- **Replicated verbatim** from `FormalConjectures/ErdosProblems/97.lean`. -/
def HasNEquidistantPointsOn (n : ℕ) (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (B : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ B, HasNEquidistantPointsAt n A p

/-- **Replicated verbatim** from `FormalConjectures/ErdosProblems/97.lean`. -/
def HasNEquidistantProperty (n : ℕ) (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  HasNEquidistantPointsOn n A A

/-- Danzer's 9 points (verbatim from the upstream witness). -/
noncomputable def danzer9 : Finset (EuclideanSpace ℝ (Fin 2)) :=
  { !₂[(-√3), -1], !₂[(√3), -1], !₂[0, 2],
    !₂[(-8991 / 10927 * √3), -26503 / 10927],
    !₂[(17747 / 10927 * √3), -235 / 10927],
    !₂[(-8756 / 10927 * √3), 26738 / 10927],
    !₂[(-10753 / 18529 * √3), -44665 / 18529],
    !₂[(27709 / 18529 * √3), 6203 / 18529],
    !₂[(-16956 / 18529 * √3), 38462 / 18529] }


-- ── leaf: ConvexIndep ──



/-- Danzer's 9 points are in convex position: each is extremal.

Strategy A — an explicit separating linear functional per point.  For point `pᵢ`
we use `fᵢ(x) = ⟪uᵢ, x⟫` with `uᵢ = !₂[w₁·√3, 3·w₂]`; because `√3·√3 = 3`, every
value `⟪uᵢ, pⱼ⟫` is a pure rational and `fᵢ(pᵢ) > fᵢ(pⱼ)` strictly for `j ≠ i`.
Hence `danzer9 \ {pᵢ}` lies in the open half-space `{x | fᵢ x < fᵢ pᵢ}`, which is
convex, so its convex hull does too — contradicting `pᵢ ∈ hull`. -/
theorem convexIndep_danzer9 : ConvexIndep (↑danzer9) := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  -- inner product of two explicit `Fin 2` euclidean vectors
  have ir : ∀ a0 a1 b0 b1 : ℝ,
      (inner ℝ (!₂[a0, a1] : EuclideanSpace ℝ (Fin 2)) (!₂[b0, b1])) = a0 * b0 + a1 * b1 := by
    intro a0 a1 b0 b1
    simp [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  -- separating-functional lemma: if `⟪u, ·⟫` strictly separates `p` from the rest,
  -- then `p` is not in the convex hull of the rest.
  have sep : ∀ (u p : EuclideanSpace ℝ (Fin 2)),
      (∀ x ∈ (↑danzer9 : Set (EuclideanSpace ℝ (Fin 2))) \ {p},
        (inner ℝ u x : ℝ) < inner ℝ u p) →
      p ∉ convexHull ℝ ((↑danzer9 : Set (EuclideanSpace ℝ (Fin 2))) \ {p}) := by
    intro u p hlt hp
    have hconv : Convex ℝ {x : EuclideanSpace ℝ (Fin 2) | (inner ℝ u x : ℝ) < inner ℝ u p} :=
      convex_halfSpace_lt ((innerₗ (EuclideanSpace ℝ (Fin 2)) u).isLinear) _
    have hsub : (↑danzer9 : Set (EuclideanSpace ℝ (Fin 2))) \ {p} ⊆
        {x | (inner ℝ u x : ℝ) < inner ℝ u p} := hlt
    have hmem := convexHull_min hsub hconv hp
    rw [Set.mem_ofPred_eq] at hmem
    exact lt_irrefl _ hmem
  intro a ha
  rw [Finset.mem_coe, danzer9] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sep (!₂[-√3, 0]) _ (by
      intro x hx; obtain ⟨hxd, hxne⟩ := hx
      rw [Finset.mem_coe, danzer9] at hxd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxd
      rcases hxd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hxne
          | (simp only [ir]; nlinarith [h3]))
  · exact sep (!₂[√3, -3]) _ (by
      intro x hx; obtain ⟨hxd, hxne⟩ := hx
      rw [Finset.mem_coe, danzer9] at hxd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxd
      rcases hxd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hxne
          | (simp only [ir]; nlinarith [h3]))
  · exact sep (!₂[√3, 3]) _ (by
      intro x hx; obtain ⟨hxd, hxne⟩ := hx
      rw [Finset.mem_coe, danzer9] at hxd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxd
      rcases hxd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hxne
          | (simp only [ir]; nlinarith [h3]))
  · exact sep (!₂[0, -3]) _ (by
      intro x hx; obtain ⟨hxd, hxne⟩ := hx
      rw [Finset.mem_coe, danzer9] at hxd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxd
      rcases hxd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hxne
          | (simp only [ir]; nlinarith [h3]))
  · exact sep (!₂[√3, 0]) _ (by
      intro x hx; obtain ⟨hxd, hxne⟩ := hx
      rw [Finset.mem_coe, danzer9] at hxd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxd
      rcases hxd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hxne
          | (simp only [ir]; nlinarith [h3]))
  · exact sep (!₂[0, 3]) _ (by
      intro x hx; obtain ⟨hxd, hxne⟩ := hx
      rw [Finset.mem_coe, danzer9] at hxd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxd
      rcases hxd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hxne
          | (simp only [ir]; nlinarith [h3]))
  · exact sep (!₂[√3, -6]) _ (by
      intro x hx; obtain ⟨hxd, hxne⟩ := hx
      rw [Finset.mem_coe, danzer9] at hxd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxd
      rcases hxd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hxne
          | (simp only [ir]; nlinarith [h3]))
  · exact sep (!₂[2 * √3, 3]) _ (by
      intro x hx; obtain ⟨hxd, hxne⟩ := hx
      rw [Finset.mem_coe, danzer9] at hxd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxd
      rcases hxd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hxne
          | (simp only [ir]; nlinarith [h3]))
  · exact sep (!₂[-4 * √3, 3]) _ (by
      intro x hx; obtain ⟨hxd, hxne⟩ := hx
      rw [Finset.mem_coe, danzer9] at hxd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxd
      rcases hxd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hxne
          | (simp only [ir]; nlinarith [h3]))


-- ── leaf: Equidistant ──



/-! ## Internal helpers (cut duplication across the 9 vertices). -/

/-- Reduce a `EuclideanSpace ℝ (Fin 2)` distance between two explicit `!₂[_, _]` points to the
rational identity `(Δx)² + (Δy)² = r²`. -/
private lemma dist_sqrt (a1 b1 a2 b2 r2 : ℝ) (h : (a1 - a2) ^ 2 + (b1 - b2) ^ 2 = r2) :
    dist (!₂[a1, b1] : EuclideanSpace ℝ (Fin 2)) !₂[a2, b2] = Real.sqrt r2 := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  congr 1
  show dist a1 a2 ^ 2 + dist b1 b2 ^ 2 = r2
  rw [Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
  exact h

/-- Two `!₂[_, _]` points differ if their first coordinates differ. -/
private lemma ne_of_fst_ne {a1 b1 a2 b2 : ℝ} (h : a1 ≠ a2) :
    (!₂[a1, b1] : EuclideanSpace ℝ (Fin 2)) ≠ !₂[a2, b2] :=
  fun he => h (congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) he)

/-- Two `!₂[_, _]` points differ if their second coordinates differ. -/
private lemma ne_of_snd_ne {a1 b1 a2 b2 : ℝ} (h : b1 ≠ b2) :
    (!₂[a1, b1] : EuclideanSpace ℝ (Fin 2)) ≠ !₂[a2, b2] :=
  fun he => h (congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) he)

/-- Package "`p` has 3 named, pairwise-distinct, equidistant peers in `danzer9`" into
`HasNEquidistantPointsAt`. -/
private lemma exists3 {p qa qb qc : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (hr : 0 < r) (hma : qa ∈ danzer9) (hmb : qb ∈ danzer9) (hmc : qc ∈ danzer9)
    (hda : dist p qa = r) (hdb : dist p qb = r) (hdc : dist p qc = r)
    (hab : qa ≠ qb) (hac : qa ≠ qc) (hbc : qb ≠ qc) :
    HasNEquidistantPointsAt 3 danzer9 p := by
  refine ⟨r, hr, ?_⟩
  have hsub : ({qa, qb, qc} : Finset (EuclideanSpace ℝ (Fin 2))) ⊆
      danzer9.filter fun q ↦ dist p q = r := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hma, hda⟩
    · exact Finset.mem_filter.mpr ⟨hmb, hdb⟩
    · exact Finset.mem_filter.mpr ⟨hmc, hdc⟩
  have hcard : ({qa, qb, qc} : Finset (EuclideanSpace ℝ (Fin 2))).card = 3 :=
    Finset.card_eq_three.mpr ⟨qa, qb, qc, hab, hac, hbc, rfl⟩
  calc (3 : ℕ) = ({qa, qb, qc} : Finset (EuclideanSpace ℝ (Fin 2))).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- The square root of `3`, used repeatedly to discharge the irrational-coordinate arithmetic. -/
private lemma sq_sqrt3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

set_option maxHeartbeats 4000000 in
/-- **Danzer's 9-point construction has the 3-equidistant property.** -/
theorem equidistant_danzer9 : HasNEquidistantProperty 3 danzer9 := by
  intro p hp
  rw [danzer9, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
    Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
    Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- p0, peers {1,2,5}, r² = 12
    apply exists3 (qa := !₂[(√3 : ℝ), -1]) (qb := !₂[(0 : ℝ), 2])
      (qc := !₂[(-8756 / 10927 * √3 : ℝ), 26738 / 10927]) (r := Real.sqrt 12)
    · exact Real.sqrt_pos.mpr (by norm_num)
    · rw [danzer9]; simp
    · rw [danzer9]; simp
    · rw [danzer9]; simp
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply ne_of_snd_ne; norm_num
    · apply ne_of_snd_ne; norm_num
    · apply ne_of_snd_ne; norm_num
  · -- p1, peers {0,2,3}, r² = 12
    apply exists3 (qa := !₂[(-√3 : ℝ), -1]) (qb := !₂[(0 : ℝ), 2])
      (qc := !₂[(-8991 / 10927 * √3 : ℝ), -26503 / 10927]) (r := Real.sqrt 12)
    · exact Real.sqrt_pos.mpr (by norm_num)
    · rw [danzer9]; simp
    · rw [danzer9]; simp
    · rw [danzer9]; simp
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply ne_of_snd_ne; norm_num
    · apply ne_of_snd_ne; norm_num
    · apply ne_of_snd_ne; norm_num
  · -- p2, peers {0,1,4}, r² = 12
    apply exists3 (qa := !₂[(-√3 : ℝ), -1]) (qb := !₂[(√3 : ℝ), -1])
      (qc := !₂[(17747 / 10927 * √3 : ℝ), -235 / 10927]) (r := Real.sqrt 12)
    · exact Real.sqrt_pos.mpr (by norm_num)
    · rw [danzer9]; simp
    · rw [danzer9]; simp
    · rw [danzer9]; simp
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply ne_of_fst_ne
      have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
      intro h; nlinarith
    · apply ne_of_snd_ne; norm_num
    · apply ne_of_snd_ne; norm_num
  · -- p3, peers {4,5,7}, r² = 259428/10927
    apply exists3 (qa := !₂[(17747 / 10927 * √3 : ℝ), -235 / 10927])
      (qb := !₂[(-8756 / 10927 * √3 : ℝ), 26738 / 10927])
      (qc := !₂[(27709 / 18529 * √3 : ℝ), 6203 / 18529]) (r := Real.sqrt (259428 / 10927))
    · exact Real.sqrt_pos.mpr (by norm_num)
    · rw [danzer9]; simp
    · rw [danzer9]; simp
    · rw [danzer9]; simp
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply ne_of_snd_ne; norm_num
    · apply ne_of_snd_ne; norm_num
    · apply ne_of_snd_ne; norm_num
  · -- p4, peers {3,5,8}, r² = 259428/10927
    apply exists3 (qa := !₂[(-8991 / 10927 * √3 : ℝ), -26503 / 10927])
      (qb := !₂[(-8756 / 10927 * √3 : ℝ), 26738 / 10927])
      (qc := !₂[(-16956 / 18529 * √3 : ℝ), 38462 / 18529]) (r := Real.sqrt (259428 / 10927))
    · exact Real.sqrt_pos.mpr (by norm_num)
    · rw [danzer9]; simp
    · rw [danzer9]; simp
    · rw [danzer9]; simp
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply ne_of_snd_ne; norm_num
    · apply ne_of_snd_ne; norm_num
    · apply ne_of_snd_ne; norm_num
  · -- p5, peers {3,4,6}, r² = 259428/10927
    apply exists3 (qa := !₂[(-8991 / 10927 * √3 : ℝ), -26503 / 10927])
      (qb := !₂[(17747 / 10927 * √3 : ℝ), -235 / 10927])
      (qc := !₂[(-10753 / 18529 * √3 : ℝ), -44665 / 18529]) (r := Real.sqrt (259428 / 10927))
    · exact Real.sqrt_pos.mpr (by norm_num)
    · rw [danzer9]; simp
    · rw [danzer9]; simp
    · rw [danzer9]; simp
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply ne_of_snd_ne; norm_num
    · apply ne_of_snd_ne; norm_num
    · apply ne_of_snd_ne; norm_num
  · -- p6, peers {2,7,8}, r² = 379164/18529
    apply exists3 (qa := !₂[(0 : ℝ), 2]) (qb := !₂[(27709 / 18529 * √3 : ℝ), 6203 / 18529])
      (qc := !₂[(-16956 / 18529 * √3 : ℝ), 38462 / 18529]) (r := Real.sqrt (379164 / 18529))
    · exact Real.sqrt_pos.mpr (by norm_num)
    · rw [danzer9]; simp
    · rw [danzer9]; simp
    · rw [danzer9]; simp
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply ne_of_snd_ne; norm_num
    · apply ne_of_snd_ne; norm_num
    · apply ne_of_snd_ne; norm_num
  · -- p7, peers {0,6,8}, r² = 379164/18529
    apply exists3 (qa := !₂[(-√3 : ℝ), -1]) (qb := !₂[(-10753 / 18529 * √3 : ℝ), -44665 / 18529])
      (qc := !₂[(-16956 / 18529 * √3 : ℝ), 38462 / 18529]) (r := Real.sqrt (379164 / 18529))
    · exact Real.sqrt_pos.mpr (by norm_num)
    · rw [danzer9]; simp
    · rw [danzer9]; simp
    · rw [danzer9]; simp
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply ne_of_snd_ne; norm_num
    · apply ne_of_snd_ne; norm_num
    · apply ne_of_snd_ne; norm_num
  · -- p8, peers {1,6,7}, r² = 379164/18529
    apply exists3 (qa := !₂[(√3 : ℝ), -1]) (qb := !₂[(-10753 / 18529 * √3 : ℝ), -44665 / 18529])
      (qc := !₂[(27709 / 18529 * √3 : ℝ), 6203 / 18529]) (r := Real.sqrt (379164 / 18529))
    · exact Real.sqrt_pos.mpr (by norm_num)
    · rw [danzer9]; simp
    · rw [danzer9]; simp
    · rw [danzer9]; simp
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply dist_sqrt; nlinarith [sq_sqrt3]
    · apply ne_of_snd_ne; norm_num
    · apply ne_of_snd_ne; norm_num
    · apply ne_of_snd_ne; norm_num


-- ── leaf: Nonempty ──


/-- The witness set is nonempty. -/
theorem danzer9_nonempty : danzer9.Nonempty := by
  rw [danzer9]
  exact Finset.insert_nonempty _ _


-- ── leaf: Main ──


/-- **Erdős #97, Danzer's variant** (`erdos_97.variants.three_equidistant`): there is a
convex-independent set of points in the plane with the 3-equidistant property. Combines the
three independently-proven leaves on the shared `danzer9` witness. -/
theorem erdos_97_variants_three_equidistant :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
      A.Nonempty ∧ ConvexIndep A ∧ HasNEquidistantProperty 3 A :=
  ⟨danzer9, danzer9_nonempty, convexIndep_danzer9, equidistant_danzer9⟩


end MathProof.Challenges.C0047Erdos97ThreeEquidistant9gon

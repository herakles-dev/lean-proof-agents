import MathProof.Basic

/-!
# MathProof.Certify.Sup — finite-`iSup` witness bridges

Part of `MathProof.Certify` (the witness→Lean-certificate "moat" for the finite-computation
solver layer). A solver decides a bound on `⨆ m : Fin n, f m` by scanning `f` over
`Finset.range n`; these two lemmas turn that scan into the two directions of a `≤`/`<` fact
about the actual `iSup`, for an arbitrary `f : ℕ → ℕ` — no domain-specific content (e.g. `σ`)
survives here, that lives in the calling challenge module.
-/

set_option autoImplicit false

namespace MathProof.Certify.Sup

/-- If `f m ≤ c` for every `m` in the scanned range `Finset.range n` (`n > 0` so the `iSup` is
over a nonempty index type), then `⨆ m : Fin n, f m ≤ c`. -/
theorem ciSup_le_of_forall_range {n c : ℕ} {f : ℕ → ℕ} (hn : 0 < n)
    (h : ∀ m ∈ Finset.range n, f m ≤ c) : (⨆ m : Fin n, f (m : ℕ)) ≤ c :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  ciSup_le fun m => h m (Finset.mem_range.mpr m.isLt)

/-- If some `m` in the scanned range `Finset.range n` witnesses `c < f m`, then
`c < ⨆ m : Fin n, f m`. -/
theorem lt_ciSup_of_exists_range {n c : ℕ} {f : ℕ → ℕ}
    (h : ∃ m ∈ Finset.range n, c < f m) : c < ⨆ m : Fin n, f (m : ℕ) := by
  obtain ⟨m, hm, hlt⟩ := h
  have hm' : m < n := Finset.mem_range.mp hm
  refine lt_of_lt_of_le hlt ?_
  have hb : BddAbove (Set.range fun m : Fin n => f (m : ℕ)) := (Set.finite_range _).bddAbove
  exact le_ciSup hb ⟨m, hm'⟩

end MathProof.Certify.Sup

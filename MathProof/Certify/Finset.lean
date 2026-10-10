import MathProof.Basic

/-!
# MathProof.Certify.Finset — `Set` ↔ `Finset` quantifier bridge

Part of `MathProof.Certify` (the witness→Lean-certificate "moat" for the finite-computation
solver layer). A solver that decides a property `P` of every *subset* of a finite vertex type
enumerates `Finset`s (the computable, enumerable shape); the target statement is usually phrased
over `Set V' ` (e.g. "every set of vertices ..."). This bridges the two quantifiers so a
`Finset`-indexed `decide` search certifies the `Set`-quantified statement (#128: the `∀ V' :
Set V` / `Finset` mismatch a naive port would silently get wrong).
-/

set_option autoImplicit false

namespace MathProof.Certify.Finset

/-- Over a `Fintype` ambient type, quantifying a predicate `P` over every `Set V'` is the same
as quantifying it over every `Finset` (coerced to a `Set`) — every subset of a finite type is
itself finite, hence `Finset`-representable. -/
theorem forall_set_iff_forall_finset {V : Type*} [Fintype V] {P : Set V → Prop} :
    (∀ V' : Set V, P V') ↔ ∀ s : _root_.Finset V, P (↑s : Set V) := by
  constructor
  · intro h s
    exact h (↑s)
  · intro h V'
    have hfin : V'.Finite := Set.toFinite V'
    have hP := h hfin.toFinset
    rwa [hfin.coe_toFinset] at hP

end MathProof.Certify.Finset

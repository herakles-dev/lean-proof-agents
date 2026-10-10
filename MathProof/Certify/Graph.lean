import MathProof.Basic

/-!
# MathProof.Certify.Graph — finite-graph witness bridges

Part of `MathProof.Certify` (the witness→Lean-certificate "moat" for the finite-computation
solver layer). Builds a `SimpleGraph` from a boolean adjacency table produced by a solver, and
fills a decidability gap Mathlib doesn't ship: `Decidable p.IsPath` exists
(`SimpleGraph.Walk` instance), but `Decidable p.IsTrail` / `Decidable p.IsCycle` do not, so a
`decide`-based search over walks of a concrete finite graph has no anchor without them.
-/

set_option autoImplicit false

namespace MathProof.Certify.Graph

open SimpleGraph

/-- Build a `SimpleGraph` on `Fin n` from a boolean adjacency function (the shape a solver
witness naturally produces). Irreflexive/symmetric by construction via `SimpleGraph.fromRel`. -/
def ofAdjBool {n : ℕ} (adj : Fin n → Fin n → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => adj i j = true)

instance {n : ℕ} (adj : Fin n → Fin n → Bool) : DecidableRel (ofAdjBool adj).Adj := by
  unfold ofAdjBool; infer_instance

/-- `IsTrail` is decidable for any graph with decidable adjacency on a `DecidableEq` vertex
type: it unfolds to `p.edges.Nodup`, decidable once `Sym2 V` has decidable equality. -/
instance decIsTrail {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) : Decidable p.IsTrail :=
  decidable_of_iff _ (Walk.isTrail_def p).symm

/-- `IsCycle` is decidable for any graph with decidable adjacency on a `DecidableEq` vertex
type: swap Mathlib's `p ≠ nil` disjunct for the decidable `p.length ≠ 0`, equivalent to it. -/
instance decIsCycle {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {u : V} (p : G.Walk u u) : Decidable p.IsCycle :=
  decidable_of_iff (p.IsTrail ∧ p.length ≠ 0 ∧ p.support.tail.Nodup) (by
    rw [Walk.isCycle_def]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, fun h => h2 (by subst h; rfl), h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, fun h => h2 (by cases p <;> simp_all), h3⟩)

-- TODO (Wave D, #64): `no_pow2_cycle_of_forall_len` — the headline "no cycle of length a power
-- of 2 in a graph whose every cycle length satisfies P" bridge is DEFERRED. Do not stub it with
-- a `sorry`; add it as a real proof when Wave D lands.

end MathProof.Certify.Graph

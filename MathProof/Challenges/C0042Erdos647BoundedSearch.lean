import MathProof.Basic
import MathProof.Certify

set_option autoImplicit false

open ArithmeticFunction ArithmeticFunction.sigma

/-!
# Challenge C0042 — Erdős #647, bounded no-witness certificate

**Status:** ✅ SOLVED — a bounded **partial** result (read the honesty note).

Erdős #647 asks whether there is some `n > 24` with
`max_{m < n} (m + τ(m)) ≤ n + 2` (τ = number of divisors = `σ 0`). This is an OPEN
problem; Erdős called such an `n` "extremely doubtful".

This challenge certifies the honest fact the solver layer's `sweep` produced: **there is
no such witness in `[25, 60)`.** The sweep (`scripts/solve.sh` + `predicates/pred647.py`)
searched far past that — no witness ≤ 2·10⁶, min excess `1` at `n = 35` — but that wider
range is *searched*, not kernel-*certified*. What `decide +kernel` verifies under the
trusted axioms is the `[25,60)` window; closing the searched-vs-certified gap is the
reflection work (Certify v2).

**This is NOT the £25 prize.** That needs an actual witness `n` (none exists within reach)
or a full resolution of the open problem. The kernel certifies only the bounded claim.

Pipeline: `lit-search` (open-confirmed) → `search-reducer` (shape `sweep`) → `solve.sh sweep`
→ this certificate via `MathProof.Certify.Sup.lt_ciSup_of_exists_range` (the witness→Lean moat).
-/

namespace MathProof.Challenges.C0042Erdos647BoundedSearch

/-- Decidable core (`decide +kernel`): for every `n ∈ [25,60)`, some `m < n` has
`n + 2 < m + τ(m)` — i.e. `n` fails the #647 condition. -/
theorem no_witness_core :
    ∀ n ∈ Finset.Ico 25 60, ∃ m ∈ Finset.range n, n + 2 < m + σ 0 m := by
  decide +kernel

/-- Bounded no-witness certificate for Erdős #647 over `[25,60)`: the supremum
`⨆_{m<n} (m + τ(m))` strictly exceeds `n + 2`, so no `n` in this window is a #647 witness.
Bridged from the decidable core by `Certify.Sup.lt_ciSup_of_exists_range`. -/
theorem no_witness_below_60 :
    ∀ n ∈ Finset.Ico 25 60, n + 2 < ⨆ m : Fin n, ((m : ℕ) + σ 0 m) := by
  intro n hn
  exact MathProof.Certify.Sup.lt_ciSup_of_exists_range (no_witness_core n hn)

end MathProof.Challenges.C0042Erdos647BoundedSearch

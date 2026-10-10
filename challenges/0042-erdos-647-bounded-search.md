# 0042 — Erdős #647 (bounded no-witness certificate)

**Status:** ✅ SOLVED (bounded **partial** result) · **Module:** `MathProof/Challenges/C0042Erdos647BoundedSearch.lean`

## Problem (Erdős #647 — OPEN)
Is there some `n > 24` with `max_{m<n} (m + τ(m)) ≤ n + 2`? (τ = number of divisors = `σ 0`.)
Erdős called such an `n` "extremely doubtful". Tagged `verifiable`, £25 (erdosproblems.com/647).

## What is certified here
`no_witness_below_60 : ∀ n ∈ Finset.Ico 25 60, n + 2 < ⨆ m : Fin n, ((m : ℕ) + σ 0 m)` —
i.e. **no #647 witness exists in `[25, 60)`** (the supremum strictly exceeds `n + 2`, so every such
`n` fails the condition). Proved by a `decide +kernel` core (`no_witness_core`) bridged to the
⨆-form via `MathProof.Certify.Sup.lt_ciSup_of_exists_range` (the witness→Lean moat). Axioms: the
trusted trio only (no `sorryAx`, no `Lean.ofReduceBool`).

## Honesty / scope
- **Searched vs. certified:** `scripts/solve.sh sweep --py scripts/predicates/pred647.py` found no
  witness up to 2·10⁶ (min excess `1` at `n = 35`), but only `[25, 60)` is *kernel-certified*
  (the `decide +kernel` ceiling). The wider *searched* range is evidence, not proof; certifying it
  needs the Certify v2 reflection checker.
- **NOT the £25 prize.** The prize needs an actual witness `n` (none exists within reach) or a full
  resolution of the open problem. This is an honest, Lean-checked bounded partial result.

## Pipeline (the finite-computation solver layer, run end-to-end)
`lit-search` (open-confirmed) → `search-reducer` (shape `sweep`) → `solve.sh sweep`
(`.search/647/witness.json`) → `witness-to-lean.sh` → this certificate → `check-proof.sh`
(clean axioms) → `proof-auditor`.

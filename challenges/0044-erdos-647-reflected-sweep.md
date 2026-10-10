# Challenge 0044 — Erdős #647, reflection-certified no-witness (Certify v2)

- **Module:** `MathProof/Challenges/C0044Erdos647ReflectedSweep.lean`
- **Theorems:** `sweep_ok_3000`, `no_witness_below_3000`
- **Status:** ✅ SOLVED — bounded **partial** result; `sorry`-free, axioms clean
  (`scripts/check-proof.sh C0044Erdos647ReflectedSweep --all`).

## Problem

Erdős #647 asks whether there is some `n > 24` with `max_{m < n} (m + τ(m)) ≤ n + 2`
(τ = number of divisors = `σ 0`). OPEN; Erdős called such an `n` "extremely doubtful".

This certifies the honest **no-witness** fact on `[25, 3000)` — the upper bound is raised from 60 (the v1
certificate `C0042`, `[25, 60)`) to 3000 — using **proof by reflection** (Certify v2). **Not the £25 prize:**
the wider `[25, 3000)` is kernel-*certified*; the solver `sweep` searched to `2·10⁶` (no witness,
min excess `1` at `n = 35`) but that is *searched*, not proved.

## Formal statement

```lean
-- reflective decidable core: a pure-Nat Bool sweep, kernel-evaluated
theorem sweep_ok_3000 : sweepS 0 0 3000 = true := by decide +kernel

-- the certificate over [25, 3000)
theorem no_witness_below_3000 :
    ∀ n ∈ Finset.Ico 25 3000, n + 2 < ⨆ m : Fin n, ((m : ℕ) + σ 0 m)
```

## How it works (Certify v2 = proof by reflection)

`MathProof.Certify.Reflect` provides:
- `tauS : ℕ → ℕ` — a fast trial-division divisor count (O(√n)), proven `tauS n = σ 0 n`
  (`tauS_eq`) — the crux, a genuinely new Mathlib-gap lemma (no √n divisor-pairing existed).
- `sweepS : ℕ → ℕ → ℕ → Bool` — a **structural** (kernel-reducible, `brecOn`) Bool prefix-max
  sweep, with `sweepS_sound` certifying `sweepS 0 0 N = true → ∀ n ∈ [25,N), ∃ m < n, n+2 < m+σ0 m`.

`decide +kernel` then evaluates the checker with GMP-accelerated `Nat` arithmetic instead of
unfolding `Finset.divisors`/`Multiset` (the v1 bottleneck, which became intractable at a few hundred). Bridged to the `iSup`
form by `Certify.Sup.lt_ciSup_of_exists_range`.

**Axioms:** `sweep_ok_3000` depends on *no axioms*; `no_witness_below_3000` on `[propext,
Classical.choice, Quot.sound]`. **No `native_decide`; `TRUSTED_AXIOMS` untouched.**

## Significance

The first shipped piece of Certify **v2**: a reusable reflection pattern (a Bool checker plus a
soundness theorem, evaluated by the kernel) that makes larger *certified* finite checks possible
without trusting a solver or the compiler. A graph checker could follow the same pattern; none
exists yet, and this challenge is a divisor-count sweep over 3000 integers, not progress on the
graph-theoretic Erdős problems. The reflection design is described in the header comment of
`MathProof/Certify/Reflect.lean`.

import MathProof.Basic
import MathProof.Certify

set_option autoImplicit false

open ArithmeticFunction ArithmeticFunction.sigma
open MathProof.Certify.Reflect

/-!
# Challenge C0044 — Erdős #647, reflection-certified no-witness (Certify v2)

**Status:** ✅ SOLVED — a bounded **partial** result (read the honesty note), at **50× the range**
of the v1 certificate `C0042` via proof-by-reflection.

Erdős #647 asks whether there is some `n > 24` with `max_{m < n} (m + τ(m)) ≤ n + 2`
(τ = number of divisors = `σ 0`). This is OPEN; Erdős called such an `n` "extremely doubtful".

Where `C0042` (v1) certified the no-witness fact on `[25, 60)` by unfolding `σ 0` over `Finset`s
under `decide +kernel` (which dies by N≈300), this uses the **Certify v2 reflective checker**
(`MathProof.Certify.Reflect`): a fast pure-`Nat` divisor count `tauS` — proven equal to Mathlib's
`σ 0` in `tauS_eq` — inside a structural Bool prefix-max sweep `sweepS`, whose `sweepS_sound`
lemma certifies that a `true` result implies the no-witness fact. `decide +kernel` then evaluates
the checker with GMP-accelerated `Nat` arithmetic, certifying **`[25, 3000)`** in ~30 s — with
**no `native_decide`**, axioms `[propext, Classical.choice, Quot.sound]`.

**This is NOT the £25 prize.** The solver `sweep` found no witness `≤ 2·10⁶` (min excess `1` at
`n = 35`), but only `[25, 3000)` is kernel-*certified* here; the wider range is *searched*, not
proved. Closing the gap further is more reflection (a larger `N` under the same checker) and,
ultimately, Tier-2 compute — never `native_decide`.

Pipeline: v1 `C0042` → **Certify v2** (`Reflect.tauS_eq` + `Reflect.sweepS_sound`) → this
certificate via `Certify.Sup.lt_ciSup_of_exists_range`.
-/

namespace MathProof.Challenges.C0044Erdos647ReflectedSweep

/-- Reflective decidable core (`decide +kernel` over a pure-`Nat` Bool program): the sweep checker
returns `true` on `[0, 3000)`. Certifies in ~30 s where the v1 `Finset`-`σ 0` form dies by N≈300. -/
theorem sweep_ok_3000 : sweepS 0 0 3000 = true := by decide +kernel

/-- **Bounded no-witness certificate for Erdős #647 over `[25, 3000)`** (50× the v1 window of
`C0042`): for every `n` in this range, `⨆_{m < n} (m + τ(m))` strictly exceeds `n + 2`, so no such
`n` is a #647 witness. Bridged from the reflective core by `Reflect.sweepS_sound` (soundness of the
checker) then `Certify.Sup.lt_ciSup_of_exists_range`. -/
theorem no_witness_below_3000 :
    ∀ n ∈ Finset.Ico 25 3000, n + 2 < ⨆ m : Fin n, ((m : ℕ) + σ 0 m) := by
  intro n hn
  exact MathProof.Certify.Sup.lt_ciSup_of_exists_range (sweepS_sound 3000 sweep_ok_3000 n hn)

end MathProof.Challenges.C0044Erdos647ReflectedSweep

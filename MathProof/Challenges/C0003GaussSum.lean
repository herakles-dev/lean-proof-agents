import MathProof.Basic

/-!
# Challenge C0003 — Gauss's sum by induction

**Statement:** `(0 + 1 + ⋯ + n) · 2 = n · (n + 1)`.
**Status:** SOLVED ✅

Our first genuine *hand* proof — a real induction, not a one-line library citation.
We use the times-two form to stay entirely in ℕ (no truncated division), unfold the
sum with `Finset.sum_range_succ`, feed in the induction hypothesis, and finish with `ring`.

(Mathlib already has `Finset.sum_range_id`; the point here is to write the induction.)
-/

namespace MathProof.Challenges.C0003GaussSum

open Finset

/-- Gauss's schoolboy sum, in division-free form: `(∑_{i<n+1} i) · 2 = n · (n+1)`. -/
theorem gauss_sum (n : ℕ) : (∑ i ∈ range (n + 1), i) * 2 = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, add_mul, ih]
    ring

end MathProof.Challenges.C0003GaussSum

import MathProof.Basic

/-!
# Challenge C0001 — Warmup: √2 is irrational

**Statement:** `Real.sqrt 2` is irrational.
**Status:** SOLVED ✅

This warmup exists to demonstrate the full loop: state a theorem, close it with a
real (machine-checked) proof, and verify completeness with `scripts/check-proof.sh`.
It leans on Mathlib's `irrational_sqrt_two`.
-/

namespace MathProof.Challenges.C0001Warmup

/-- The square root of two is irrational. -/
theorem sqrt_two_irrational : Irrational (Real.sqrt 2) :=
  irrational_sqrt_two

end MathProof.Challenges.C0001Warmup

import MathProof.Basic

/-!
# Challenge C0025EulerTotientTheorem — Euler's theorem (unfolded `% n` form)

**Status:** ✅ SOLVED

Fermat–Euler: if `gcd(a, n) = 1` then `a ^ φ(n) ≡ 1 (mod n)`, stated in the *unfolded*
remainder form `a ^ Nat.totient n % n = 1 % n` (holds for all `n`, including `0` and `1`).

DEPTH-loop ANCHOR-rung target: the winning move is a single Mathlib lemma
(`Nat.ModEq.pow_totient`, whose `≡ [MOD n]` conclusion is definitionally this `%` goal),
which a first-principles attempt won't reach.
-/

namespace MathProof.Challenges.C0025EulerTotientTheorem

/-- **Euler's theorem** (unfolded form): for coprime `a n`, `a ^ φ(n) ≡ 1 (mod n)`. -/
theorem euler {a n : ℕ} (h : Nat.Coprime a n) :
    a ^ Nat.totient n % n = 1 % n := by
  -- `Nat.ModEq.pow_totient h : a ^ φ n ≡ 1 [MOD n]`, and `≡ [MOD n]` is *definitionally*
  -- `_ % n = _ % n`, so it closes this goal directly (keeper ANCHOR decision).
  exact Nat.ModEq.pow_totient h

end MathProof.Challenges.C0025EulerTotientTheorem

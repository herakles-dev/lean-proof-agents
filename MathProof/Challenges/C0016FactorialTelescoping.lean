import MathProof.Basic

/-!
# Challenge C0016FactorialTelescoping — factorial telescoping sum

**Status:** ✅ SOLVED

`∑_{i<n} i·i! = n! - 1`, proved in the equivalent additive form
`(∑_{i<n} i·i!) + 1 = n!` by induction on `n`, telescoping via `Nat.factorial_succ`.
-/

namespace MathProof.Challenges.C0016FactorialTelescoping

/-- The sum `∑_{i<n} i·i!` telescopes to `n! - 1` (stated additively to stay in `ℕ`). -/
theorem factorial_telescope (n : ℕ) :
    (∑ i ∈ Finset.range n, i * Nat.factorial i) + 1 = Nat.factorial n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.factorial_succ, ← ih]
    ring

end MathProof.Challenges.C0016FactorialTelescoping

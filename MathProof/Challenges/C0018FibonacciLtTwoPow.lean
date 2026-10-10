import MathProof.Basic

/-!
# Challenge C0018FibonacciLtTwoPow — Fibonacci numbers are bounded by powers of two

**Status:** ✅ SOLVED

`Nat.fib n < 2 ^ n` for every natural number `n`. Fibonacci is a two-term recurrence
(`fib (n+2) = fib n + fib (n+1)`), so a single-step induction isn't enough on its own;
we strengthen the induction hypothesis to a conjunction carrying both `fib n < 2^n`
and `fib (n+1) < 2^(n+1)` simultaneously, then induct on that.
-/

namespace MathProof.Challenges.C0018FibonacciLtTwoPow

/-- Every Fibonacci number is strictly smaller than the corresponding power of two. -/
theorem fib_lt_two_pow (n : ℕ) : Nat.fib n < 2 ^ n := by
  suffices h : ∀ m : ℕ, Nat.fib m < 2 ^ m ∧ Nat.fib (m + 1) < 2 ^ (m + 1) by
    exact (h n).1
  intro m
  induction m with
  | zero => decide
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    rw [Nat.fib_add_two]
    have e1 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    have e2 : (2 : ℕ) ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; ring
    omega

end MathProof.Challenges.C0018FibonacciLtTwoPow

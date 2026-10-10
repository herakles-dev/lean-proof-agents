import MathProof.Basic

/-!
# Challenge C0015FibonacciSquaresSum — sum of squares of Fibonacci numbers

**Status:** ✅ SOLVED

Classical identity: `∑_{i=0}^{n} fib(i)^2 = fib(n) * fib(n+1)`.

Not imported by `MathProof.lean` until `scripts/new-challenge.sh` copies it.
-/

namespace MathProof.Challenges.C0015FibonacciSquaresSum

/-- The sum of the squares of the first `n + 1` Fibonacci numbers equals
`fib n * fib (n + 1)`. Proved by induction on `n`, using the Fibonacci
recurrence `fib (n + 2) = fib n + fib (n + 1)` to bridge the inductive step. -/
theorem fib_sq_sum (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), Nat.fib i ^ 2) = Nat.fib n * Nat.fib (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.fib_add_two]
    ring

end MathProof.Challenges.C0015FibonacciSquaresSum

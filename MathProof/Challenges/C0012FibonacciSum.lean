import MathProof.Basic

/-!
# Challenge C0012FibonacciSum — Fibonacci partial-sum identity

**Status:** ✅ SOLVED

Verify:  `scripts/check-proof.sh C0012FibonacciSum`
-/

namespace MathProof.Challenges.C0012FibonacciSum

/-- The sum of the first `n` Fibonacci numbers, `fib 0 + fib 1 + ... + fib (n-1)`, equals
`fib (n + 1) - 1`. Stated with `+ 1` on the left to avoid ℕ subtraction. -/
theorem fib_sum (n : ℕ) : (∑ i ∈ Finset.range n, Nat.fib i) + 1 = Nat.fib (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, Nat.fib_add_two]; omega

end MathProof.Challenges.C0012FibonacciSum

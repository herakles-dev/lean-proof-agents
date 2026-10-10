# Challenge 0018 — Fibonacci Lt Two Pow

- **Module:** `MathProof/Challenges/C0018FibonacciLtTwoPow.lean`
- **Theorem:** `MathProof.Challenges.C0018FibonacciLtTwoPow.fib_lt_two_pow`
- **Status:** ✅ SOLVED

## Problem

Every Fibonacci number is strictly smaller than the corresponding power of two:
`fib(n) < 2^n` for all natural numbers `n`.

## Formal statement

```lean
theorem fib_lt_two_pow (n : ℕ) : Nat.fib n < 2 ^ n
```

## Notes

Fibonacci is a two-term recurrence (`fib (n+2) = fib n + fib (n+1)`), so a plain
single-step induction on `fib n < 2^n` alone doesn't carry enough information forward.
The proof strengthens the induction hypothesis to the conjunction
`fib m < 2^m ∧ fib (m+1) < 2^(m+1)` and inducts on that instead, using
`Nat.fib_add_two` and `pow_succ` to unfold both sides of the step, then closing the
resulting linear arithmetic with `omega`.

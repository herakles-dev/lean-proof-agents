# Challenge 0015 — Fibonacci Squares Sum

- **Module:** `MathProof/Challenges/C0015FibonacciSquaresSum.lean`
- **Theorem:** `MathProof.Challenges.C0015FibonacciSquaresSum.fib_sq_sum`
- **Status:** ✅ SOLVED

## Problem

For every natural number `n`, the sum of the squares of the first `n + 1` Fibonacci
numbers equals the product of `fib n` and `fib (n + 1)`:

∑_{i=0}^{n} fib(i)^2 = fib(n) · fib(n+1)

## Formal statement

```lean
theorem fib_sq_sum (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), Nat.fib i ^ 2) = Nat.fib n * Nat.fib (n + 1)
```

## Notes

Proved by induction on `n` using `Finset.sum_range_succ` to peel off the last term and
`Nat.fib_add_two` (`fib (n + 2) = fib n + fib (n + 1)`) to rewrite the inductive step into
an algebraic identity closed by `ring`.

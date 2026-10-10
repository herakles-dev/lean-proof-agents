# Challenge 0012 — Fibonacci partial sum

- **Module:** `MathProof/Challenges/C0012FibonacciSum.lean`
- **Theorem:** `MathProof.Challenges.C0012FibonacciSum.fib_sum`
- **Status:** ✅ SOLVED

## Problem

The sum of the first `n` Fibonacci numbers is one less than a later Fibonacci number:
`fib 0 + fib 1 + … + fib (n-1) = fib (n+1) - 1`. Stated with `+ 1` on the left to avoid
ℕ truncated subtraction, so it holds for **all** `n : ℕ` including `n = 0`.

## Formal statement

```lean
theorem fib_sum (n : ℕ) : (∑ i ∈ Finset.range n, Nat.fib i) + 1 = Nat.fib (n + 1)
```

## Notes

Genuine from-scratch induction (no single Mathlib citation):

```lean
induction n with
| zero => simp
| succ n ih => rw [Finset.sum_range_succ, Nat.fib_add_two]; omega
```

`Finset.sum_range_succ` peels the last term, `Nat.fib_add_two` supplies the recurrence, and
`omega` closes the linear arithmetic against the induction hypothesis.
Axioms: `[propext, Classical.choice, Quot.sound]` (clean).

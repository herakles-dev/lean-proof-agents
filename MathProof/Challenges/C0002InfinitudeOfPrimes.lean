import MathProof.Basic

/-!
# Challenge C0002 — Infinitude of primes (Euclid's theorem)

**Statement:** there is no largest prime — equivalently, the set of primes is infinite.
**Status:** SOLVED ✅

Two forms of the same classical fact, both discharged via Mathlib:
* `euclid` — for every bound `n` there is a prime `p ≥ n`;
* `infinitude_of_primes` — the set `{p | p.Prime}` is infinite.
-/

namespace MathProof.Challenges.C0002InfinitudeOfPrimes

/-- Euclid's theorem: for every `n` there exists a prime `p` with `n ≤ p`. -/
theorem euclid (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime :=
  Nat.exists_infinite_primes n

/-- The set of prime natural numbers is infinite. -/
theorem infinitude_of_primes : {p : ℕ | p.Prime}.Infinite :=
  Nat.infinite_setOfPred_prime

end MathProof.Challenges.C0002InfinitudeOfPrimes

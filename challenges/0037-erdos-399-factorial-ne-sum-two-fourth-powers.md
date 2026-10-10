# Challenge 0037 — Erdos 399 Factorial Ne Sum Two Fourth Powers

- **Module:** `MathProof/Challenges/C0037Erdos399FactorialNeSumTwoFourthPowers.lean`
- **Theorem:** `MathProof.Challenges.C0037Erdos399FactorialNeSumTwoFourthPowers.erdos_399_cambie`
- **Status:** ✅ SOLVED (axioms: propext, Classical.choice, Quot.sound)

## Problem

Erdős Problem #399, Cambie's coprime variant: for coprime natural numbers `x, y` with
`x·y > 1`, no factorial equals `x⁴ + y⁴`. (The unrestricted Erdős #399 — which also allows the
form `n! + yᵏ = xᵏ` — *does* have solutions: `10! + 36⁴ = 48⁴`, i.e. `10! = 48⁴ − 36⁴`, where
`gcd(48,36) = 12` are non-coprime. The coprime **sum** form proved here is the impossible one.)

**Source:** google-deepmind/formal-conjectures, `ErdosProblems/399.lean`, theorem
`erdos_399.variants.cambie`, tagged `@[category research solved, AMS 11]` with a `sorry` body
upstream when this was written (September 2026), i.e. a formalization gap for a result tagged as solved. Statement reproduced verbatim.

## Formal statement

```lean
theorem erdos_399_cambie {n x y : ℕ} (hxy : x.Coprime y) (h1 : 1 < x * y) :
    n ! ≠ x ^ 4 + y ^ 4
```

## Proof sketch

By contradiction, assume `n ! = x ^ 4 + y ^ 4`, split on `n < 4` vs `4 ≤ n`:

- **`n < 4`:** `n ! ≤ 6` (`interval_cases n <;> decide`). Since `1 < x * y`, not both `x, y ≤ 1`,
  so `2 ≤ x ∨ 2 ≤ y`, giving `x ^ 4 + y ^ 4 ≥ 2 ^ 4 = 16 > 6 ≥ n !` — contradiction via `omega`.
- **`4 ≤ n`:** `8 ∣ n !` (`4 ! = 24` is divisible by `8`, and `4 ! ∣ n !` via
  `Nat.factorial_dvd_factorial`), so `8 ∣ x ^ 4 + y ^ 4`. Coprimality forbids `x, y` both even
  (a common factor `2` would divide `gcd x y = 1`). A from-scratch parity lemma
  `∀ z, z ^ 4 % 8 = z % 2` (proved by `ring`-normalizing `(k+k)^4 = 8*(2*k^4)` and
  `(2*k+1)^4 = 8*(2*k^4+4*k^3+3*k^2+k)+1`, closed by `omega`) pins `x ^ 4 % 8` and `y ^ 4 % 8`
  to `x % 2` and `y % 2`. Since not both are `0`, `(x^4+y^4) % 8 ≠ 0`, contradicting `8 ∣ x^4+y^4`
  — closed by `omega`.

Verify: `scripts/check-proof.sh C0037Erdos399FactorialNeSumTwoFourthPowers erdos_399_cambie`.

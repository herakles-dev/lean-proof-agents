# Challenge 0025 — Euler's theorem (Fermat–Euler totient theorem)

- **Module:** `MathProof/Challenges/C0025EulerTotientTheorem.lean`
- **Theorem:** `MathProof.Challenges.C0025EulerTotientTheorem.euler`
- **Status:** ✅ SOLVED

## Problem

> If `a` and `n` are natural numbers with `gcd(a, n) = 1`, then
> `a ^ φ(n) ≡ 1 (mod n)`, where `φ` is Euler's totient.

Stated in the **unfolded remainder form** (`% n`), which holds for all `n` (including the
degenerate `n = 0, 1`), and keeps the coprimality hypothesis (required — e.g. `a=2, n=4`
fails without it).

## Formal statement

```lean
theorem euler {a n : ℕ} (h : Nat.Coprime a n) :
    a ^ Nat.totient n % n = 1 % n
```

## Notes

DEPTH-loop **ANCHOR-rung** dogfood. A deliberately *naive* first-principles attempt
(induction on `n`, no lemma search) was dispatched first and **BLOCKED**: the induction
hypothesis is gated on `a.Coprime n` (not derivable from `a.Coprime (n+1)`), and `Nat.totient`
has no elementary recursive step. `stall-check` → STALL → `proof-trajectory-keeper` returned
**ANCHOR** (the failure signature = "no applicable lemma") → the winning move is the single
library lemma `Nat.ModEq.pow_totient` (`Mathlib/FieldTheory/Finite/Basic.lean`), whose
`≡ [MOD n]` conclusion is *definitionally* the `% n` goal, so `exact Nat.ModEq.pow_totient h`
closes it. Axioms: `{propext, Classical.choice, Quot.sound}`.

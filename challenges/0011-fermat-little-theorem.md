# Challenge 0011 — Fermat's Little Theorem

- **Module:** `MathProof/Challenges/C0011FermatLittleTheorem.lean`
- **Theorem:** `MathProof.Challenges.C0011FermatLittleTheorem.fermat_little`
- **Status:** ✅ SOLVED

## Problem

Fermat's Little Theorem (the `ZMod p` form): for a prime `p` and **any** `a : ZMod p`,
`a ^ p = a`. (Equivalently `a ^ (p-1) = 1` for `a ≠ 0`; the `a^p = a` form is the clean
universal statement that also holds at `a = 0`.)

## Formal statement

```lean
theorem fermat_little (p : ℕ) [Fact p.Prime] (a : ZMod p) : a ^ p = a
```

## Notes

One-line citation of `ZMod.pow_card` (Mathlib `FieldTheory/Finite/Basic.lean`). The
`[Fact p.Prime]` instance is what supplies the field structure on `ZMod p`.
Axioms: `[propext, Classical.choice, Quot.sound]` (clean).

# Challenge 0014 — Wilson's theorem

- **Module:** `MathProof/Challenges/C0014WilsonTheorem.lean`
- **Theorem:** `MathProof.Challenges.C0014WilsonTheorem.wilson`
- **Status:** ✅ SOLVED

## Problem

Wilson's theorem: for a prime `p`, `(p - 1)!` is congruent to `-1` modulo `p`.

## Formal statement

```lean
theorem wilson (p : ℕ) [Fact p.Prime] : ((p - 1)! : ZMod p) = -1
```

Here `(p - 1)!` is `Nat.factorial (p - 1)` (via `open Nat`) cast into `ZMod p`.

## Notes

One-line citation of `ZMod.wilsons_lemma` (Mathlib `NumberTheory/Wilson.lean`). The
`[Fact p.Prime]` instance is genuine (it builds the field instance used by the lemma), so the
statement is non-vacuous.
Axioms: `[propext, Classical.choice, Quot.sound]` (clean).

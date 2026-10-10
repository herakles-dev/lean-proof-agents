# Challenge 0023 — IMO 1988 Q6 perfect square

- **Module:** `MathProof/Challenges/C0023IMO1988Q6PerfectSquare.lean`
- **Theorem:** `MathProof.Challenges.C0023IMO1988Q6PerfectSquare.imo1988_q6`
- **Status:** ✅ SOLVED

## Problem

International Mathematical Olympiad 1988, Problem 6 (famously hard — several jury members
failed to solve it in the time limit; it introduced the *Vieta jumping* technique).

> Let `a` and `b` be positive integers such that `a·b + 1` divides `a² + b²`.
> Show that `(a² + b²) / (a·b + 1)` is a perfect square.

## Formal statement

```lean
theorem imo1988_q6 {a b : ℕ} (h : a * b + 1 ∣ a ^ 2 + b ^ 2) :
    ∃ d, d ^ 2 = (a ^ 2 + b ^ 2) / (a * b + 1)
```

The `ℕ`-division is exact because of the divisibility hypothesis, so `∃ d, d² = quotient`
faithfully states "the quotient is a perfect square" (this is identical to Mathlib's Archive
statement — not a weakening).

## Notes

Proof method: **constant-descent Vieta jumping** (minimal counterexample + infinite descent
along a hyperbola). Solved as a *version-matched verbatim port* of Mathlib's
`Archive/Imo/Imo1988Q6.lean` — the Archive is CI-gated against our pinned Mathlib (Lean
v4.33.1) but lives in a separate Lake lib target, so it is not importable; the
`constant_descent_vieta_jumping` infrastructure lemma and the application were copied into the
module (only adaptation: file-scope `attribute [local simp] sq` + a nested namespace).

Ceiling-test target for the trajectory DEPTH loop (`proof-strategist` plan → `lean-prover`
port → `proof-auditor`). Outcome: a **recognition win** — search-first surfaced the canonical
proof; no Opus escalation needed. Axioms: `{propext, Classical.choice, Quot.sound}`.

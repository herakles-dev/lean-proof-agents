# Lean, for a newcomer — a primer

A short mental model for what's happening in this repo. Grounded in our own proofs.

## The one idea

**A proof is a value the computer checks.** Lean rests on *dependent type theory*, where
**propositions are types and proofs are values of those types**. To prove `P`, you build a value
of type `P`; Lean's tiny trusted **kernel** verifies the construction. If it type-checks, it's
correct — that's why here **Lean is the sole proof authority**.

## `sorry` and axioms

`sorry` means "trust me" — it makes *anything* type-check, so it's a cheat. Two guards:
- `scripts/check-proof.sh <mod> [thm]` fails on any `sorry`.
- `#print axioms thm` lists hidden dependencies. A real proof shows only
  `[propext, Classical.choice, Quot.sound]` (Lean's standard logic). `sorryAx` = a cheat.

## Two ways to write a proof

```lean
-- term mode: give Lean the finished value
theorem sqrt_two_irrational : Irrational (Real.sqrt 2) := irrational_sqrt_two

-- tactic mode: build it step by step after `by`
theorem gauss_sum (n : ℕ) : (∑ i ∈ range (n+1), i) * 2 = n * (n+1) := by
  induction n with
  | zero => simp
  | succ k ih => rw [sum_range_succ, add_mul, ih]; ring
```

`by` enters **tactic mode**: you manipulate a **goal state** (`hypotheses ⊢ goal`) with **tactics**
until nothing is left. In `gauss_sum`: `induction` splits into base + step; `simp` clears the base;
`rw` rewrites by known equations (including the induction hypothesis `ih`); `ring` finishes the
algebra.

## The workhorse tactics (each is a mini prover)

| Tactic | Closes |
|---|---|
| `ring` | polynomial/ring equalities |
| `omega` | linear arithmetic over ℕ/ℤ |
| `nlinarith` / `linarith` | (non)linear inequalities over ℝ/ℚ — feed hints like `sq_nonneg (a-b)` |
| `simp` | simplify with the library's marked lemmas |
| `induction n with \| zero => \| succ k ih =>` | natural-number induction |
| `exact` / `apply` / `intro` / `obtain` | give a term / apply a lemma / introduce / destructure |

## Mathlib is the secret weapon

Mathlib is a very large library (over a million lines) of already-proven theorems. So proving is mostly **search**:
"does the lemma exist?" Our tools answer that:
- `scripts/mathlib-search.sh "<name>"` — search by name (loogle + local grep).
- `scripts/lean-suggest.sh "<binders> : <goal>"` — Lean's own `exact?`/`apply?` by goal.

Find the lemma, then glue. See `.claude/skills/prove` for the full loop and `PROOF_PATTERNS.md` for
recurring goal→tactic recipes.

## Where to look next

- Lean 4 + Mathlib docs: <https://leanprover-community.github.io/>
- Mathlib search (web): <https://leanprover-community.github.io/mathlib4_docs/> and loogle.
- Our worked examples: `MathProof/Challenges/C0001…` (read them top to bottom).

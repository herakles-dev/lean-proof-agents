# Challenge 0038 — Erdos 493 Product Minus Sum

- **Module:** `MathProof/Challenges/C0038Erdos493ProductMinusSum.lean`
- **Theorem:** `MathProof.Challenges.C0038Erdos493ProductMinusSum.erdos_493`
- **Status:** ✅ SOLVED (axioms: propext, Classical.choice, Quot.sound)

## Problem

Erdős Problem #493: does there exist a `k` such that every sufficiently large integer `n` can
be written as `(∏_{i=1}^k a_i) - (∑_{i=1}^k a_i)` for some integers `a_i ≥ 2`? Erdős attributes
the question to Schinzel. Eli Seamans observed that the answer is **yes**, with `k = 2`, for a
very simple reason: `n = 2·(n+2) - (2 + (n+2))`.

**Source:** google-deepmind/formal-conjectures, `ErdosProblems/493.lean`, theorem `erdos_493`,
tagged `@[category research solved, AMS 11]` with a `sorry` body upstream when this was written (September 2026), i.e. a
formalization gap for a result tagged as solved. Statement reproduced verbatim (upstream's
`answer(·)` elaborator is shimmed locally, since for a `Prop` argument it elaborates to that
proposition, i.e. `answer(True) ≡ True`). NOTE: an external proof exists at `plby/lean-proofs`
(v4.29.1), referenced upstream via `formal_proof using lean4`; this is an independent v4.33.1
formalization.

## Formal statement

```lean
theorem erdos_493 : answer(True) ↔
    ∃ k : ℕ, ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      ∃ a : Fin k → ℤ,
        (∀ i : Fin k, (2 : ℤ) ≤ a i) ∧
        (∏ i : Fin k, a i) - (∑ i : Fin k, a i) = n
```

## Proof sketch

The reverse direction `(∃ …) → answer(True)` is `trivial`. Forward direction: take `k = 2`,
`N = 0`, and for each `n ≥ 0` the pair `a = ![2, n + 2] : Fin 2 → ℤ`:

- `∀ i, 2 ≤ a i`: `a 0 = 2`; `a 1 = n + 2 ≥ 2` since `n ≥ 0` (`fin_cases i <;> simp_all`).
- `(∏ i, a i) - (∑ i, a i) = n`: unfold via `Fin.prod_univ_two`/`Fin.sum_univ_two`, then `ring`
  reduces `2 * (n + 2) - (2 + (n + 2))` to `n`.

Verify: `scripts/check-proof.sh C0038Erdos493ProductMinusSum erdos_493`.

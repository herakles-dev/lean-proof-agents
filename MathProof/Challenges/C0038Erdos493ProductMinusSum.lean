import MathProof.Basic

/-!
# Challenge C0038Erdos493ProductMinusSum — Erdős 493 (product-minus-sum representation)

**Status:** ✅ SOLVED (axioms: propext, Classical.choice, Quot.sound).

**Source:** google-deepmind/formal-conjectures, `ErdosProblems/493.lean`, theorem `erdos_493`,
tagged `@[category research solved, AMS 11]` with a `sorry` body (a genuine formalization gap —
a KNOWN-true Erdős result whose proof is not yet formalized in that repo). Toolchain there is
Lean v4.33.1 = ours. Statement reproduced **verbatim** (imports adapted to `MathProof.Basic`;
upstream's `answer(·)` elaborator is shimmed below since it elaborates a `Prop` argument to
itself, so `answer(True) ≡ True`). NOTE: an external proof exists at `plby/lean-proofs`
(v4.29.1) referenced upstream via `formal_proof using lean4`; this is an independent v4.33.1
formalization for our corpus.

**Statement.** Does there exist `k` such that every sufficiently large integer `n` can be
written as `(∏ i, a i) - (∑ i, a i)` for some `a : Fin k → ℤ` with every `a i ≥ 2`? Answer: yes.

**Proof idea (Eli Seamans' observation, `k = 2`).** Take `N = 0` and, for `n ≥ 0`, the pair
`a = ![2, n + 2]`. Both coordinates are `≥ 2` (the second since `n ≥ 0`), and
`2 · (n + 2) - (2 + (n + 2)) = n`. The reverse direction of the `↔` is `trivial`.
-/

/-- Shim of formal-conjectures' `answer(·)` elaborator: for a `Prop` argument it elaborates to
that proposition (`answer(True)` ≡ `True`). -/
macro "answer(" t:term ")" : term => `($t)

namespace MathProof.Challenges.C0038Erdos493ProductMinusSum

theorem erdos_493 : answer(True) ↔
    ∃ k : ℕ, ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      ∃ a : Fin k → ℤ,
        (∀ i : Fin k, (2 : ℤ) ≤ a i) ∧
        (∏ i : Fin k, a i) - (∑ i : Fin k, a i) = n := by
  constructor
  · intro _
    refine ⟨2, 0, fun n hn => ⟨![2, n + 2], ?_, ?_⟩⟩
    · intro i
      fin_cases i <;> simp_all
    · simp [Fin.prod_univ_two, Fin.sum_univ_two]
      ring
  · intro _
    trivial

end MathProof.Challenges.C0038Erdos493ProductMinusSum

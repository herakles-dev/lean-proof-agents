# Challenge 0046 — 30 divides n⁵ − n

- **Module:** `MathProof/Challenges/C0046ThirtyDividesNPow5MinusN.lean`
- **Theorem:** `MathProof.Challenges.C0046ThirtyDividesNPow5MinusN.challenge_statement`
- **Status:** ✅ SOLVED
- **Provenance:** `/swarm` (Phase ①, end-to-end run) — shared-blackboard parallel-leaf proof.
- **Gate:** `check-proof --all` ✅ · `verify-all` ✅ (whole-repo regression run) · `proof-auditor` **PASS** (faithful ∀n:ℤ,
  non-vacuous per negative controls; genuine 3-leaf combiner, no circularity; axioms ⊆
  {propext, Classical.choice, Quot.sound}).

## Problem

Show that for every integer `n`, the number `n⁵ − n` is divisible by `30`.

This is the classic independent-leaf theorem: `30 = 2 · 3 · 5` with `2, 3, 5` pairwise coprime,
and `n⁵ ≡ n` modulo each of `2, 3, 5` (Fermat's little theorem for the primes `2, 3, 5`). So the
proof splits into **three independent modular leaves** that combine by coprimality — exactly the
DAG shape `/swarm` parallelizes.

Truth-gated offline (`n⁵ − n mod 30`, n = −7…12): all `0`.

## Formal statement

```lean
theorem challenge_statement (n : ℤ) : (30 : ℤ) ∣ n ^ 5 - n
```

## Proof structure (swarm DAG)

| Subgoal | Leaf | Statement | Deps |
|---|---|---|---|
| sg1 | `dvd_two`   | `(2 : ℤ) ∣ n^5 - n`  | ∅ (independent) |
| sg2 | `dvd_three` | `(3 : ℤ) ∣ n^5 - n`  | ∅ (independent) |
| sg3 | `dvd_five`  | `(5 : ℤ) ∣ n^5 - n`  | ∅ (independent) |
| sg4 | `challenge_statement` | `(30 : ℤ) ∣ n^5 - n` | sg1, sg2, sg3 (combiner) |

Wave 1 = {sg1, sg2, sg3} proven in parallel by three `lean-prover`s (each owning its own bank
file); Wave 2 = sg4 combines them by pairwise coprimality (`IsCoprime.mul_dvd`, `30 = 2·3·5`).

Each modular leaf: `ZMod.intCast_zmod_eq_zero_iff_dvd (n^5 - n) k` reduces `k ∣ n^5 - n` to
`∀ m : ZMod k, m^5 - m = 0`, closed by `decide` (finite, kernel-clean — **no** `native_decide`).

## Notes

Wolfram/OEIS are scratchpads only. Lean's kernel is the sole arbiter: SOLVED only when
`scripts/check-proof.sh C0046ThirtyDividesNPow5MinusN --all` is green (no `sorry`, axioms ⊆
{propext, Classical.choice, Quot.sound}).

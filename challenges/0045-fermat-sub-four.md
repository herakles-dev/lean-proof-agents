# Challenge 0045 — Fermat's right-triangle theorem, quartic `−` form (`x⁴ − y⁴ = z²`)

- **Module:** `MathProof/Challenges/C0045FermatSubFour.lean`
- **Theorems:** `fermat_sub_four`, `no_nontrivial_fermat_sub_four`
- **Status:** ✅ SOLVED — `sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`
  (`scripts/check-proof.sh C0045FermatSubFour --all`).

## Problem

**Fermat's right-triangle theorem** (no Pythagorean triangle has square area), in its explicit
quartic form. The `−` mirror of Mathlib's `not_fermat_42` (`a⁴ + b⁴ ≠ c²`,
`Mathlib/NumberTheory/FLT/Four.lean`) — not present in Mathlib at the pinned toolchain, to the author's knowledge. Together with C0043's
`no_four_squares_in_ap` it completes the right-triangle theorem family.

**Faithful statement (anti-vacuity).** The naive `a⁴ − b⁴ ≠ c²` is *false* — the trivial family
`a = ±b, c = 0` satisfies it. The real content: for nonzero `a, b`, `a⁴ − b⁴ = c²` forces `c = 0`.
Self-audited: no nontrivial `(a,b,c)` with `1 ≤ b < a ≤ 80` (`#eval` brute search, empty).

## Formal statement

```lean
theorem fermat_sub_four (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (h : a ^ 4 - b ^ 4 = c ^ 2) : c = 0

theorem no_nontrivial_fermat_sub_four :
    ¬ ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ^ 4 - b ^ 4 = c ^ 2
```

## Proof

Infinite descent, a structural clone of `Fermat42.not_minimal` with `+ → −`. `a⁴ − b⁴ = c²`
⟹ `c² + (b²)² = (a²)²`, a Pythagorean triple. Take a minimal counterexample (least `a.natAbs`); it
is coprime. Classify via `PythagoreanTriple.coprime_classification'`; the parity of `b` gives two
forks, each producing a strictly smaller solution of the *same* equation:
- `c` even: one Pythagorean step.
- `c` odd: two steps + a four-way square split (`Int.sq_of_gcd_eq_one` on pairwise-coprime factors
  `r · s · (r²−s²)`), yielding `i⁴ − j⁴ = ±k²` with smaller `a.natAbs`.
Minimality is contradicted, so no nontrivial solution exists.

## Verification note

check-proof `--all` clean (trusted trio); **proof-auditor PASS** (2026-09-16, line-by-line:
statement fidelity + anti-vacuity + descent integrity cross-checked against Mathlib's
`coprime_classification'` / `Int.sq_of_gcd_eq_one` / `Fermat42.not_minimal`; no `native_decide`, no
circular/omega-laundered contradiction); fidelity self-audit (no nontrivial solution, brute force
`|a|,|b| ≤ 60–80`). A pull request to Mathlib has not been opened.

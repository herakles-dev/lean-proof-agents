# Challenge 0043 — Fermat: no four squares in arithmetic progression (1640)

- **Note:** the file name says "right-triangle theorem", but the theorems proved here are `no_four_squares_in_ap` and `four_squares_not_in_ap`; the `x⁴ − y⁴ = z²` form is challenge 0045.
- **Module:** `MathProof/Challenges/C0043FermatRightTriangleTheorem.lean`
- **Theorems:** `no_four_squares_in_ap`, `four_squares_not_in_ap` (AP-form wrapper)
- **Status:** ✅ SOLVED — `sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`
  (`scripts/check-proof.sh C0043FermatRightTriangleTheorem --all`).

## Problem

Prove **Fermat's theorem of 1640**: four perfect squares can never form a *nonconstant*
arithmetic progression. Equivalently, this is Fermat's *right-triangle theorem* (no Pythagorean
triangle has square area) and the congruent-number-1 obstruction.

To the author's knowledge, as of September 2026, this is a **Mathlib gap** (a Mathlib-PR candidate): at the pinned toolchain Mathlib has
no four-squares-in-AP theorem, no `x⁴ − y⁴ ≠ z²` right-triangle theorem, and no congruent-number
theorem. The only nearby result is `not_fermat_42` (`a⁴ + b⁴ ≠ c²`,
`Mathlib/NumberTheory/FLT/Four.lean`) — the *parallel* `+`-descent, not reachable from this one by a
short algebraic identity.

## Formal statement

```lean
-- key theorem (equations form)
theorem no_four_squares_in_ap (r s t u D : ℤ) (hD : D ≠ 0)
    (h1 : s ^ 2 = r ^ 2 + D) (h2 : t ^ 2 = s ^ 2 + D) (h3 : u ^ 2 = t ^ 2 + D) : False

-- clean user-facing AP-form wrapper
theorem four_squares_not_in_ap (a b c d : ℤ)
    (hab : b ^ 2 - a ^ 2 = c ^ 2 - b ^ 2) (hbc : c ^ 2 - b ^ 2 = d ^ 2 - c ^ 2)
    (hne : a ^ 2 ≠ b ^ 2) : False
```

## Provenance & scope

The proof is the self-contained descent chain extracted **verbatim** from `C0040`
(Erdős #672 / Euler), where it was developed and adversarially audited. Extraction is a pure lift
of the transitive closure of `no_four_squares_in_ap` (17 declarations); all Erdős-specific
machinery (`ap4_prod_ne_sq*`, `sg7*`, `concordant_forms_*`) is intentionally dropped so the module
is a minimal, upstream-portable unit.

**Proof engine:** the primitive Euler concordant-`(1,4)` descent — two equal-area Pythagorean
triangles → four-number factorisation `P·Q = P'·Q'` → concordant pair `X²+Y²=□ ∧ X²+4Y²=□` →
infinite descent on `|X|·|Y|` (residual cofactor `k ∣ 3` killed mod 3).

## Right-triangle form (see challenge 0045)

The explicit right-triangle form `x⁴ − y⁴ ≠ z²` is **equivalent** but *not* a `ring`-identity
corollary: a solution yields only three squares in AP (the Pythagorean triple `(y², z, x²)`);
producing the fourth is itself a Fermat descent step. It is proved separately in challenge 0045
(`fermat_sub_four`).

## Notes

Truth-gated offline before formalizing (`scripts/lean-eval.sh`): `x⁴ − y⁴ = z²` has no positive
solution for `1 ≤ y < x ≤ 120`; four squares in nonconstant AP have no hit for base roots `≤ 60`.
Wolfram is a scratchpad only — Lean's kernel is the sole arbiter.

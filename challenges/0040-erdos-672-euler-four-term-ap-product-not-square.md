# Challenge 0040 — Erdős #672 (Euler): four-term AP product is never a square

- **Module:** `MathProof/Challenges/C0040Erdos672EulerFourTermAPProductNotSquare.lean`
- **Theorems:** `ap4_prod_ne_sq` (full theorem, PROVEN), `ap4_prod_ne_sq_d_eq_one`, `ap4_prod_ne_sq_d_ge_two`, and the descent kernels `no_four_squares_in_ap` / `four_squares_ap_descent` / `four_squares_ap_descent_step_primitive` — all PROVEN.
- **Status:** ✅ SOLVED — `sorry`-free, clean axioms (`#print axioms ap4_prod_ne_sq` =
  `[propext, Classical.choice, Quot.sound]`; `scripts/check-proof.sh C0040… --all` → SOLVED).
  Closed end-to-end by a multi-agent DEPTH loop (strategist plan → normalization → parallel
  Pythagorean/Gaussian provers → a final descent step by the strongest prover model used here).

## Problem

Euler's theorem (the number-theoretic core of Erdős problem #672): the product of four terms
of an arithmetic progression of positive integers with coprime common difference is never a
perfect square. Formally, for `n, d > 0` with `gcd(n, d) = 1`:

```
n * (n + d) * (n + 2*d) * (n + 3*d) ≠ q^2   for all q.
```

(The full `Erdos672With 4 2` statement wraps this ℕ core fact in Finset/ENat plumbing — a
separate, later step; this module isolates the arithmetic heart only.)

## Formal statement

```lean
theorem ap4_prod_ne_sq (n d q : ℕ) (hn : 0 < n) (hd : 0 < d) (hcop : n.gcd d = 1) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) ≠ q ^ 2
```

split as:

```lean
theorem ap4_prod_ne_sq_d_eq_one (n q : ℕ) (hn : 0 < n) :
    n * (n + 1) * (n + 1 + 1) * (n + 1 + 1 + 1) ≠ q ^ 2

theorem ap4_prod_ne_sq_d_ge_two (n d q : ℕ) (hn : 0 < n) (hd : 2 ≤ d) (hcop : n.gcd d = 1) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) ≠ q ^ 2
```

## Proof sketch

**`d = 1` (PROVEN, no `sorry`, axioms = `[propext, Classical.choice, Quot.sound]`).**
`n(n+1)(n+2)(n+3) + 1 = (n²+3n+1)²` is a pure `ring` identity (no subtraction needed, since
`d⁴ = 1`). Writing `x = n²+3n+1` and assuming the product equals `q²`, we get `q² + 1 = x²`
with `x ≥ 5`. Then `q < x` (from `q² < x²` via `Nat.pow_le_pow_left`), so `q + 1 ≤ x`, so
`(q+1)² ≤ x² = q² + 1`, forcing `q = 0` and hence `x² = 1`, contradicting `x ≥ 5`. Closed by
`nlinarith` after the two `Nat.pow_le_pow_left` steps.

**`d ≥ 2` (PROVEN — the real descent crux).** Anchor identity `P + d⁴ = x²`,
`x = n² + 3nd + d²`; `gcd(x,d)=1` from `gcd(n,d)=1`, and `P=q²` gives `(x−q)(x+q)=d⁴` in `ℤ`.
Split on parity of `d`:
- **odd `d`** (`sg7d_descent_core`): `x−q, x+q` odd & coprime ⇒ each a 4th power ⇒ algebra bridge
  `(f²−e²)² = 2n(n+3d)` ⇒ `concordant_forms_core`.
- **even `d`** (`sg7e_even_branch`): `x` odd ⇒ `x±d²` coprime odd squares ⇒ 4-term AP of squares
  or a concordant system ⇒ `no_four_squares_in_ap` / `concordant_forms_core`.

Both bottom out at **`no_four_squares_in_ap`** — Fermat's "no four squares in arithmetic
progression" (1640). Mathlib has **no** anchor for it (no four-squares-in-AP, no `x⁴−y⁴=z²`
right-triangle theorem, no congruent-number theorem; `not_fermat_42` is the parallel `+`-descent,
not a usable reduction), so it is proved **from scratch**:

1. sign trichotomy + `natAbs` normalization ⇒ the clean case `four_squares_ap_descent`
   (`0<r<s<t<u`, `r²+t²=2s²`, `s²+u²=2t²`);
2. strong induction on `u.natAbs` over a descent step; non-primitive case divides out the common
   gcd; the **primitive core** `four_squares_ap_descent_step_primitive` is closed by an Euler
   concordant-forms descent: halve to two **equal-area** Pythagorean triangles → Euler four-number
   factorisation `P·Q = P'·Q'` → the `(1,4)` concordant form (`X²+Y²=□`, `X²+4Y²=□`) → infinite
   descent on `|X|·|Y|` via `PythagoreanTriple.coprime_classification'` (twice), residual cofactor
   `k∣3` killed mod 3.

Note **equal-area ≠ square-area**, so this is *strictly harder* than Fermat's right-triangle
descent — no single square-extraction shortcut. Comparable in depth to `not_fermat_42` (Beeger 1917 / Mordell, *Diophantine
Equations* ch. 4). **`no_four_squares_in_ap` is a genuine Mathlib gap → a candidate Mathlib PR.**

## Notes

Explored via the strategist's anchor identity (verified by `ring`) and a brute-force truth-gate
(no 4-square AP with roots ≤ 20000); no Wolfram/OEIS lookup needed — this is Euler's classical
theorem. Solved by a multi-agent DEPTH loop: `proof-strategist` plan + ledger (not committed),
`lean-prover-opus` normalization, parallel Pythagorean + Gaussian provers (which converged on the
2-var kernel and caught the equal-area≠square-area subtlety), and a final prover using the strongest model tier for
the final descent. Reusable recipes logged to `PROOF_PATTERNS.md`.

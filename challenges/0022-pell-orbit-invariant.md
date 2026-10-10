# Challenge 0022 — Pell Orbit Invariant

- **Module:** `MathProof/Challenges/C0022PellOrbitInvariant.lean`
- **Theorem:** `MathProof.Challenges.C0022PellOrbitInvariant.orbit_ne`
- **Status:** ✅ SOLVED

## Problem

Let $f(x,y) = (3x+4y,\ 2x+3y)$ on $\mathbb{Z}^2$. Starting from $(3,2)$, show the orbit under $f$
never reaches $(1,1)$:

$$\forall n,\quad f^{[n]}(3,2) \ne (1,1).$$

## Formal statement

```lean
def f (p : ℤ × ℤ) : ℤ × ℤ := (3 * p.1 + 4 * p.2, 2 * p.1 + 3 * p.2)

theorem orbit_ne (n : ℕ) : f^[n] (3, 2) ≠ (1, 1)
```

## Notes

- **An INVARIANT argument.** Direct induction on `n` gets no grip: the hypothesis `f^[n](3,2) ≠ (1,1)`
  says nothing about `f^[n+1]`, because `f` has *another* preimage of `(1,1)` — namely `(-1,1)`
  (`f(-1,1) = (1,1)`). You must find the conserved quantity.
- **The invariant:** `Q(x,y) = x² − 2y²` (the Pell form; `f` is the matrix `[[3,4],[2,3]]` of
  determinant 1, so it preserves `x²−2y²`). Then `Q(f p) = Q p` (a `ring` identity), `Q(f^[n](3,2)) = 1`
  for all `n` (induction), while `Q(1,1) = 1 − 2 = −1 ≠ 1` — so `(1,1)` is off the orbit's level set.
- Truth-gated: `Q` = 1 for iterates n=0..10; `Q(1,1) = −1`.
- **Solved via the DEPTH loop — the keeper's INVARIANT-SEARCH rung.** Naive prover BLOCKED (found the
  `(-1,1)` counterexample) → `stall-check` STALL → `proof-trajectory-keeper` returned **INVARIANT-SEARCH**
  with the conserved quantity → re-planned → SOLVED. This used a different keeper rung from C0021's
  GENERALIZE. The ledger is not committed to this repo.

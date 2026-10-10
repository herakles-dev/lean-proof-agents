# Challenge 0036 — Finite Krein–Milman (hull = hull of extreme points)

- **Module:** `MathProof/Challenges/C0036FiniteKreinMilmanHullExtremePoints.lean`
- **Theorem:** `MathProof.Challenges.C0036FiniteKreinMilmanHullExtremePoints.finite_convexHull_eq_convexHull_extremePoints`
- **Status:** ✅ SOLVED (axioms: `propext, Classical.choice, Quot.sound`)
- **Source:** INFRA-LEMMA spun out of C0031 (Putnam 1962 A1, "Happy Ending"). Not a competition
  problem — a reusable Mathlib-gap-adjacent lemma the `E.ncard ≤ 3` case of C0031 needs.

## Problem

For a **finite** point set `S ⊆ ℝ²`, the convex hull of `S` equals the convex hull of the extreme
points of that hull. (Every point of `S` — in particular the non-vertices — lies in the convex hull
of the hull's vertices.) Mathlib supplies Krein–Milman only up to a `closure`; the finiteness makes
the closure removable.

## Formal statement

```lean
theorem finite_convexHull_eq_convexHull_extremePoints
    (S : Set (ℝ × ℝ)) (hS : S.Finite) :
    convexHull ℝ S = convexHull ℝ ((convexHull ℝ S).extremePoints ℝ)
```

## Proof

Let `E' := (convexHull ℝ S).extremePoints ℝ`. By `extremePoints_convexHull_subset`, `E' ⊆ S`, so
`E'` is finite (`hS.subset`); hence `convexHull ℝ E'` is closed (`Set.Finite.isClosed_convexHull`,
as `ℝ × ℝ` is `T2Space`). Krein–Milman (`closure_convexHull_extremePoints`) on the compact
(`Set.Finite.isCompact_convexHull`) convex (`convex_convexHull`) set `convexHull ℝ S` gives
`closure (convexHull ℝ E') = convexHull ℝ S`; rewriting the closure by `IsClosed.closure_eq`
collapses it to `convexHull ℝ E' = convexHull ℝ S`.

## Notes

- The key finding: the "finite Krein–Milman" lemma a first prover attempt reported as *missing from Mathlib*
  is a ~5-line assembly of existing anchors once the closure-removal (finite ⇒ closed hull) is seen.
  A lemma search before proving dissolved the reported obstacle.
- Feeds the `E.ncard ≤ 3` case of C0031 (the two non-extreme points land in the hull of the ≤3
  extreme points, i.e. the same triangle).

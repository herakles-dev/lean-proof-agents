import MathProof.Basic

/-!
# Challenge C0036FiniteKreinMilmanHullExtremePoints — finite Krein–Milman (hull = hull of extreme points)

**Status:** ✅ SOLVED — INFRA-LEMMA spun out of C0031 (Putnam 1962 A1, the "Happy Ending" problem).

The `E.ncard ≤ 3` case of C0031 needs: for a **finite** point set, its convex hull equals the convex
hull of its own extreme points — so the non-extreme points lie inside the hull of the extreme ones.
Mathlib supplies Krein–Milman only up to a `closure` (`closure_convexHull_extremePoints`); for a
finite set the closure is removable, because the extreme points are finite and so their convex hull
is already closed.

**Anchors (verified in-tree):**
- `closure_convexHull_extremePoints (hscomp : IsCompact s) (hAconv : Convex ℝ s) :
   closure (convexHull ℝ (s.extremePoints ℝ)) = s` (Krein–Milman)
- `extremePoints_convexHull_subset : (convexHull 𝕜 A).extremePoints 𝕜 ⊆ A`
- `Set.Finite.isCompact_convexHull : s.Finite → IsCompact (convexHull ℝ s)`
- `Set.Finite.isClosed_convexHull [T2Space E] : s.Finite → IsClosed (convexHull ℝ s)`
- `convex_convexHull`, `Set.Finite.subset`, `IsClosed.closure_eq`

**Sketch:** let `E' := (convexHull ℝ S).extremePoints ℝ`. Then `E' ⊆ S` (`extremePoints_convexHull_subset`)
so `E'` is finite, hence `convexHull ℝ E'` is closed. Krein–Milman on the compact convex `convexHull ℝ S`
gives `closure (convexHull ℝ E') = convexHull ℝ S`; since `convexHull ℝ E'` is closed, its closure is
itself, so `convexHull ℝ E' = convexHull ℝ S`.
-/

namespace MathProof.Challenges.C0036FiniteKreinMilmanHullExtremePoints

open Set

theorem finite_convexHull_eq_convexHull_extremePoints
    (S : Set (ℝ × ℝ)) (hS : S.Finite) :
    convexHull ℝ S = convexHull ℝ ((convexHull ℝ S).extremePoints ℝ) := by
  -- The extreme points of the hull lie inside `S`, hence form a finite set.
  have hE'fin : ((convexHull ℝ S).extremePoints ℝ).Finite :=
    hS.subset extremePoints_convexHull_subset
  -- Krein–Milman on the compact convex hull: closure of hull-of-extreme-points is the hull.
  have hkm : closure (convexHull ℝ ((convexHull ℝ S).extremePoints ℝ)) = convexHull ℝ S :=
    closure_convexHull_extremePoints (hS.isCompact_convexHull ℝ) (convex_convexHull ℝ S)
  -- The hull of a finite set is closed (ℝ × ℝ is T2), so its closure is itself.
  rw [(hE'fin.isClosed_convexHull ℝ).closure_eq] at hkm
  exact hkm.symm

end MathProof.Challenges.C0036FiniteKreinMilmanHullExtremePoints

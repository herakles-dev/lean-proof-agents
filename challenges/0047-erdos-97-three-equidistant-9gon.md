# Challenge 0047 — Erdős #97 (Danzer variant): a convex 9-gon with the 3-equidistant property

- **Module:** `MathProof/Challenges/C0047Erdos97ThreeEquidistant9gon.lean`
- **Theorem:** `MathProof.Challenges.C0047Erdos97ThreeEquidistant9gon.erdos_97_variants_three_equidistant`
- **Status:** ✅ SOLVED (no `sorry`; axioms `[propext, Classical.choice, Quot.sound]`)
- **Upstream target:** `erdos_97.variants.three_equidistant` in
  `google-deepmind/formal-conjectures` (`FormalConjectures/ErdosProblems/97.lean`; `sorry` there when this was written, September 2026).

## Problem

[Erdős #97](https://www.erdosproblems.com/97) originally conjectured that every convex polygon has a
vertex with no 3 other vertices equidistant from it. **Danzer disproved this** with an explicit
convex polygon on 9 points in which *every* vertex has (at least) three other vertices equidistant
from it — the common distance may differ from vertex to vertex.

## Formal statement

```lean
theorem erdos_97_variants_three_equidistant :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
      A.Nonempty ∧ ConvexIndep A ∧ HasNEquidistantProperty 3 A
```

with the upstream definitions replicated verbatim (`ℝ² = EuclideanSpace ℝ (Fin 2)`;
`ConvexIndep S := ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})`;
`HasNEquidistantProperty n A := ∀ p ∈ A, ∃ r > 0, (A.filter (dist p · = r)).card ≥ n`).
The witness `danzer9` is Danzer's explicit 9 points (verbatim from the upstream file).

## How it was proved — `/swarm` (Phase ②)

Proven by the shared-blackboard proof swarm on a `proof-strategist` DAG:
`Witness → { Nonempty, ConvexIndep, Equidistant } → Main`.

- **`ConvexIndep` (the hard crux)** was closed by **Phase ② best-of-N crux racing** — 3 provers ran
  diverse strategies in parallel; the winner (an explicit separating linear functional per point,
  `uᵢ = !₂[w₁·√3, 3·w₂]`, so `⟪uᵢ,·⟫` is pure-rational since `√3·√3=3`, giving a strict supporting
  functional at each vertex via `convex_halfSpace_lt` + `convexHull_min`) was the first kernel-clean
  candidate; the losers were cancelled.
- **`Equidistant`** — for each of the 9 points, its 3 equidistant peers verified via the fact that
  every pairwise *squared* distance is rational (`EuclideanSpace.dist_eq` → `(Δx)²+(Δy)²=r²`,
  `nlinarith`).
- The three leaves were proven in parallel on the shared bank, then `bank.sh assemble`'d
  (topological order) into this self-contained module and kernel-gated (`check-proof --all` +
  `proof-auditor` + `verify-all`).

## Notes

Structural facts (exact-arithmetic verified by `proof-strategist`): the 9 points lie on three
concentric circles centred at the origin (radii² = 4, 259428/10927, 379164/18529), all are convex-hull
vertices, and each has exactly 3 equidistant peers. To port upstream: the proof term drops into
`formal-conjectures`'s `97.lean` in place of the `sorry` on `erdos_97.variants.three_equidistant`
(their file already provides `ConvexIndep` and the `HasNEquidistant*` defs).

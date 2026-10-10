import MathProof.Certify.Sup
import MathProof.Certify.Graph
import MathProof.Certify.Finset
import MathProof.Certify.Reflect

/-!
# MathProof.Certify — the witness→Lean-certificate bridge lemmas (the moat)

v1 (decide-a-Finset-scan bridges): `Certify.Sup` (finite-`iSup` scan bridges, #647),
`Certify.Graph` (trail/cycle decidability infra, #64), `Certify.Finset` (`Set`/`Finset`
quantifier bridge, #128).

v2 (proof by reflection): `Certify.Reflect` — Bool checkers over `Nat` + a soundness theorem each,
run under `decide +kernel` with GMP-accelerated `Nat` arithmetic instead of unfolding
`Finset`/`Multiset`. The τ-sweep (`tauS`/`tauS_eq` + `sweepS`/`sweepS_sound`) certifies #647's
no-witness fact ~50× further than v1 (N=3000 vs N≈60). See the header of `Certify/Reflect.lean`.

Still deferred: `Certify.Graph.no_pow2_cycle_of_forall_len` (the #64 DFS checker needs a v2 graph
reflection checker AND far more compute — search starts above 58 vertices).

**Never `native_decide`. Never widen `TRUSTED_AXIOMS`.** Every lemma here must depend only on
`propext`, `Classical.choice`, `Quot.sound` — a solver witness is only as trustworthy as the
kernel proof that checks it, and `native_decide` (or a stray `axiom`) breaks that chain.
-/

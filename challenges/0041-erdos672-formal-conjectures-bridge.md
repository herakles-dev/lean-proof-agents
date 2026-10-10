# Challenge 0041 — Erdős #672 (Euler variant): bridge to the `formal-conjectures` statement

- **Module:** `MathProof/Challenges/C0041Erdos672FormalConjecturesBridge.lean`
- **Theorem:** `erdos_672_variants_euler : Erdos672With 4 2`
- **Status:** ✅ SOLVED — `sorry`-free, clean axioms (`[propext, Classical.choice, Quot.sound]`).

## Problem

`google-deepmind/formal-conjectures` states Erdős #672 in `FormalConjectures/ErdosProblems/672.lean`.
Its Euler variant — `erdos_672.variants.euler : Erdos672With 4 2` — was `sorry` there when this was written (September 2026; the author did not re-check later). This
challenge closes it: the product of a **4-term arithmetic progression of positive integers with
coprime common difference** is never a perfect square, phrased against their abstract
`Set.IsAPOfLengthWith` AP predicate over a `Finset ℕ`.

## Formal statement

```lean
-- replicated verbatim from formal-conjectures (same Mathlib v4.33.1 pin)
def Set.IsAPOfLengthWith {α} [AddCommMonoid α] (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

def Erdos672With (k l : ℕ) : Prop :=
  ∀ (s : Finset ℕ), s.card = k → ∀ᵉ (n > 0) (d > 0), n.gcd d = 1 →
    Set.IsAPOfLengthWith s k n d → ∀ q, ∏ i ∈ s, i ≠ q ^ l

theorem erdos_672_variants_euler : Erdos672With 4 2
```

## Proof sketch

Bridge from the abstract AP predicate to the concrete product, then invoke C0040:
1. `Set.IsAPOfLengthWith ↑s 4 n d` gives `↑s = {n + m•d | m < (4:ℕ∞)}`; unfold (`m < 4` after the
   `ℕ→ℕ∞` cast, `interval_cases m`) to the explicit set `{n, n+d, n+2d, n+3d}`.
2. Transfer the set equality to the `Finset` via `Finset.coe_injective`.
3. `∏ i ∈ {n, n+d, n+2d, n+3d}, i = n*(n+d)*(n+2d)*(n+3d)` (`Finset.prod_insert`; the four terms are
   distinct because `d > 0`, by `omega`).
4. Apply the certified `ap4_prod_ne_sq` (C0040 — Euler / Erdős #672, full Fermat descent).

## Notes

**Transfer to `formal-conjectures`:** the `Set.IsAPOfLengthWith` / `Erdos672With` definitions here
are copied verbatim from upstream (identical Lean/Mathlib pin), so the proof term of
`erdos_672_variants_euler` drops directly into their `672.lean` in place of the `sorry`. The only
non-Mathlib dependency is `ap4_prod_ne_sq`, so the real PR contributes the C0040 descent + this
bridge together. Upstream status: formal-conjectures
[PR #5481](https://github.com/google-deepmind/formal-conjectures/pull/5481) (merged 2026-09-18)
links the externally published proof (challenges 0040 + 0041,
<https://github.com/herakles-dev/erdos672-four-squares-lean>) from `erdos_672.variants.euler`; the proof itself is not inside formal-conjectures.

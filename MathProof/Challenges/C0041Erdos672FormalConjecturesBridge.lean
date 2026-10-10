import MathProof.Basic
import MathProof.Challenges.C0040Erdos672EulerFourTermAPProductNotSquare

/-!
# Challenge C0041 — Erdős #672 (Euler variant): bridge to the `formal-conjectures` statement

This proves **`Erdos672With 4 2`** — verbatim the target of
`google-deepmind/formal-conjectures`'s `FormalConjectures/ErdosProblems/672.lean`, lemma
`erdos_672.variants.euler` (currently `sorry` there) — by reducing it to our certified
`ap4_prod_ne_sq` (C0040). This closes the "Finset/ENat plumbing" C0040 deferred: turning the
abstract `Set.IsAPOfLengthWith` AP predicate into the concrete product `n(n+d)(n+2d)(n+3d)`.

The two upstream definitions are **replicated verbatim** below (same Mathlib pin, Lean v4.33.1 /
mathlib rev `0df444a…`, so lemma names transfer with zero skew). To land this in
`formal-conjectures`, drop the proof of `erdos_672_variants_euler` into their `672.lean` in place
of the `sorry` on `erdos_672.variants.euler` — their file already provides `Erdos672With` and
`Set.IsAPOfLengthWith`, so only the proof term is needed there.

Verify: `scripts/check-proof.sh C0041Erdos672FormalConjecturesBridge erdos_672_variants_euler`
-/

namespace MathProof.Challenges.C0041Erdos672FormalConjecturesBridge

open MathProof.Challenges.C0040Erdos672EulerFourTermAPProductNotSquare

/-- **Replicated verbatim** from `formal-conjectures`
`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`. A set `s` is an arithmetic progression
of length `l` with first term `a` and difference `d`. -/
def _root_.Set.IsAPOfLengthWith {α : Type*} [AddCommMonoid α] (s : Set α) (l : ℕ∞) (a d : α) :
    Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

/-- **Replicated verbatim** from `formal-conjectures` `FormalConjectures/ErdosProblems/672.lean`. -/
def Erdos672With (k l : ℕ) : Prop :=
  ∀ (s : Finset ℕ), s.card = k → ∀ᵉ (n > 0) (d > 0), n.gcd d = 1 →
    Set.IsAPOfLengthWith s k n d → ∀ q, ∏ i ∈ s, i ≠ q ^ l

/-- **Euler's variant of Erdős #672** (`erdos_672.variants.euler`): the product of a 4-term
arithmetic progression of positive integers with coprime common difference is never a perfect
square. Reduces to `ap4_prod_ne_sq` (C0040) once the `Set.IsAPOfLengthWith` AP predicate is
unfolded to the explicit four-element set `{n, n+d, n+2d, n+3d}`. -/
theorem erdos_672_variants_euler : Erdos672With 4 2 := by
  intro s hcard n hn d hd hcop hAP q
  obtain ⟨-, hset⟩ := hAP
  -- `↑s` equals the explicit four-element set.
  have hcoe : (↑s : Set ℕ) = {n, n + d, n + 2 * d, n + 3 * d} := by
    rw [hset]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨m, hm, rfl⟩
      have hm4 : m < 4 := by exact_mod_cast hm
      interval_cases m <;> simp [smul_eq_mul]
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, by exact_mod_cast (by norm_num : (0 : ℕ) < 4), by simp⟩
      · exact ⟨1, by exact_mod_cast (by norm_num : (1 : ℕ) < 4), by simp [smul_eq_mul]⟩
      · exact ⟨2, by exact_mod_cast (by norm_num : (2 : ℕ) < 4), by simp [smul_eq_mul]⟩
      · exact ⟨3, by exact_mod_cast (by norm_num : (3 : ℕ) < 4), by simp [smul_eq_mul]⟩
  -- Transfer the set equality to a `Finset` equality (coercion is injective).
  have hsfin : s = ({n, n + d, n + 2 * d, n + 3 * d} : Finset ℕ) := by
    apply Finset.coe_injective
    rw [hcoe]
    simp
  -- Compute the product over the explicit (distinct, since `d > 0`) four-element `Finset`.
  have hprod : ∏ i ∈ ({n, n + d, n + 2 * d, n + 3 * d} : Finset ℕ), i
      = n * (n + d) * (n + 2 * d) * (n + 3 * d) := by
    rw [Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
        Finset.prod_insert (by simp; omega), Finset.prod_singleton]
    ring
  rw [hsfin, hprod]
  exact ap4_prod_ne_sq n d q hn hd hcop

end MathProof.Challenges.C0041Erdos672FormalConjecturesBridge

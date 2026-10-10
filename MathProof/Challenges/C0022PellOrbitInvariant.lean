import MathProof.Basic

/-!
# Challenge C0022PellOrbitInvariant — a Pell orbit never hits (1,1)

**Status:** ✅ SOLVED

The map `f(x,y) = (3x+4y, 2x+3y)` preserves the quantity `x² − 2y²` (Pell form). Starting from
`(3,2)` where `3²−2·2² = 1`, every iterate keeps `x²−2y² = 1`; but `(1,1)` has `1²−2·1² = −1`.
So the orbit of `(3,2)` never reaches `(1,1)` — a pure INVARIANT argument (direct induction on the
pair gets no grip; you must find the conserved quantity). Truth-gated: inv = 1 for n=0..10.

Workflow:
1. (optional) explore first:  `scripts/wolfram.sh "<atomic query>"`
2. state the theorem below, keep `sorry` while you work
3. build it:  `lake build MathProof.Challenges.C0022PellOrbitInvariant`
4. verify done (no sorry, clean axioms):  `scripts/check-proof.sh C0022PellOrbitInvariant`

Not imported by `MathProof.lean` until `scripts/new-challenge.sh` copies it.
-/

namespace MathProof.Challenges.C0022PellOrbitInvariant

/-- The Pell orbit map `(x, y) ↦ (3x + 4y, 2x + 3y)` on `ℤ × ℤ`. -/
def f (p : ℤ × ℤ) : ℤ × ℤ := (3 * p.1 + 4 * p.2, 2 * p.1 + 3 * p.2)

/-- The conserved Pell quantity `x² − 2y²`. -/
def Q (p : ℤ × ℤ) : ℤ := p.1 ^ 2 - 2 * p.2 ^ 2

/-- `f` preserves `Q`. -/
theorem step_inv (p : ℤ × ℤ) : Q (f p) = Q p := by
  simp only [Q, f]
  ring

/-- Every iterate of `f` starting from `(3, 2)` has `Q = 1`. -/
theorem orbit_Q (n : ℕ) : Q (f^[n] (3, 2)) = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Function.iterate_succ_apply', step_inv]
    exact ih

/-- Starting from `(3, 2)`, the orbit of `f` never reaches `(1, 1)`. -/
theorem orbit_ne (n : ℕ) : f^[n] (3, 2) ≠ (1, 1) := by
  intro h
  have hQ := orbit_Q n
  rw [h] at hQ
  simp only [Q] at hQ
  omega

end MathProof.Challenges.C0022PellOrbitInvariant

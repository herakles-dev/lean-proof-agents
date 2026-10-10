import Mathlib

/-!
# MathProof.Basic — shared foundation for every challenge

Importing all of `Mathlib` here means each challenge module (which imports
`MathProof.Basic`) has the entire library available with no import hunting.
Builds stay fast because Mathlib is pulled from the prebuilt cache.

Put shared notation, helper lemmas, and custom tactics for the challenge set
inside the `MathProof` namespace below.
-/

namespace MathProof

-- Shared helpers go here. Example scaffold (safe no-op):
/-- Marker used by challenge templates so an unproved statement still elaborates
    while making the `sorry` obvious in `#print axioms`. -/
abbrev Unsolved (p : Prop) : Prop := p

end MathProof

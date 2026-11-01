import Mathlib

/-! Positive controls for `scripts/DuplicateProbe.lean`: two declarations that are
deliberate duplicates, so that a probe reporting "no duplicates" can be distinguished
from a probe that is not working. Not part of any library target. -/

namespace NavierStokes.Planted

/-- Duplicates `plantedB`. -/
theorem plantedA (n : ℕ) : n = n := rfl

/-- Duplicates `plantedA`. -/
theorem plantedB (m : ℕ) : m = m := rfl

/-- Duplicates Mathlib's `Nat.add_comm`. -/
theorem plantedAddComm (a b : ℕ) : a + b = b + a := Nat.add_comm a b

end NavierStokes.Planted

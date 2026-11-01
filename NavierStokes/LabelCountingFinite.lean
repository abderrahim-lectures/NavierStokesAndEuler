import NavierStokes.SlotColoring
import Mathlib.Data.Set.Card

noncomputable section

namespace NavierStokes.LabelCountingFinite

open SlotColoring
open scoped BigOperators

def gridCandidates (c : Grid) (K : Fin 3 → ℕ) : Finset Grid :=
  Fintype.piFinset (fun j => Finset.Icc (c j - (K j : ℤ)) (c j + (K j : ℤ)))

def labelCandidates (n : ℕ) (c : Grid) (K : Fin 3 → ℕ) : Finset Label :=
  ((gridCandidates c K).product (Finset.univ : Finset Bool)).image (fun gs => (n, gs))








/-- Five consecutive integer indices include every natural band at distance
at most one from a real logarithmic coordinate. -/
def bandCandidates (c : ℝ) : Finset ℕ :=
  (Finset.Icc (⌊c⌋ - 2) (⌊c⌋ + 2)).image Int.toNat






end NavierStokes.LabelCountingFinite

import NavierStokes.SquaredPartition
import Mathlib.Data.Set.Card
import NavierStokes.LabelCountingFinite
import Mathlib.Analysis.Normed.Group.Bounded
import NavierStokes.PhysicalWaveSum

/-!
# Quantitative counts of slow-grid labels

The boxes here use the actual normalized spacing `S_n⁻³` and the actual
`SlotColoring.Label` indices. The radius factor is arbitrary and fixed, so
the counting bounds include every fixed-factor enlargement.
-/

noncomputable section

namespace NavierStokes.LabelCounting

open Set
open scoped BigOperators
open SlotColoring SquaredPartition

/-- A closed slow-coordinate grid box with an arbitrary enlargement factor. -/
def normalizedBox (A : ℝ) (L : Label) : Set Position :=
  {x | ∀ j, |x j - nativeSpacing L.1 * (L.2.1 j : ℝ)| ≤ A * nativeSpacing L.1}

/-- Both signs are counted separately, exactly as in the manuscript. -/
def relevantLabels (n : ℕ) (A : ℝ) (B : Set Position) : Set Label :=
  {L | L.1 = n ∧ (normalizedBox A L ∩ B).Nonempty}






/-- A normalized radial slice; the two transverse coordinates are arbitrary. -/
def radialSlice (I : Set ℝ) (Z T : ℝ) : Set Position :=
  {x | x 0 ∈ I ∧ x 1 = Z ∧ x 2 = T}







/-- Labels whose genuine closed dyadic band and enlarged slow box contain
the point. Each band uses its own physical-to-normalized chart. -/
def pointwiseLabels (D A q : ℝ) (x : Position) : Set Label :=
  {L | 1 ≤ L.1 ∧ q ∈ tsupport (dyadicMask (L.1 : ℤ)) ∧
    slowCoordinates D L.1 x ∈ normalizedBox A L}








end NavierStokes.LabelCounting

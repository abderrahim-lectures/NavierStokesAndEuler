import NavierStokes.SharpPhysicalLogBounds
import NavierStokes.MixedFiniteBackground

noncomputable section

namespace NavierStokes.WholeDomainStageBounds

open Set Function Filter ProblemStatement PhysicalWaveSum SharpGluedStageBounds
open scoped Topology ContDiff BigOperators

/-- The loss is selected before the length of the finite prefix. -/
def prefixLoss (initial positive : ℕ → ℝ) (m : ℕ) : ℝ := max (initial m) (positive m)

section Prefix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {h qbig : ℝ} {F : ℕ → SpaceTime → V} {gain initial positive : ℕ → ℝ}


end Prefix


end NavierStokes.WholeDomainStageBounds

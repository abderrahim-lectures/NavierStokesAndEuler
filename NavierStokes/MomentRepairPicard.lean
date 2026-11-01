import NavierStokes.MomentRepairPicardConvergence

/-! Compatibility of the same quadratic correction in two Banach norms.
Both solutions are limits of the same zero-started Picard iterates. -/

noncomputable section

open Filter Function
open scoped Topology

namespace NavierStokes.MomentRepairPicard

variable {E₀ Eₖ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [NormedAddCommGroup Eₖ] [NormedSpace ℝ Eₖ]







end NavierStokes.MomentRepairPicard

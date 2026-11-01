import NavierStokes.SmoothMomentRepair

/-! # Convergence of the actual quadratic moment-repair iterates

The Banach fixed-point theorem is applied to the explicit correction iteration
on its invariant quantitative ball. The returned solution is the limit of
those iterates starting from zero.
-/

noncomputable section

open Set Function Filter
open scoped Topology NNReal

namespace NavierStokes.MomentRepairPicardConvergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


end NavierStokes.MomentRepairPicardConvergence

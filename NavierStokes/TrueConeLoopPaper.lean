import NavierStokes.TrueConeLoop
import NavierStokes.FlatPrimitivePaper
import Mathlib.Topology.MetricSpace.Thickening

/-! Compact loop data specified on a neighborhood of the closed parameter
set suffice for the loop construction and its uniform cone margin. -/

noncomputable section

open Set
open scoped ContDiff

namespace NavierStokes.TrueConeLoopPaper

open TrueConeLoop SmoothLoop LoopMoments LoopVariance ConeAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]



end NavierStokes.TrueConeLoopPaper

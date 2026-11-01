import NavierStokes.ParametricFlatFactor
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! The flat primitive lemma with coefficients specified only near a compact
parameter rectangle. The factor includes the manuscript's explicit `1/2`. -/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokes.FlatPrimitivePaper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]



end NavierStokes.FlatPrimitivePaper

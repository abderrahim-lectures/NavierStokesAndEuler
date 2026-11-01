import NavierStokes.HeatProfileExtension
import Mathlib.RingTheory.Polynomial.Pochhammer

/-! Exact endpoint jets and quantitative small-argument estimates for the
gamma integral in `heat:exterior`. -/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokes.AppendixHeatResults

open RadialHeatProfile

/-- The rising factorial used in the manuscript: Mathlib's `ascPochhammer` polynomial,
evaluated at the argument. -/
def rising (b : ℝ) (n : ℕ) : ℝ := (ascPochhammer ℝ n).eval b



















end NavierStokes.AppendixHeatResults

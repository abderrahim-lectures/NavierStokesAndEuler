import NavierStokes.R3.CompactEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The time primitive of the spatial L² norm of a compact force

All spatial and temporal integrals use ordinary Lebesgue volume.
-/

noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology BigOperators ContDiff InnerProductSpace

namespace NavierStokesR3.CompactEnergy

open NavierStokes.ProblemStatement

/-- The ordinary spatial L² norm, used with square-integrable slices. -/
def l2Norm (f : VelocityField) (t : ℝ) : ℝ := Real.sqrt (l2Sq f t)

/-- The time integral of the spatial L² norm starting at time zero. -/
def cumulativeForceNorm (f : VelocityField) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, l2Norm f t





@[simp] theorem cumulativeForceNorm_zero (f : VelocityField) :
    cumulativeForceNorm f 0 = 0 := by
  simp [cumulativeForceNorm]






end NavierStokesR3.CompactEnergy

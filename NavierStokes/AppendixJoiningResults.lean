import NavierStokes.ReferenceBounds

/-!
# Additional literal bounds in the axis and joining appendices
-/

noncomputable section

namespace NavierStokes.AppendixJoiningResults

open Set
open scoped ContDiff
open NaturalAxisCoefficients NaturalProfile ProfileHistories ReferenceBounds


/-- The apparent quadratic parameter contributions cancel in the complete
constant angular source. This keeps its margin on the full printed range. -/
theorem axis_base_source_identity (h j η : ℝ) :
    -NaturalAxisData.W h j η - h * (1 - 2 * η * NaturalAxisData.U j η) =
      3 - h + j * η := by
  unfold NaturalAxisData.W NaturalAxisData.U NaturalAxisData.d NaturalAxisData.D
  ring


/-- The real denominator remains positive on the existing enlarged window
even under the larger `h ≤ .01` range of the current manuscript. -/
theorem axis_L_lower_bound_window {h η : ℝ} (hh0 : 0 ≤ h) (hh : h ≤ 1 / 100)
    (hη : η ∈ window.interval) : (4879 / 5000 : ℝ) ≤ NaturalAxisData.L h η := by
  have he : η ∈ Icc (-11 / 10 : ℝ) (11 / 10) := hη
  have hs : η ^ 2 ≤ 121 / 100 := by nlinarith [he.1, he.2]
  have hm := mul_nonneg hh0 (sub_nonneg.mpr hs)
  unfold NaturalAxisData.L
  nlinarith


end NavierStokes.AppendixJoiningResults

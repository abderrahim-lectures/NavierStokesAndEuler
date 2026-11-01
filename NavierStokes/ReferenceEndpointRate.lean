import NavierStokes.ReferenceUniformStocks
import NavierStokes.AppendixJoiningResults

/-! # The literal linear joining-width estimate at the actual held endpoint -/

noncomputable section

namespace NavierStokes.ReferenceEndpointRate

open Set Filter ProfileHistories ReferencePath NaturalProfile NaturalAxisCoefficients
open ReferenceUniformStocks ReferenceUniformJets TransitionRamp ClosedIntervalJetAlgebra StressActivation
open scoped Topology ContDiff

variable {h j σ Λ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hΛ : 0 < Λ) (hP0 : ContDiff ℝ ∞ P0)
    (hs : NaturalAxisRange.Parameters h j)

/-- The same stock-driven continuation, on the full printed numerical range. -/
def reference (q : Choice d Λ) : StockReference parameterInterval where
  exponent := h
  radius0 := (q.input hΛ).endpoint
  radius0_pos := (q.input hΛ).endpoint_pos
  domain := (q.input hΛ).radialDomain
  profiles := q.profiles hΛ hP0
  log_mem := fun y _ hη => StressActivation.FromReference.log_radius_mem (q.input hΛ) y hη
  f_pos := fun y _ hη => (q.input hΛ).refF_pos q.δ
    (StressActivation.FromReference.log_radius_mem (q.input hΛ) y hη)
    (mul_pos (q.input hΛ).endpoint_pos (Real.exp_pos _)).le
  L_ne_zero := fun η hη => (lt_of_lt_of_le (by norm_num : (0:ℝ)<4879/5000)
    (AppendixJoiningResults.axis_L_lower_bound_window hs.h_pos.le hs.h_le
      ⟨hη.1.le,hη.2.le⟩)).ne'


theorem reference_radius (q : Choice d Λ) :
    (reference d hΛ hP0 hs q).radius0 = 4/Λ := rfl















end NavierStokes.ReferenceEndpointRate

import NavierStokes.WholeDomainHeatGeometry

/-! # Exact scaling identities for the physical heat velocity and pressure -/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.WholeDomainHeatBounds

open ProblemStatement PhysicalWaveSum


theorem rescale_heat_ratio (a : ℝ) (ha : 0 < a) (z : ℝ) {w : SpaceTime}
    (hs : 0 < AxisymmetricFields.radialEnergy w.2) :
    (1-(rescale a ha z w).1) / AxisymmetricFields.radialEnergy (rescale a ha z w).2 =
      (1-w.1) / AxisymmetricFields.radialEnergy w.2 := by
  rw [rescale_time, rescale_radialEnergy]
  field_simp
  ring



theorem heatPressure_rescale (C h a : ℝ) (ha : 0 < a) (z : ℝ) {w : SpaceTime}
    (hs : 0 < AxisymmetricFields.radialEnergy w.2) :
    BaseExterior.heatPressureField C h w =
      a ^ (-2*TerminalPressure.amplitudeExponent h) *
        BaseExterior.heatPressureField C h (rescale a ha z w) := by
  change BaseExterior.heatPressure C h (AxisymmetricFields.profilePoint w.1 w.2) =
    a ^ (-2*TerminalPressure.amplitudeExponent h) *
      BaseExterior.heatPressure C h (AxisymmetricFields.profilePoint
        (rescale a ha z w).1 (rescale a ha z w).2)
  rw [BaseExterior.heatPressure_formula C h hs,
    BaseExterior.heatPressure_formula C h (by
      change 0 < AxisymmetricFields.radialEnergy (rescale a ha z w).2
      rw [rescale_radialEnergy]; exact div_pos hs ha)]
  dsimp only [AxisymmetricFields.profilePoint]
  rw [rescale_heat_ratio a ha z hs, rescale_radialEnergy, Real.div_rpow hs.le ha.le]
  have hp : a ^ (-2*TerminalPressure.amplitudeExponent h) ≠ 0 :=
    (Real.rpow_pos_of_pos ha _).ne'
  field_simp

end NavierStokes.WholeDomainHeatBounds

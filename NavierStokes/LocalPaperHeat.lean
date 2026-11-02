import NavierStokes.LocalPaperTheorem
import NavierStokes.BaseExterior
import Mathlib.MeasureTheory.Function.JacobianOneDim
import NavierStokes.DirectAngularDiagonal

/-!
# The local theorem's literal radial heat formulas

These consequences use the same fields and normalization as `local_theorem`.
They express the heat exterior in the manuscript's radius coordinate, including
the genuinely integrable pressure tail.
-/
/-! Merged from `NavierStokes.LocalHeatPressure`. -/
/-!
# Canonical heat pressure in the radius coordinate

The canonical pressure in the regular coordinate `s = r ^ 2 / 2` is exactly
the radius tail integral of the squared heat amplitude divided by the radius.
-/

noncomputable section

open Set MeasureTheory

namespace NavierStokes.LocalHeatPressure

private theorem radiusChange_image {r : ℝ} (hr : 0 < r) :
    (fun ρ : ℝ => ρ ^ 2 / 2) '' Ioi r = Ioi (r ^ 2 / 2) := by
  ext s
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    change r < ρ at hρ
    change r ^ 2 / 2 < ρ ^ 2 / 2
    nlinarith
  · intro hs
    change r ^ 2 / 2 < s at hs
    have hs0 : 0 < s := by
      have hr2 := sq_nonneg r
      linarith
    refine ⟨Real.sqrt (2 * s), ?_, ?_⟩
    · have hsq := Real.sq_sqrt (show 0 ≤ 2 * s by positivity)
      have hnonneg := Real.sqrt_nonneg (2 * s)
      change r < Real.sqrt (2 * s)
      nlinarith
    · dsimp only
      rw [Real.sq_sqrt (by positivity)]
      ring

private theorem radiusChange_deriv (r ρ : ℝ) :
    HasDerivWithinAt (fun x : ℝ => x ^ 2 / 2) ρ (Ioi r) ρ := by
  simpa using (((hasDerivAt_id ρ).pow 2).div_const 2).hasDerivWithinAt (s := Ioi r)

private theorem radiusChange_injOn {r : ℝ} (hr : 0 < r) :
    InjOn (fun ρ : ℝ => ρ ^ 2 / 2) (Ioi r) := by
  intro x hx y hy hxy
  change r < x at hx
  change r < y at hy
  change x ^ 2 / 2 = y ^ 2 / 2 at hxy
  nlinarith

/-- Change the canonical pressure integral from `s` to the physical radius. -/
theorem canonicalPressure_radius_integral (F : SimilarityProfile.PhysicalProfile)
    (t z : ℝ) {r : ℝ} (hr : 0 < r) :
    TerminalStress.canonicalPressure F (TerminalStress.radiusPoint t r z) =
      -(∫ ρ in Ioi r, ρ * F (TerminalStress.radiusPoint t ρ z) ^ 2) := by
  unfold TerminalStress.canonicalPressure TerminalStress.radiusPoint
  dsimp only
  congr 1
  rw [← radiusChange_image hr]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun ρ _ => radiusChange_deriv r ρ) (radiusChange_injOn hr)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  dsimp only
  rw [abs_of_pos (hr.trans hρ), smul_eq_mul]

/-- The regular swirl coefficient is the heat amplitude divided by the radius. -/
theorem heatCoefficient_radius (C h t z : ℝ) {r : ℝ} (hr : 0 < r) :
    BaseExterior.heatCoefficient C h (TerminalStress.radiusPoint t r z) =
      TerminalStress.heatAmplitude C (1 + h) t r / r := by
  have he := TerminalStress.swirlCoefficient_amplitude C h (fun _ => 1) t z hr
  simp only [TerminalStress.radialSlice, TerminalStress.flattening, mul_one] at he
  apply (eq_div_iff hr.ne').2
  exact (mul_comm _ _).trans he

/-- The canonical pure heat pressure is the literal radial improper integral. -/
theorem heatPressure_radius_integral (C h t z : ℝ) {r : ℝ} (hr : 0 < r) :
    BaseExterior.heatPressure C h (TerminalStress.radiusPoint t r z) =
      -(∫ ρ in Ioi r, TerminalStress.heatAmplitude C (1 + h) t ρ ^ 2 / ρ) := by
  rw [BaseExterior.heatPressure, canonicalPressure_radius_integral _ t z hr]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  dsimp only
  rw [heatCoefficient_radius C h t z (hr.trans hρ)]
  field_simp

/-- The radius pressure integrand is integrable on every positive exterior tail. -/
theorem heatAmplitude_sq_div_integrable (C : ℝ) {h t r : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1) (hr : 0 < r) :
    IntegrableOn (fun ρ => TerminalStress.heatAmplitude C (1 + h) t ρ ^ 2 / ρ)
      (Ioi r) := by
  have hi := BaseExterior.heatCoefficient_sq_integrable C hh hh1
    (z := 0) ht (show 0 < r ^ 2 / 2 by positivity)
  rw [← radiusChange_image hr] at hi
  have hi' := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun ρ _ => radiusChange_deriv r ρ) (radiusChange_injOn hr)
    (fun s => BaseExterior.heatCoefficient C h (t, (s, 0)) ^ 2)).mp hi
  apply hi'.congr_fun _ measurableSet_Ioi
  intro ρ hρ
  change |ρ| • BaseExterior.heatCoefficient C h
      (TerminalStress.radiusPoint t ρ 0) ^ 2 = _
  rw [abs_of_pos (hr.trans hρ), smul_eq_mul,
    heatCoefficient_radius C h t 0 (hr.trans hρ)]
  field_simp

end NavierStokes.LocalHeatPressure

/-! Merged from `NavierStokes.LocalHeatFormula`. -/
/-!
# The literal exterior heat profile in radial coordinates

This packages the existing heat solution using the manuscript's argument
`τ / r²`, with its fixed normalization absorbed into the exterior profile.
-/

noncomputable section

namespace NavierStokes.LocalHeatFormula

open Set
open scoped ContDiff

/-- The exterior profile with the fixed physical normalization absorbed. -/
noncomputable def exteriorProfile (C h y : ℝ) : ℝ :=
  C * (2 : ℝ) ^ (1 / 2 + h) * RadialHeatProfile.profile (1 + h) (4 * y)

theorem exteriorProfile_smooth (C : ℝ) {h : ℝ} (hh : 0 < h) :
    ContDiffOn ℝ ∞ (exteriorProfile C h) (Ici 0) := by
  have hm : MapsTo (fun y : ℝ => 4 * y) (Ici 0) (Ici 0) := by
    intro y hy
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hy
  exact contDiffOn_const.mul
    ((RadialHeatProfile.profile_contDiffOn (show 1 < 1 + h by linarith)).comp
      (contDiffOn_const.mul contDiffOn_id) hm)

theorem exteriorProfile_iteratedDerivWithin (C : ℝ) {h : ℝ} (hh : 0 < h)
    (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    iteratedDerivWithin n (exteriorProfile C h) (Ici 0) y =
      (C * (2 : ℝ) ^ (1 / 2 + h)) * (4 : ℝ) ^ n *
        iteratedDerivWithin n (RadialHeatProfile.profile (1 + h)) (Ici 0) (4 * y) := by
  unfold exteriorProfile
  rw [iteratedDerivWithin_const_mul_field]
  rw [iteratedDerivWithin_comp_const_smul (s := Ici (0 : ℝ)) hy (uniqueDiffOn_Ici 0)
    ((RadialHeatProfile.profile_contDiffOn (show 1 < 1 + h by linarith)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)) 4
    (fun z hz => mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hz)]
  simp only [smul_eq_mul, mul_assoc]

/-- A finite bound independent of the nonnegative profile argument. -/
noncomputable def exteriorDerivativeBound (C h : ℝ) (n : ℕ) : ℝ :=
  |C * (2 : ℝ) ^ (1 / 2 + h)| * (4 : ℝ) ^ n *
    (|(Real.Gamma (1 + h))⁻¹ * RadialHeatProfile.derivativeCoeff (1 + h) n| *
      Real.Gamma (1 + h + (n : ℝ)))

theorem exteriorProfile_derivative_bound (C : ℝ) {h : ℝ} (hh : 0 < h)
    (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    |iteratedDerivWithin n (exteriorProfile C h) (Ici 0) y| ≤ exteriorDerivativeBound C h n := by
  rw [exteriorProfile_iteratedDerivWithin C hh n hy, abs_mul, abs_mul,
    abs_of_nonneg (show 0 ≤ (4 : ℝ) ^ n by positivity)]
  exact mul_le_mul_of_nonneg_left
    (RadialHeatProfile.profile_derivative_bound (show 1 < 1 + h by linarith) n
      (mul_nonneg (by norm_num) hy)) (by positivity)

theorem exteriorProfile_all_derivatives_bounded (C : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Ici (0 : ℝ),
      |iteratedDerivWithin n (exteriorProfile C h) (Ici 0) y| ≤ M := by
  refine ⟨exteriorDerivativeBound C h n, ?_, fun y hy => exteriorProfile_derivative_bound C hh n hy⟩
  exact (abs_nonneg _).trans (exteriorProfile_derivative_bound C hh n (y := 0) le_rfl)

/-- The angular speed expressed using backward time. -/
noncomputable def amplitude (C h τ r : ℝ) : ℝ :=
  C * RadialHeatProfile.radialProfile (1 + h) τ r

theorem amplitude_formula (C h τ : ℝ) {r : ℝ} (hr : 0 < r) :
    amplitude C h τ r = r ^ (-1 - 2 * h) * exteriorProfile C h (τ / r ^ 2) := by
  have hpow : (r ^ 2 / 2) ^ (-(1 / 2 + h)) =
      r ^ (-1 - 2 * h) * (2 : ℝ) ^ (1 / 2 + h) := by
    rw [Real.div_rpow (sq_nonneg r) (by norm_num), ← Real.rpow_natCast r 2,
      ← Real.rpow_mul hr.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * -(1 / 2 + h) = -1 - 2 * h by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
  have harg : 2 * τ / (r ^ 2 / 2) = 4 * (τ / r ^ 2) := by ring
  rw [amplitude, RadialHeatProfile.radialProfile_source_formula, hpow, harg, exteriorProfile]
  ring

theorem amplitude_heat_equation (C : ℝ) {h τ r : ℝ}
    (hh : 0 < h) (hτ : 0 < τ) (hr : 0 < r) :
    -deriv (fun τ => amplitude C h τ r) τ =
      iteratedDeriv 2 (amplitude C h τ) r + deriv (amplitude C h τ) r / r -
        amplitude C h τ r / r ^ 2 := by
  have he := RadialHeatProfile.radial_heat_equation (show 1 < 1 + h by linarith) hτ hr
  change -deriv (fun τ => C * RadialHeatProfile.radialProfile (1 + h) τ r) τ =
    iteratedDeriv 2 (fun r => C * RadialHeatProfile.radialProfile (1 + h) τ r) r +
      deriv (fun r => C * RadialHeatProfile.radialProfile (1 + h) τ r) r / r -
      C * RadialHeatProfile.radialProfile (1 + h) τ r / r ^ 2
  rw [iteratedDeriv_const_mul_field, deriv_const_mul_field, deriv_const_mul_field]
  linear_combination C * he

theorem amplitude_eq_heatAmplitude (C h t r : ℝ) :
    amplitude C h (1 - t) r = TerminalStress.heatAmplitude C (1 + h) t r := rfl

theorem heatCoefficient_radius (C h t z : ℝ) {r : ℝ} (hr : 0 < r) :
    BaseExterior.heatCoefficient C h (TerminalStress.radiusPoint t r z) =
      amplitude C h (1 - t) r / r := by
  have he := TerminalStress.swirlCoefficient_amplitude C h (fun _ => 1) t z hr
  simp only [TerminalStress.radialSlice, TerminalStress.flattening, mul_one] at he
  apply (eq_div_iff hr.ne').mpr
  simpa only [BaseExterior.heatCoefficient, amplitude_eq_heatAmplitude, mul_comm] using he

theorem heatVelocity_formula (C h : ℝ) {w : ProblemStatement.SpaceTime}
    (hs : 0 < AxisymmetricFields.radialEnergy w.2) :
    BaseExterior.heatVelocity C h w =
      (amplitude C h (1 - w.1) (Real.sqrt (2 * AxisymmetricFields.radialEnergy w.2)) /
        Real.sqrt (2 * AxisymmetricFields.radialEnergy w.2)) • BaseResidual.angularVector w := by
  rw [BaseExterior.heatVelocity_eq_angularVector]
  have he := heatCoefficient_radius C h w.1 (w.2 2)
    (show 0 < Real.sqrt (2 * AxisymmetricFields.radialEnergy w.2) by positivity)
  rw [TerminalStress.radiusPoint_profilePoint hs.le] at he
  rw [he]




end NavierStokes.LocalHeatFormula


noncomputable section

namespace NavierStokes.LocalPaper

open Set MeasureTheory ProblemStatement
open scoped ContDiff

variable {h qstar Xa Xext C : ℝ} {A D u : VelocityField} {p : PressureField}

theorem Properties.exterior_profile_smooth
    (hp : Properties h qstar Xa Xext C A D u p) :
    ContDiffOn ℝ ∞ (LocalHeatFormula.exteriorProfile C h) (Ici 0) :=
  LocalHeatFormula.exteriorProfile_smooth C hp.exponent_small.1

theorem Properties.exterior_profile_derivatives_bounded
    (hp : Properties h qstar Xa Xext C A D u p) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Ici (0 : ℝ),
      |iteratedDerivWithin n (LocalHeatFormula.exteriorProfile C h) (Ici 0) y| ≤ M :=
  LocalHeatFormula.exteriorProfile_all_derivatives_bounded C hp.exponent_small.1 n

/-- The exterior angular magnitude is exactly `r^(-1-2h) H_ext(τ/r²)`. -/
theorem Properties.exterior_amplitude_formula
    (_hp : Properties h qstar Xa Xext C A D u p) (τ : ℝ) {r : ℝ} (hr : 0 < r) :
    LocalHeatFormula.amplitude C h τ r =
      r ^ (-1 - 2 * h) * LocalHeatFormula.exteriorProfile C h (τ / r ^ 2) :=
  LocalHeatFormula.amplitude_formula C h τ hr

theorem Properties.exterior_heat_equation
    (hp : Properties h qstar Xa Xext C A D u p) {τ r : ℝ}
    (hτ : 0 < τ) (hr : 0 < r) :
    -deriv (fun τ => LocalHeatFormula.amplitude C h τ r) τ =
      iteratedDeriv 2 (LocalHeatFormula.amplitude C h τ) r +
        deriv (LocalHeatFormula.amplitude C h τ) r / r -
        LocalHeatFormula.amplitude C h τ r / r ^ 2 :=
  LocalHeatFormula.amplitude_heat_equation C hp.exponent_small.1 hτ hr

/-- The same exterior direct field is `K eθ`, and its pressure is the
literal radius integral `-∫ K²/ρ`; the integrability assertion is explicit. -/
theorem Properties.exterior_radial_form
    (hp : Properties h qstar Xa Xext C A D u p) {w : SpaceTime}
    (ht : w.1 < 1) (hq : PhysicalWaveSum.physicalQ h w < qstar)
    (hX : Xext ≤ AxisymmetricFields.radialEnergy w.2 / PhysicalWaveSum.physicalQ h w) :
    let r := Real.sqrt (2 * AxisymmetricFields.radialEnergy w.2)
    0 < r ∧
      D w = (LocalHeatFormula.amplitude C h (1 - w.1) r / r) • BaseResidual.angularVector w ∧
      p w = -(∫ ρ in Ioi r, LocalHeatFormula.amplitude C h (1 - w.1) ρ ^ 2 / ρ) ∧
      IntegrableOn (fun ρ => LocalHeatFormula.amplitude C h (1 - w.1) ρ ^ 2 / ρ) (Ioi r) := by
  have hh1 : h < 1 / 2 := by linarith [hp.exponent_small.2]
  have hq0 := PhysicalWaveSum.physicalQ_pos hp.exponent_small.1 hh1 ht
  have hXe : 0 < Xext := hp.edges_ordered.1.trans hp.edges_ordered.2
  have hs : 0 < AxisymmetricFields.radialEnergy w.2 :=
    (mul_pos hXe hq0).trans_le ((le_div_iff₀ hq0).mp hX)
  have hr : 0 < Real.sqrt (2 * AxisymmetricFields.radialEnergy w.2) := by positivity
  obtain ⟨_, hD, hP, _⟩ := hp.exterior w ht hq hX
  refine ⟨hr, hD.trans (LocalHeatFormula.heatVelocity_formula C h hs), ?_, ?_⟩
  · rw [hP]
    have he := LocalHeatPressure.heatPressure_radius_integral C h w.1 (w.2 2) hr
    rw [TerminalStress.radiusPoint_profilePoint hs.le] at he
    exact he
  · exact LocalHeatPressure.heatAmplitude_sq_div_integrable C hp.exponent_small.1 hh1 ht hr

end NavierStokes.LocalPaper

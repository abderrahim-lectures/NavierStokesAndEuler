import NavierStokes.R3.ComparisonCutoffs
import NavierStokes.R3.ComparisonFiniteEnergy
import NavierStokes.R3.ComparisonGronwall
import NavierStokes.R3.LocalizedDifferenceEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.OpenPos
import NavierStokes.R3.LocalizedFluxEstimates
import NavierStokes.R3.ComparisonRateBound

/-!
# Closing the whole-space comparison estimate

This module isolates the final PDE energy calculation. Its explicit pressure
flux hypothesis is discharged by the pressure reconstruction modules in the
whole-space uniqueness theorem; it is not a competitor hypothesis.
-/

/-! Merged from `NavierStokes.R3.WholeSpaceEnergyLimit`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# Removing the spatial energy cutoff

At a fixed time, square integrability gives an integrable dominating function.
This module removes the cutoff only after that hypothesis has been supplied.
-/


noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokesR3.WholeSpaceEnergyLimit

open ProblemStatement Comparison ComparisonCutoffs

theorem integral_weight_tendsto {w : Space → Space} (hw : Continuous w)
    (hi : Integrable (fun x : Space => ‖w x‖ ^ 2)) :
    Tendsto (fun R : ℝ => ∫ x : Space, weight R x * ‖w x‖ ^ 2)
      atTop (𝓝 (l2Sq w)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x : Space => ‖w x‖ ^ 2)
  · exact Filter.Eventually.of_forall fun R =>
      ((weight_smooth R).continuous.mul (hw.norm.pow 2)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weight_nonneg R x) (sq_nonneg _))]
      exact mul_le_of_le_one_left (sq_nonneg _) (weight_le_one R x)
  · exact hi
  · exact Filter.Eventually.of_forall fun x => by
      have h := ((cutoff_tendsto_one x).pow 8).mul_const (‖w x‖ ^ 2)
      simpa only [weight, one_pow, one_mul] using h

theorem eq_zero_of_l2Sq_eq_zero {w : Space → Space} (hw : Continuous w)
    (hi : Integrable (fun x : Space => ‖w x‖ ^ 2)) (hz : l2Sq w = 0) :
    ∀ x : Space, w x = 0 := by
  have hae : (fun x : Space => ‖w x‖ ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hi).mp hz
  have heq : (fun x : Space => ‖w x‖ ^ 2) = (fun _ : Space => (0 : ℝ)) :=
    Measure.eq_of_ae_eq hae (hw.norm.pow 2) continuous_const
  intro x
  have hx : ‖w x‖ ^ 2 = 0 := congrFun heq x
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)

/-- A bound on actual weighted integrals, uniform over large radii, forces a
continuous square-integrable field to vanish everywhere. -/
theorem eq_zero_of_radius_bound {w : Space → Space} (hw : Continuous w)
    (hi : Integrable (fun x : Space => ‖w x‖ ^ 2)) {D R₀ : ℝ}
    (hbound : ∀ R : ℝ, max 1 R₀ ≤ R →
      (∫ x : Space, weight R x * ‖w x‖ ^ 2) ≤ D / R) :
    ∀ x : Space, w x = 0 := by
  have hlim := integral_weight_tendsto hw hi
  have hz : Tendsto (fun R : ℝ => D / R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => D) atTop (𝓝 D)).mul
        (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0))
  have hle : l2Sq w ≤ 0 :=
    le_of_tendsto_of_tendsto hlim hz (eventually_atTop.2 ⟨max 1 R₀, hbound⟩)
  exact eq_zero_of_l2Sq_eq_zero hw hi
    (le_antisymm hle (integral_nonneg fun x => sq_nonneg _))

/-- The final scalar and cutoff step of uniqueness. The differential estimate
is an explicit input here; deriving it from the PDE and pressure is separate. -/
theorem eq_zero_of_weighted_rate_bound {w : VelocityField} {T K C R₀ : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hw : ContDiffOn ℝ ∞ w (Comparison.slab 0 T))
    (hi : ∀ t ∈ Icc (0 : ℝ) T, SquareIntegrableAtTime w t)
    (hzero : ∀ x : Space, w (0, x) = 0)
    (hrate : ∀ R : ℝ, max 1 R₀ ≤ R → ∀ t ∈ Ioo (0 : ℝ) T,
      weightedEnergyRate (weight R) w t ≤ K * weightedEnergy (weight R) w t + C / R) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space, w (t, x) = 0 := by
  intro t ht
  have hs := NavierStokes.PeriodicUniqueness.spatial_smooth hw ht
  apply eq_zero_of_radius_bound hs.continuous (hi t ht)
    (D := C * T * Real.exp (K * T)) (R₀ := R₀)
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR)
  have hcont := LocalizedDifferenceEnergy.weightedEnergy_continuousOn
    (weight_smooth R).continuous (weight_hasCompactSupport hRpos) hw
  have hinit : weightedEnergy (weight R) w 0 = 0 := by
    simp [weightedEnergy, hzero]
  exact ComparisonGronwall.le_div_radius_of_deriv_le hT hK hC hRpos hcont hinit
    (fun s hs => LocalizedDifferenceEnergy.weightedEnergy_hasDerivAt
      (weight_smooth R) (weight_hasCompactSupport hRpos) hw hs)
    (hrate R hR) t ht

end NavierStokesR3.WholeSpaceEnergyLimit


end



noncomputable section

open Set MeasureTheory
open scoped ContDiff BigOperators InnerProductSpace

namespace NavierStokesR3.WholeSpaceComparisonClosure

open ProblemStatement Comparison ComparisonCutoffs
open NavierStokes.ProblemStatement (spatialDerivative spatialDivergence)
open NavierStokes.PeriodicUniqueness (spatial_smooth time_differentiable_at_interior)

def pressureEnvelope (R A B : ℝ) : ℝ :=
  (B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) +
    R ^ (-7 / 4 : ℝ) * B ^ (3 / 4 : ℝ)

/-- Once the pressure flux has been estimated from the equations, compact
localized integration, Sobolev, Young and Gronwall imply equality everywhere.
All constants precede the radius and time quantifiers. -/
theorem eq_of_pressure_flux_bound {T M G CP R₀ : ℝ}
    {u v : VelocityField} {p q : PressureField}
    (hT : 0 ≤ T) (hM0 : 0 ≤ M) (hG0 : 0 ≤ G) (hCP0 : 0 ≤ CP)
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hwu : ∀ t ∈ Icc (0 : ℝ) T, MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hM : ∀ t ∈ Icc (0 : ℝ) T, comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤ M)
    (hG : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖spatialDerivative u t x‖ ≤ G)
    (hdu : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      navierStokesResidual 1 u p t x = navierStokesResidual 1 v q t x)
    (hzero : ∀ x, u (0, x) = v (0, x))
    (hvanish : ∀ R ≥ R₀, ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      fderiv ℝ (weight R) x (u (t, x)) = 0)
    (hpressure : ∀ R ≥ 1, ∀ t ∈ Ioo (0 : ℝ) T,
      |∫ x : Space, (p - q) (t, x) * fderiv ℝ (weight R) x ((u - v) (t, x))| ≤
        CP * pressureEnvelope R (dissipationRoot (cutoff R) (u - v) t)
          (cutoffL6 (cutoff R) (u - v) t)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x) := by
  let C0 := LocalizedFluxEstimates.weightLaplacianConstant * M ^ 2 / 2
  let C1 := 4 * derivativeConstant 1 * M ^ (3 / 2 : ℝ)
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    exact div_nonneg (mul_nonneg
      LocalizedFluxEstimates.weightLaplacianConstant_pos.le (sq_nonneg M)) (by norm_num)
  have hC1 : 0 ≤ C1 := by
    dsimp [C1]
    exact mul_nonneg (mul_nonneg (by norm_num) (derivativeConstant_pos 1).le)
      (Real.rpow_nonneg hM0 _)
  obtain ⟨D, hD, hrate⟩ := ComparisonRateBound.exists_uniform_rate_bound hC0 hC1 hCP0
    WeightedSobolev.weightedSobolevConstant_pos.le
    (mul_nonneg (derivativeConstant_pos 1).le hM0)
  have hwzero : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, (u - v) (t, x) = 0 := by
    apply WholeSpaceEnergyLimit.eq_zero_of_weighted_rate_bound (K := 2 * G) (C := D) (R₀ := R₀)
      hT (mul_nonneg (by norm_num) hG0) hD (hu.sub hv)
    · intro t ht
      exact (memLp_two_iff_integrable_sq_norm (hwu t ht).aestronglyMeasurable).mp (hwu t ht)
    · intro x
      simp only [hzero x, sub_self]
    · intro R hR t ht
      have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
      have hRpos : 0 < R := zero_lt_one.trans_le hR1
      have htcc : t ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self ht
      have hut := spatial_smooth hu htcc
      have hvt := spatial_smooth hv htcc
      have hwt := hut.sub hvt
      have hw2 := hwu t htcc
      let A := dissipationRoot (cutoff R) (u - v) t
      let B := cutoffL6 (cutoff R) (u - v) t
      have hA : 0 ≤ A := Real.sqrt_nonneg _
      have hB : 0 ≤ B := ENNReal.toReal_nonneg
      have hm : 0 ≤ comparisonLpNorm 2 (fun x => (u - v) (t, x)) := ENNReal.toReal_nonneg
      have hAsq : A ^ 2 = weightedDissipation (weight R) (u - v) t := by
        apply Real.sq_sqrt
        exact LocalizedDifferenceEnergy.weightedDissipation_nonneg (weight_nonneg R) _ _
      have hSob0 := WeightedSobolev.cutoffL6_le
        ((cutoff_smooth R).of_le (by simp)) (cutoff_hasCompactSupport hRpos)
        (hwt.of_le (by simp)) hw2 (cutoff_nonneg R) (cutoff_le_one R)
        (div_nonneg (derivativeConstant_pos 1).le hRpos.le) (cutoff_fderiv_le hRpos)
      have hSob : B ≤ WeightedSobolev.weightedSobolevConstant *
          (A + (derivativeConstant 1 * M) / R) := by
        apply hSob0.trans
        apply mul_le_mul_of_nonneg_left _ WeightedSobolev.weightedSobolevConstant_pos.le
        apply add_le_add_right
        calc
          derivativeConstant 1 / R * comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤
              derivativeConstant 1 / R * M := mul_le_mul_of_nonneg_left (hM t htcc)
                (div_nonneg (derivativeConstant_pos 1).le hRpos.le)
          _ = _ := by ring
      have hc := LocalizedFluxEstimates.neg_coupling_le_weightedEnergy
        (u := u) (w := u - v) (t := t)
        (weight_smooth R).continuous (weight_hasCompactSupport hRpos) (weight_nonneg R)
        (hut.of_le (by simp)) hwt.continuous (hG t htcc)
      have hl := (LocalizedFluxEstimates.weight_laplacian_flux_bound hRpos hw2).2
      have hl' : |∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
          ∑ i : Fin 3, partialD i (partialD i (weight R)) x| ≤
          LocalizedFluxEstimates.weightLaplacianConstant * M ^ 2 / R ^ 2 := by
        apply hl.trans
        calc
          _ ≤ (LocalizedFluxEstimates.weightLaplacianConstant / R ^ 2) * M ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm (hM t htcc) 2)
              (div_nonneg LocalizedFluxEstimates.weightLaplacianConstant_pos.le (sq_nonneg _))
          _ = _ := by ring
      have htflux := (LocalizedFluxEstimates.transport_flux_bound
        ((cutoff_smooth R).of_le (by simp)) (cutoff_hasCompactSupport hRpos)
        hut.continuous hvt.continuous hw2 (cutoff_nonneg R) (cutoff_le_one R)
        (div_nonneg (derivativeConstant_pos 1).le hRpos.le) (cutoff_fderiv_le hRpos)
        (hvanish R ((le_max_right _ _).trans hR) t htcc)).2
      have htflux' : |∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
          fderiv ℝ (weight R) x (v (t, x))| ≤
          (8 * derivativeConstant 1 * M ^ (3 / 2 : ℝ)) / R * B ^ (3 / 2 : ℝ) := by
        apply htflux.trans
        calc
          _ ≤ (8 * (derivativeConstant 1 / R)) * M ^ (3 / 2 : ℝ) * B ^ (3 / 2 : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hB _)
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow hm (hM t htcc) (by norm_num))
              (mul_nonneg (by norm_num) (div_nonneg (derivativeConstant_pos 1).le hRpos.le))
          _ = _ := by ring
      have hpflux := hpressure R hR1 t ht
      have hbalance := LocalizedDifferenceEnergy.difference_energy_balance
        (weight_smooth R) (weight_hasCompactSupport hRpos) hut hvt
        (spatial_smooth hp htcc) (spatial_smooth hq htcc)
        (time_differentiable_at_interior hu ht) (time_differentiable_at_interior hv ht)
        (hdu t ht) (hdv t ht) (hNS t ht)
      apply hrate R hR1 A hA B hB hSob
        (weightedEnergy (weight R) (u - v) t) (weightedEnergyRate (weight R) (u - v) t) G
      rw [hAsq, hbalance]
      have hlle := (le_abs_self (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        ∑ i : Fin 3, partialD i (partialD i (weight R)) x)).trans hl'
      have htle := (le_abs_self (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        fderiv ℝ (weight R) x (v (t, x)))).trans htflux'
      have hple : (∫ x : Space, (p - q) (t, x) *
          fderiv ℝ (weight R) x ((u - v) (t, x))) ≤ CP * pressureEnvelope R A B :=
        (le_abs_self _).trans hpflux
      have hsum := add_le_add (add_le_add
        (add_le_add hc (mul_le_mul_of_nonneg_left hlle (by norm_num : (0 : ℝ) ≤ 1 / 2)))
        (mul_le_mul_of_nonneg_left htle (by norm_num : (0 : ℝ) ≤ 1 / 2))) hple
      convert! hsum using 1
      dsimp only [C0, C1, pressureEnvelope]
      ring
  intro t ht x
  exact sub_eq_zero.mp (hwzero t ht x)

end NavierStokesR3.WholeSpaceComparisonClosure

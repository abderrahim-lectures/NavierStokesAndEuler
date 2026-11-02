import NavierStokes.R3.ComparisonCutoffs
import NavierStokes.R3.ComparisonFiniteEnergy
import NavierStokes.R3.ComparisonGronwall
import NavierStokes.R3.CompactEnergy
import NavierStokes.R3.ComparisonSetup
import NavierStokes.R3.LocalizedTransport
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.OpenPos
import NavierStokes.R3.WeightedSobolev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Closing the whole-space comparison estimate

This module isolates the final PDE energy calculation. Its explicit pressure
flux hypothesis is discharged by the pressure reconstruction modules in the
whole-space uniqueness theorem; it is not a competitor hypothesis.
-/
/-! Merged from `NavierStokes.R3.LocalizedDifferenceEnergy` (in a section, so its `open`s cannot leak). -/
section
/-!
# The compactly weighted difference-energy identity on R³

The cutoff alone has compact support. Both velocities and both pressures may
be arbitrary smooth fields on the time slab. Every integral below is an
ordinary Lebesgue volume integral on Euclidean three-space.
-/
/-! Merged from `NavierStokes.R3.LocalizedLaplacian`. -/
/-!
# The Laplacian in a compactly weighted energy identity

All integrals are ordinary volume integrals on Euclidean three-space. The
weight is smooth and compactly supported; the vector field is smooth but is
not required to have compact support or globally integrable derivatives.
-/


noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff InnerProductSpace

namespace NavierStokesR3.LocalizedDifferenceEnergy

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness


private theorem laplacian_partial_smul {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (i : Fin 3) (x : Space) :
    spatialPartial i (fun y => χ y • w y) x =
      χ x • spatialPartial i w x + spatialPartial i χ x • w x := by
  unfold spatialPartial
  rw [fderiv_fun_smul (hχ.differentiable (by simp) x)
    (hw.differentiable (by simp) x)]
  rfl

theorem laplacian_integrable_weighted_partial_sq {χ : Space → ℝ} {w : Space → Space}
    (hχ : Continuous χ) (hw : ContDiff ℝ ∞ w) (hcχ : HasCompactSupport χ)
    (i : Fin 3) :
    Integrable (fun x => χ x * ‖spatialPartial i w x‖ ^ 2) :=
  (hχ.mul ((spatial_partial_contDiff hw i).continuous.norm.pow 2)).integrable_of_hasCompactSupport
    hcχ.mul_right


theorem laplacian_integrable_cutoff_second_partial {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : Continuous w) (hcχ : HasCompactSupport χ)
    (i : Fin 3) :
    Integrable (fun x => ‖w x‖ ^ 2 * spatialPartial i (spatialPartial i χ) x) :=
  ((hw.norm.pow 2).mul
    (spatial_partial_contDiff (spatial_partial_contDiff hχ i) i).continuous).integrable_of_hasCompactSupport
    (CompactEnergy.compact_partial (CompactEnergy.compact_partial hcχ i) i).mul_left



/-- The one-coordinate weighted integration-by-parts identity. -/
theorem integral_weighted_second_partial {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (hcχ : HasCompactSupport χ)
    (i : Fin 3) :
    (∫ x, χ x * ⟪w x, spatialPartial i (spatialPartial i w) x⟫_ℝ) =
      -(∫ x, χ x * ‖spatialPartial i w x‖ ^ 2) +
        (1 / 2 : ℝ) * ∫ x, ‖w x‖ ^ 2 * spatialPartial i (spatialPartial i χ) x := by
  have hdw : ContDiff ℝ ∞ (spatialPartial i w) := spatial_partial_contDiff hw i
  have hdχ : ContDiff ℝ ∞ (spatialPartial i χ) := spatial_partial_contDiff hχ i
  have hi_cross : Integrable (fun x =>
      spatialPartial i χ x * ⟪w x, spatialPartial i w x⟫_ℝ) :=
    (hdχ.continuous.mul (hw.continuous.inner hdw.continuous)).integrable_of_hasCompactSupport
      (CompactEnergy.compact_partial hcχ i).mul_right
  have hi_grad := laplacian_integrable_weighted_partial_sq hχ.continuous hw hcχ i
  have hfirst := CompactEnergy.integral_inner_partial (hχ.smul hw) hdw hcχ.smul_right i
  have hfirst_rhs : (fun x =>
      ⟪spatialPartial i (fun y => χ y • w y) x, spatialPartial i w x⟫_ℝ) =
      (fun x => χ x * ‖spatialPartial i w x‖ ^ 2 +
        spatialPartial i χ x * ⟪w x, spatialPartial i w x⟫_ℝ) := by
    funext x
    rw [laplacian_partial_smul hχ hw i x, inner_add_left]
    simp only [real_inner_smul_left, real_inner_self_eq_norm_sq]
  change (∫ x, ⟪χ x • w x, spatialPartial i (spatialPartial i w) x⟫_ℝ) = -(∫ x, ⟪spatialPartial i (fun y => χ y • w y) x, spatialPartial i w x⟫_ℝ) at hfirst
  simp only [real_inner_smul_left] at hfirst
  rw [hfirst_rhs, integral_add hi_grad hi_cross] at hfirst
  have hsecond := CompactEnergy.integral_mul_partial hdχ (hw.norm_sq ℝ)
    (CompactEnergy.compact_partial hcχ i) i
  have hsecond_lhs : (fun x =>
      spatialPartial i χ x * spatialPartial i (fun y => ‖w y‖ ^ 2) x) =
      (fun x => 2 * (spatialPartial i χ x * ⟪w x, spatialPartial i w x⟫_ℝ)) := by
    funext x
    change spatialPartial i χ x * fderiv ℝ (fun y => ‖w y‖ ^ 2) x (coordinateVector i) = _
    rw [fderiv_normsq hw]
    dsimp only [spatialPartial]
    ring
  rw [hsecond_lhs, integral_const_mul] at hsecond
  linarith

/-- Compactly weighted Laplacian energy identity for an arbitrary smooth
spatial vector field. No global integrability assumption on the vector field
or its derivatives is needed. -/
theorem integral_weighted_laplacian {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (hcχ : HasCompactSupport χ) :
    (∫ x, χ x * ⟪w x, ∑ i : Fin 3, spatialPartial i (spatialPartial i w) x⟫_ℝ) =
      -(∫ x, χ x * ∑ i : Fin 3, ‖spatialPartial i w x‖ ^ 2) +
        (1 / 2 : ℝ) * ∫ x, ‖w x‖ ^ 2 *
          ∑ i : Fin 3, spatialPartial i (spatialPartial i χ) x := by
  have hi_left (i : Fin 3) : Integrable (fun x =>
      χ x * ⟪w x, spatialPartial i (spatialPartial i w) x⟫_ℝ) :=
    (hχ.continuous.mul (hw.continuous.inner
      (spatial_partial_contDiff (spatial_partial_contDiff hw i) i).continuous)).integrable_of_hasCompactSupport
      hcχ.mul_right
  simp only [inner_sum, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi_left i),
    integral_finsetSum _ (fun i _ => laplacian_integrable_weighted_partial_sq hχ.continuous hw hcχ i),
    integral_finsetSum _ (fun i _ => laplacian_integrable_cutoff_second_partial hχ hw.continuous hcχ i)]
  simp_rw [integral_weighted_second_partial hχ hw hcχ]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]

/-- The same identity in the velocity-field notation used by Navier--Stokes. -/
theorem integral_weighted_spatialLaplacian {χ : Space → ℝ} {w : VelocityField} {t : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ (fun x => w (t, x)))
    (hcχ : HasCompactSupport χ) :
    (∫ x, χ x * ⟪w (t, x), spatialLaplacian w t x⟫_ℝ) =
      -(∫ x, χ x * ∑ i : Fin 3, ‖spatialPartial i (fun y => w (t, y)) x‖ ^ 2) +
        (1 / 2 : ℝ) * ∫ x, ‖w (t, x)‖ ^ 2 *
          ∑ i : Fin 3, spatialPartial i (spatialPartial i χ) x := by
  exact integral_weighted_laplacian hχ hw hcχ

end NavierStokesR3.LocalizedDifferenceEnergy



noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff InnerProductSpace

namespace NavierStokesR3.LocalizedDifferenceEnergy

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness
open Comparison (weightedEnergy weightedEnergyRate weightedDissipation gradientSq)

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

private theorem infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)

/-- A continuous factor needs no decay when multiplied by the compact cutoff. -/
theorem integrable_cutoff_mul {χ f : Space → ℝ}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ) (hf : Continuous f) :
    Integrable (fun x => χ x * f x) :=
  (hχ.mul hf).integrable_of_hasCompactSupport hcχ.mul_right

theorem integrable_weighted_energy {χ : Space → ℝ} {w : VelocityField} {t : ℝ}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hw : Continuous (fun x : Space => w (t, x))) :
    Integrable (fun x : Space => χ x * ‖w (t, x)‖ ^ 2) :=
  integrable_cutoff_mul hχ hcχ (hw.norm.pow 2)



theorem weightedDissipation_nonneg {χ : Space → ℝ} (hχ : ∀ x, 0 ≤ χ x)
    (w : VelocityField) (t : ℝ) : 0 ≤ weightedDissipation χ w t :=
  integral_nonneg (fun x => mul_nonneg (hχ x)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- Energy is continuous on the closed slab, including its initial time. -/
theorem weightedEnergy_continuousOn {a b : ℝ} {χ : Space → ℝ} {w : VelocityField}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hw : ContDiffOn ℝ ∞ w (Comparison.slab a b)) :
    ContinuousOn (weightedEnergy χ w) (Icc a b) := by
  have hF : ContinuousOn (fun z : SpaceTime => χ z.2 * ‖w z‖ ^ 2)
      (Icc a b ×ˢ univ) :=
    (hχ.comp continuous_snd).continuousOn.mul (hw.continuousOn.norm.pow 2)
  apply CompactTimeIntegral.continuousOn_integral hcχ hF
  intro t ht x hx
  rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- Joint smoothness and the cutoff justify differentiation under the integral. -/
theorem weightedEnergy_hasDerivAt {a b t : ℝ} {χ : Space → ℝ} {w : VelocityField}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hw : ContDiffOn ℝ ∞ w (Comparison.slab a b)) (ht : t ∈ Ioo a b) :
    HasDerivAt (weightedEnergy χ w) (weightedEnergyRate χ w t) t := by
  have hF : ContDiffOn ℝ 1 (fun z : SpaceTime => χ z.2 * ‖w z‖ ^ 2)
      (Icc a b ×ˢ univ) :=
    (((hχ.comp contDiff_snd).contDiffOn).mul (hw.norm_sq ℝ)).of_le (nat_le_infty 1)
  refine CompactTimeIntegral.hasDerivAt_integral_of_contDiffOn_of_hasDerivAt hcχ hF ?_ ht ?_
  · intro r hr x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  · intro x
    exact (energy_density_derivative (time_differentiable_at_interior hw ht x)).const_mul (χ x)


/-- The localized balance follows from equality of the actual Navier--Stokes
residuals. No integrability or support condition is imposed on either velocity. -/
theorem difference_energy_balance {χ : Space → ℝ} {u v : VelocityField}
    {p q : PressureField} {t : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t, x)))
    (htu : ∀ x : Space, DifferentiableAt ℝ (fun r => u (r, x)) t)
    (htv : ∀ x : Space, DifferentiableAt ℝ (fun r => v (r, x)) t)
    (hdivu : ∀ x : Space, spatialDivergence u t x = 0)
    (hdivv : ∀ x : Space, spatialDivergence v t x = 0)
    (hNS : ∀ x : Space, ProblemStatement.navierStokesResidual 1 u p t x =
      ProblemStatement.navierStokesResidual 1 v q t x) :
    (1 / 2 : ℝ) * weightedEnergyRate χ (u - v) t + weightedDissipation χ (u - v) t =
      -(∫ x : Space, χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) +
      (1 / 2 : ℝ) * (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        ∑ i : Fin 3, spatialPartial i (spatialPartial i χ) x) +
      (1 / 2 : ℝ) * (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        fderiv ℝ χ x (v (t, x))) +
      ∫ x : Space, (p - q) (t, x) * fderiv ℝ χ x ((u - v) (t, x)) := by
  have hw : ContDiff ℝ ∞ (fun x : Space => (u - v) (t, x)) := hu.sub hv
  have hπ : ContDiff ℝ ∞ (fun x : Space => (p - q) (t, x)) := hp.sub hq
  have hdivw : ∀ x : Space, spatialDivergence (u - v) t x = 0 := by
    intro x
    rw [spatialDivergence_sub hu hv, hdivu x, hdivv x, sub_self]
  have hiL : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ) :=
    integrable_cutoff_mul hχ.continuous hcχ (hw.inner ℝ (spatialLaplacian_contDiff hw)).continuous
  have hiC : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) :=
    integrable_cutoff_mul hχ.continuous hcχ
      (hw.inner ℝ ((hu.fderiv_right infty_add_one_le).clm_apply hw)).continuous
  have hiT : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ) :=
    integrable_cutoff_mul hχ.continuous hcχ
      (hw.inner ℝ ((hw.fderiv_right infty_add_one_le).clm_apply hv)).continuous
  have hiP : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ) :=
    integrable_cutoff_mul hχ.continuous hcχ (hw.inner ℝ (pressureGradient_contDiff hπ)).continuous
  have hiLC : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
      χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) :=
    hiL.sub hiC
  have hiLCT : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
      χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ -
      χ x * ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ) :=
    hiLC.sub hiT
  have hEq : (fun x : Space => χ x *
      (2 * ⟪(u - v) (t, x), temporalDerivative (u - v) t x⟫_ℝ)) =
      (fun x : Space => 2 * (
        χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
        χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ -
        χ x * ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ -
        χ x * ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ)) := by
    funext x
    rw [difference_equation hu hv hp hq (htu x) (htv x) (by simpa using hNS x)]
    simp only [inner_sub_right]
    ring
  have hRate : weightedEnergyRate χ (u - v) t = 2 * (
      (∫ x : Space, χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ) -
      (∫ x : Space, χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) -
      (∫ x : Space, χ x * ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ) -
      ∫ x : Space, χ x * ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ) := by
    unfold weightedEnergyRate
    rw [hEq, integral_const_mul, integral_sub hiLCT hiP,
      integral_sub hiLC hiT, integral_sub hiL hiC]
  have hL := integral_weighted_spatialLaplacian hχ hw hcχ
  have hT := integral_weighted_transport hχ hw hv hcχ hdivv
  have hP : (∫ x : Space, χ x *
      ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ) =
      -(∫ x : Space, (p - q) (t, x) * fderiv ℝ χ x ((u - v) (t, x))) := by
    simp_rw [inner_pressureGradient]
    exact integral_weighted_pressure hχ hπ hw hcχ hdivw
  change (∫ x : Space, χ x *
    ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ) =
      -weightedDissipation χ (u - v) t +
      (1 / 2 : ℝ) * (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        ∑ i : Fin 3, spatialPartial i (spatialPartial i χ) x) at hL
  change (∫ x : Space, χ x *
    ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ) =
      -(1 / 2 : ℝ) * (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        fderiv ℝ χ x (v (t, x))) at hT
  rw [hL, hT, hP] at hRate
  rw [hRate]
  ring


end NavierStokesR3.LocalizedDifferenceEnergy
end

/-! Merged from `NavierStokes.R3.LocalizedFluxEstimates` (in a section, so its `open`s cannot leak). -/
section
/-!
# Non-pressure terms in the localized difference energy balance

The velocity difference need not have compact support or globally integrable
derivatives. The compact cutoff supplies local integrability; the estimates
use its weighted `L⁶` norm and the unweighted `L²` norm of the difference.
-/


noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff BigOperators InnerProductSpace

namespace NavierStokesR3.LocalizedFluxEstimates

open ProblemStatement Comparison
open NavierStokes.ProblemStatement (spatialDerivative coordinateVector)
open NavierStokes.PeriodicIntegration (spatialPartial)

/-- The cutoff makes the coupling integral finite. -/
theorem coupling_integrable {χ : Space → ℝ} {u w : VelocityField} {t : ℝ}
    (hχ : Continuous χ) (hs : HasCompactSupport χ)
    (hu : ContDiff ℝ 1 (fun x => u (t, x)))
    (hw : Continuous (fun x => w (t, x))) :
    Integrable (fun x => χ x *
      ⟪w (t, x), spatialDerivative u t x (w (t, x))⟫_ℝ) volume := by
  apply LocalizedDifferenceEnergy.integrable_cutoff_mul hχ hs
  exact hw.inner ((hu.continuous_fderiv (by simp)).clm_apply hw)

/-- The indefinite coupling is controlled by the gradient of the reference
velocity and the actual compactly weighted energy. -/
theorem neg_coupling_le_weightedEnergy {χ : Space → ℝ} {u w : VelocityField} {t G : ℝ}
    (hχ : Continuous χ) (hs : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hu : ContDiff ℝ 1 (fun x => u (t, x)))
    (hw : Continuous (fun x => w (t, x)))
    (hG : ∀ x, ‖spatialDerivative u t x‖ ≤ G) :
    -(∫ x, χ x * ⟪w (t, x), spatialDerivative u t x (w (t, x))⟫_ℝ) ≤
      G * weightedEnergy χ w t := by
  have hi := coupling_integrable hχ hs hu hw
  have he := LocalizedDifferenceEnergy.integrable_weighted_energy hχ hs hw
  rw [← integral_neg]
  change (∫ x, -(χ x * ⟪w (t, x), spatialDerivative u t x (w (t, x))⟫_ℝ)) ≤
    G * (∫ x, χ x * ‖w (t, x)‖ ^ 2)
  rw [← integral_const_mul]
  apply integral_mono hi.neg (he.const_mul G)
  intro x
  change -(χ x * ⟪w (t, x), spatialDerivative u t x (w (t, x))⟫_ℝ) ≤
    G * (χ x * ‖w (t, x)‖ ^ 2)
  have h := NavierStokes.PeriodicUniqueness.nonlinear_energy_bound
    (spatialDerivative u t x) (w (t, x)) (hG x)
  nlinarith [mul_le_mul_of_nonneg_left h (hχ0 x)]

/-- Derivative of the energy weight. -/
theorem fderiv_cutoff_eight {φ : Space → ℝ} {x : Space}
    (hφ : DifferentiableAt ℝ φ x) :
    fderiv ℝ (fun y => φ y ^ 8) x = (8 * φ x ^ 7) • fderiv ℝ φ x := by
  simpa only [Function.comp_def, Nat.cast_ofNat, Nat.reduceSub] using
    ((hasDerivAt_pow 8 (φ x)).comp_hasFDerivAt x hφ.hasFDerivAt).fderiv

/-- One power of the cutoff is harmless because it lies in `[0,1]`. -/
theorem norm_fderiv_cutoff_eight_apply_le {φ : Space → ℝ} {x : Space}
    (hφ : DifferentiableAt ℝ φ x) (hφ0 : 0 ≤ φ x) (hφ1 : φ x ≤ 1)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ‖fderiv ℝ φ x‖ ≤ L) (z : Space) :
    ‖fderiv ℝ (fun y => φ y ^ 8) x z‖ ≤ (8 * L) * φ x ^ 6 * ‖z‖ := by
  have h76 : φ x ^ 7 ≤ φ x ^ 6 := by
    calc
      φ x ^ 7 = φ x ^ 6 * φ x := by ring
      _ ≤ φ x ^ 6 * 1 := mul_le_mul_of_nonneg_left hφ1 (pow_nonneg hφ0 6)
      _ = φ x ^ 6 := mul_one _
  have hd : ‖fderiv ℝ φ x z‖ ≤ L * ‖z‖ :=
    ((fderiv ℝ φ x).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg z))
  rw [fderiv_cutoff_eight hφ, _root_.smul_apply, smul_eq_mul,
    norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 8 * φ x ^ 7)]
  calc
    (8 * φ x ^ 7) * ‖fderiv ℝ φ x z‖ ≤ (8 * φ x ^ 7) * (L * ‖z‖) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = φ x ^ 7 * ((8 * L) * ‖z‖) := by ring
    _ ≤ φ x ^ 6 * ((8 * L) * ‖z‖) :=
      mul_le_mul_of_nonneg_right h76 (by positivity)
    _ = (8 * L) * φ x ^ 6 * ‖z‖ := by ring

/-- The reference velocity vanishes in the cutoff derivative, leaving only
the difference velocity in the transport flux. -/
theorem transport_flux_bound {φ : Space → ℝ} {u v : VelocityField} {t : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ)
    (hu : Continuous (fun x => u (t, x))) (hv : Continuous (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x, ‖fderiv ℝ φ x‖ ≤ L)
    (hvanish : ∀ x, fderiv ℝ (fun y => φ y ^ 8) x (u (t, x)) = 0) :
    Integrable (fun x => ‖(u - v) (t, x)‖ ^ 2 *
      fderiv ℝ (fun y => φ y ^ 8) x (v (t, x))) volume ∧
    |∫ x, ‖(u - v) (t, x)‖ ^ 2 * fderiv ℝ (fun y => φ y ^ 8) x (v (t, x))| ≤
      (8 * L) * comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
        cutoffL6 φ (u - v) t ^ (3 / 2 : ℝ) := by
  have hw : Continuous (fun x => (u - v) (t, x)) := hu.sub hv
  have hweighted := WeightedSobolev.memLp_cutoff_pow_smul hφ.continuous hs hw
    (by norm_num : (4 : ℕ) ≠ 0) 6
  obtain ⟨hT, hTb⟩ := WeightedInterpolation.cutoff_transport_bound
    hφ.continuous.aestronglyMeasurable hφ0 hw2 hweighted
  have hswitch (x : Space) : fderiv ℝ (fun y => φ y ^ 8) x (v (t, x)) =
      -fderiv ℝ (fun y => φ y ^ 8) x ((u - v) (t, x)) := by
    simp only [Pi.sub_apply, map_sub, hvanish x, zero_sub, neg_neg]
  have hbound (x : Space) :
      ‖‖(u - v) (t, x)‖ ^ 2 * fderiv ℝ (fun y => φ y ^ 8) x (v (t, x))‖ ≤
        (8 * L) * (φ x ^ 6 * ‖(u - v) (t, x)‖ ^ 3) := by
    rw [norm_mul, norm_pow, norm_norm, hswitch, norm_neg]
    calc
      ‖(u - v) (t, x)‖ ^ 2 *
          ‖fderiv ℝ (fun y => φ y ^ 8) x ((u - v) (t, x))‖ ≤
          ‖(u - v) (t, x)‖ ^ 2 * ((8 * L) * φ x ^ 6 * ‖(u - v) (t, x)‖) :=
        mul_le_mul_of_nonneg_left
          (norm_fderiv_cutoff_eight_apply_le (hφ.differentiable (by simp) x)
            (hφ0 x) (hφ1 x) hL0 (hL x) _) (sq_nonneg _)
      _ = _ := by ring
  have hmajor := hT.const_mul (8 * L)
  have hflux : Continuous (fun x => ‖(u - v) (t, x)‖ ^ 2 *
      fderiv ℝ (fun y => φ y ^ 8) x (v (t, x))) :=
    (hw.norm.pow 2).mul (((hφ.pow 8).continuous_fderiv (by simp)).clm_apply hv)
  refine ⟨hmajor.mono' hflux.aestronglyMeasurable (Eventually.of_forall hbound), ?_⟩
  calc
    |∫ x, ‖(u - v) (t, x)‖ ^ 2 * fderiv ℝ (fun y => φ y ^ 8) x (v (t, x))| ≤
        ∫ x, (8 * L) * (φ x ^ 6 * ‖(u - v) (t, x)‖ ^ 3) :=
      norm_integral_le_of_norm_le hmajor (Eventually.of_forall hbound)
    _ = (8 * L) * (∫ x, φ x ^ 6 * ‖(u - v) (t, x)‖ ^ 3) := integral_const_mul _ _
    _ ≤ (8 * L) * (comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
        cutoffL6 φ (u - v) t ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hTb (by positivity)
    _ = _ := by ring

theorem continuous_laplacian {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    Continuous (ComparisonCutoffs.laplacian χ) := by
  unfold ComparisonCutoffs.laplacian
  exact continuous_finsetSum _ fun i _ =>
    (NavierStokes.PeriodicUniqueness.spatial_partial_contDiff
      (NavierStokes.PeriodicUniqueness.spatial_partial_contDiff hχ i) i).continuous

/-- A bounded Laplacian can be paired with any square-integrable field. -/
theorem laplacian_flux_bound {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw2 : MemLp w 2 volume) {K : ℝ}
    (hK : ∀ x, ‖ComparisonCutoffs.laplacian χ x‖ ≤ K) :
    Integrable (fun x => ‖w x‖ ^ 2 * ComparisonCutoffs.laplacian χ x) volume ∧
      |∫ x, ‖w x‖ ^ 2 * ComparisonCutoffs.laplacian χ x| ≤ K * comparisonLpNorm 2 w ^ 2 := by
  have hsquare : Integrable (fun x => ‖w x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hw2.aestronglyMeasurable).mp hw2
  have hmajor := hsquare.const_mul K
  have hbound (x : Space) : ‖‖w x‖ ^ 2 * ComparisonCutoffs.laplacian χ x‖ ≤
      K * ‖w x‖ ^ 2 := by
    rw [norm_mul, norm_pow, norm_norm]
    exact (mul_le_mul_of_nonneg_left (hK x) (sq_nonneg _)).trans_eq (mul_comm _ _)
  have hmeas : AEStronglyMeasurable
      (fun x => ‖w x‖ ^ 2 * ComparisonCutoffs.laplacian χ x) volume :=
    (hw2.aestronglyMeasurable.norm.pow 2).mul (continuous_laplacian hχ).aestronglyMeasurable
  refine ⟨hmajor.mono' hmeas (Eventually.of_forall hbound), ?_⟩
  calc
    |∫ x, ‖w x‖ ^ 2 * ComparisonCutoffs.laplacian χ x| ≤ ∫ x, K * ‖w x‖ ^ 2 :=
      norm_integral_le_of_norm_le hmajor (Eventually.of_forall hbound)
    _ = K * l2Sq w := integral_const_mul _ _
    _ = K * comparisonLpNorm 2 w ^ 2 := by rw [← LpNormTools.lpNorm_two_sq_eq_l2Sq hw2]

private def baseWeight (x : Space) : ℝ := ComparisonCutoffs.baseCutoff x ^ 8

private theorem baseWeight_smooth : ContDiff ℝ ∞ baseWeight :=
  ComparisonCutoffs.baseCutoff_smooth.pow 8

private theorem baseWeight_hasCompactSupport : HasCompactSupport baseWeight :=
  ComparisonCutoffs.baseCutoff_hasCompactSupport.comp_left
    (g := fun r : ℝ => r ^ 8) (by norm_num)

private theorem exists_weight_second_derivative_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Space, ‖iteratedFDeriv ℝ 2 baseWeight x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (baseWeight_hasCompactSupport.iteratedFDeriv 2).exists_bound_of_continuous
    (ContDiff.continuous_iteratedFDeriv le_rfl (contDiff_infty.1 baseWeight_smooth 2))
  exact ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun x => (hC x).trans (le_max_right _ _)⟩

/-- A fixed derivative bound for the unscaled energy weight. -/
def weightSecondDerivativeConstant : ℝ := Classical.choose exists_weight_second_derivative_bound

theorem weightSecondDerivativeConstant_pos : 0 < weightSecondDerivativeConstant :=
  (Classical.choose_spec exists_weight_second_derivative_bound).1

private theorem baseWeight_iteratedFDeriv_two_le (x : Space) :
    ‖iteratedFDeriv ℝ 2 baseWeight x‖ ≤ weightSecondDerivativeConstant :=
  (Classical.choose_spec exists_weight_second_derivative_bound).2 x

private def weightDilation (R : ℝ) : Space →L[ℝ] Space :=
  R⁻¹ • ContinuousLinearMap.id ℝ Space

private theorem norm_weightDilation_le {R : ℝ} (hR : 0 < R) :
    ‖weightDilation R‖ ≤ R⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hR.le)
  intro x
  change ‖R⁻¹ • x‖ ≤ R⁻¹ * ‖x‖
  rw [ComparisonCutoffs.norm_scaled hR, div_eq_inv_mul]

/-- Apply scaling to the fixed eighth-power weight before estimating its
derivatives. The second derivative has the same inverse-square scaling. -/
theorem weight_iteratedFDeriv_two_le {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖iteratedFDeriv ℝ 2 (ComparisonCutoffs.weight R) x‖ ≤
      weightSecondDerivativeConstant / R ^ 2 := by
  change ‖iteratedFDeriv ℝ 2 (baseWeight ∘ weightDilation R) x‖ ≤ _
  rw [(weightDilation R).iteratedFDeriv_comp_right
    (contDiff_infty.1 baseWeight_smooth 2) x le_rfl]
  calc
    ‖(iteratedFDeriv ℝ 2 baseWeight (weightDilation R x)).compContinuousLinearMap
        (fun _ => weightDilation R)‖ ≤
        ‖iteratedFDeriv ℝ 2 baseWeight (weightDilation R x)‖ *
          ∏ _ : Fin 2, ‖weightDilation R‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ 2 baseWeight (weightDilation R x)‖ * (R⁻¹) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        ∏ _ : Fin 2, ‖weightDilation R‖ ≤ ∏ _ : Fin 2, R⁻¹ := by
          gcongr with i _
          exact norm_weightDilation_le hR
        _ = (R⁻¹) ^ 2 := by simp
    _ ≤ weightSecondDerivativeConstant * (R⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_right (baseWeight_iteratedFDeriv_two_le _) (by positivity)
    _ = weightSecondDerivativeConstant / R ^ 2 := by simp [div_eq_mul_inv]

theorem weight_second_fderiv_le {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖fderiv ℝ (fderiv ℝ (ComparisonCutoffs.weight R)) x‖ ≤
      weightSecondDerivativeConstant / R ^ 2 := by
  have hn := norm_iteratedFDeriv_fderiv (𝕜 := ℝ)
    (f := fderiv ℝ (ComparisonCutoffs.weight R)) (x := x) (n := 0)
  simp only [norm_iteratedFDeriv_zero] at hn
  rw [hn, norm_iteratedFDeriv_fderiv]
  exact weight_iteratedFDeriv_two_le hR x

/-- The fixed constant in the inverse-square Laplacian estimate. -/
def weightLaplacianConstant : ℝ := 3 * weightSecondDerivativeConstant

theorem weightLaplacianConstant_pos : 0 < weightLaplacianConstant :=
  mul_pos (by norm_num) weightSecondDerivativeConstant_pos

theorem weight_laplacian_le {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖ComparisonCutoffs.laplacian (ComparisonCutoffs.weight R) x‖ ≤
      weightLaplacianConstant / R ^ 2 := by
  calc
    ‖ComparisonCutoffs.laplacian (ComparisonCutoffs.weight R) x‖ ≤
        ∑ i : Fin 3, ‖spatialPartial i (spatialPartial i (ComparisonCutoffs.weight R)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, weightSecondDerivativeConstant / R ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        (ComparisonCutoffs.norm_partial_partial_le (ComparisonCutoffs.weight_smooth R)
          i i x).trans (weight_second_fderiv_le hR x)
    _ = weightLaplacianConstant / R ^ 2 := by
      simp [weightLaplacianConstant, mul_div_assoc]

/-- The Laplacian term in the energy identity is of order `R⁻² M²`.
Finiteness is explicit and only requires `L²` membership of the velocity. -/
theorem weight_laplacian_flux_bound {R : ℝ} (hR : 0 < R) {w : VelocityField} {t : ℝ}
    (hw2 : MemLp (fun x => w (t, x)) 2 volume) :
    Integrable (fun x => ‖w (t, x)‖ ^ 2 *
      ∑ i : Fin 3, spatialPartial i (spatialPartial i (ComparisonCutoffs.weight R)) x) volume ∧
      |∫ x, ‖w (t, x)‖ ^ 2 *
        ∑ i : Fin 3, spatialPartial i (spatialPartial i (ComparisonCutoffs.weight R)) x| ≤
          (weightLaplacianConstant / R ^ 2) * comparisonLpNorm 2 (fun x => w (t, x)) ^ 2 :=
  laplacian_flux_bound (ComparisonCutoffs.weight_smooth R) hw2 (weight_laplacian_le hR)

end NavierStokesR3.LocalizedFluxEstimates
end

/-! Merged from `NavierStokes.R3.ComparisonYoung` (in a section, so its `open`s cannot leak). -/
section
/-!
# Scalar absorption for the whole-space comparison estimate

The constants in these estimates are uniform in the cutoff radius and in the
nonnegative quantity that will represent a weighted gradient norm. All
fractional powers have real exponents.
-/


noncomputable section

open Filter

namespace NavierStokesR3.ComparisonYoung

/-- Every nonnegative subquadratic power can be absorbed into an arbitrarily
small multiple of the square, with a constant independent of the argument. -/
theorem exists_rpow_absorption {C δ p : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hp0 : 0 ≤ p) (hp2 : p < 2) :
    ∃ D ≥ 0, ∀ A ≥ 0, C * A ^ p ≤ δ * A ^ 2 + D := by
  have hevent : ∀ᶠ A : ℝ in atTop, C / δ ≤ A ^ (2 - p) :=
    (tendsto_rpow_atTop (by linarith : 0 < 2 - p)).eventually
      (eventually_ge_atTop (C / δ))
  obtain ⟨b, hb⟩ := eventually_atTop.mp hevent
  let K : ℝ := max 1 b
  have hK : 0 ≤ K := le_trans zero_le_one (le_max_left _ _)
  have hD : 0 ≤ C * K ^ p := mul_nonneg hC (Real.rpow_nonneg hK _)
  refine ⟨C * K ^ p, hD, ?_⟩
  intro A hA
  by_cases hAK : A ≤ K
  · calc
      C * A ^ p ≤ C * K ^ p :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hA hAK hp0) hC
      _ ≤ δ * A ^ 2 + C * K ^ p :=
        le_add_of_nonneg_left (mul_nonneg hδ.le (sq_nonneg A))
  · have hKA : K ≤ A := le_of_lt (lt_of_not_ge hAK)
    have hApos : 0 < A := lt_of_lt_of_le zero_lt_one
      ((le_max_left 1 b).trans hKA)
    have hlarge : C ≤ A ^ (2 - p) * δ :=
      (div_le_iff₀ hδ).mp (hb A ((le_max_right 1 b).trans hKA))
    have hpow : A ^ (2 - p) * A ^ p = A ^ 2 := by
      rw [← Real.rpow_add hApos]
      norm_num
    calc
      C * A ^ p ≤ (A ^ (2 - p) * δ) * A ^ p :=
        mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hA _)
      _ = δ * (A ^ (2 - p) * A ^ p) := by ring
      _ = δ * A ^ 2 := by rw [hpow]
      _ ≤ δ * A ^ 2 + C * K ^ p := le_add_of_nonneg_right hD

/-- The same absorption estimate is uniform for a fixed unit shift. -/
theorem exists_shifted_rpow_absorption {C δ p : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hp0 : 0 ≤ p) (hp2 : p < 2) :
    ∃ D ≥ 0, ∀ A ≥ 0, C * (A + 1) ^ p ≤ δ * A ^ 2 + D := by
  obtain ⟨D, hD, hbound⟩ := exists_rpow_absorption hC (half_pos hδ) hp0 hp2
  refine ⟨D + δ, add_nonneg hD hδ.le, ?_⟩
  intro A hA
  have hboundA := hbound (A + 1) (by linarith)
  have hsquare : (A + 1) ^ 2 ≤ 2 * A ^ 2 + 2 := by
    nlinarith [sq_nonneg (A - 1)]
  have hscaled := mul_le_mul_of_nonneg_left hsquare (half_pos hδ).le
  nlinarith

/-- Dividing the shifted estimate by a radius at least one preserves the
arbitrarily small square coefficient and makes the constant decay as `1 / R`. -/
theorem exists_scaled_shifted_rpow_absorption {C δ p : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hp0 : 0 ≤ p) (hp2 : p < 2) :
    ∃ D ≥ 0, ∀ A ≥ 0, ∀ R ≥ 1,
      C / R * (A + 1) ^ p ≤ δ * A ^ 2 + D / R := by
  obtain ⟨D, hD, hbound⟩ := exists_shifted_rpow_absorption hC hδ hp0 hp2
  refine ⟨D, hD, ?_⟩
  intro A hA R hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hInv : 0 ≤ R⁻¹ := (inv_pos.mpr hRpos).le
  have hInv1 : R⁻¹ ≤ 1 := (inv_le_one₀ hRpos).mpr hR
  have hscaled := mul_le_mul_of_nonneg_right (hbound A hA) hInv
  have hquadratic := mul_le_mul_of_nonneg_left hInv1
    (mul_nonneg hδ.le (sq_nonneg A))
  simp only [div_eq_mul_inv]
  nlinarith

/-- The pressure and transport cutoff remainders are controlled by one shifted
subquadratic power. The estimate retains the full factor `1 / R`. -/
theorem cutoff_expression_le {C A R : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hR : 1 ≤ R) :
    C * ((A + R⁻¹) ^ (1 / 2 : ℝ) + 1) *
        (R⁻¹ * A + R ^ (-2 : ℝ)) +
      C * R ^ (-7 / 4 : ℝ) * (A + R⁻¹) ^ (3 / 4 : ℝ) +
      C * R⁻¹ * (A + R⁻¹) ^ (3 / 2 : ℝ) ≤
        4 * C / R * (A + 1) ^ (3 / 2 : ℝ) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hInv : 0 ≤ R⁻¹ := (inv_pos.mpr hRpos).le
  have hInv1 : R⁻¹ ≤ 1 := (inv_le_one₀ hRpos).mpr hR
  have hx : 0 ≤ A + R⁻¹ := add_nonneg hA hInv
  have hxB : A + R⁻¹ ≤ A + 1 := add_le_add_right hInv1 A
  have hB1 : 1 ≤ A + 1 := by linarith
  have hBpos : 0 < A + 1 := by linarith
  have hR2 : R ^ (-2 : ℝ) ≤ R⁻¹ := by
    simpa only [Real.rpow_neg_one] using
      (Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (-2 : ℝ) ≤ -1))
  have hR74 : R ^ (-7 / 4 : ℝ) ≤ R⁻¹ := by
    simpa only [Real.rpow_neg_one] using
      (Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (-7 / 4 : ℝ) ≤ -1))
  have hhalf : (A + R⁻¹) ^ (1 / 2 : ℝ) + 1 ≤
      2 * (A + 1) ^ (1 / 2 : ℝ) := by
    have hmon := Real.rpow_le_rpow hx hxB (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hone := Real.one_le_rpow hB1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  have hlinear : R⁻¹ * A + R ^ (-2 : ℝ) ≤ R⁻¹ * (A + 1) := by
    nlinarith
  have hlinear0 : 0 ≤ R⁻¹ * A + R ^ (-2 : ℝ) :=
    add_nonneg (mul_nonneg hInv hA) (Real.rpow_nonneg hRpos.le _)
  have hprod : (A + 1) ^ (1 / 2 : ℝ) * (A + 1) =
      (A + 1) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add_one hBpos.ne']
    norm_num
  have hfactor : ((A + R⁻¹) ^ (1 / 2 : ℝ) + 1) *
      (R⁻¹ * A + R ^ (-2 : ℝ)) ≤ 2 * R⁻¹ * (A + 1) ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ (2 * (A + 1) ^ (1 / 2 : ℝ)) * (R⁻¹ * (A + 1)) :=
        mul_le_mul hhalf hlinear hlinear0
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hBpos.le _))
      _ = 2 * R⁻¹ * ((A + 1) ^ (1 / 2 : ℝ) * (A + 1)) := by ring
      _ = _ := by rw [hprod]
  have hthreeQuarters : (A + R⁻¹) ^ (3 / 4 : ℝ) ≤
      (A + 1) ^ (3 / 2 : ℝ) :=
    (Real.rpow_le_rpow hx hxB (by norm_num : (0 : ℝ) ≤ 3 / 4)).trans
      (Real.rpow_le_rpow_of_exponent_le hB1
        (by norm_num : (3 / 4 : ℝ) ≤ 3 / 2))
  have hthreeHalves : (A + R⁻¹) ^ (3 / 2 : ℝ) ≤
      (A + 1) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hx hxB (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hterm1 := mul_le_mul_of_nonneg_left hfactor hC
  have hterm2 := mul_le_mul_of_nonneg_left
    (mul_le_mul hR74 hthreeQuarters (Real.rpow_nonneg hx _) hInv) hC
  have hterm3 := mul_le_mul_of_nonneg_left hthreeHalves (mul_nonneg hC hInv)
  simp only [div_eq_mul_inv]
  nlinarith only [hterm1, hterm2, hterm3]

/-- Scalar Young absorption of all cutoff remainders. The same nonnegative
constant works for every nonnegative gradient norm and every radius at least
one. -/
theorem exists_cutoff_absorption {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ D ≥ 0, ∀ A ≥ 0, ∀ R ≥ 1,
      C * ((A + R⁻¹) ^ (1 / 2 : ℝ) + 1) *
          (R⁻¹ * A + R ^ (-2 : ℝ)) +
        C * R ^ (-7 / 4 : ℝ) * (A + R⁻¹) ^ (3 / 4 : ℝ) +
        C * R⁻¹ * (A + R⁻¹) ^ (3 / 2 : ℝ) ≤
          δ * A ^ 2 + D / R := by
  obtain ⟨D, hD, hbound⟩ := exists_scaled_shifted_rpow_absorption
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC) hδ
    (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num : (3 / 2 : ℝ) < 2)
  exact ⟨D, hD, fun A hA R hR =>
    (cutoff_expression_le hC hA hR).trans (hbound A hA R hR)⟩

end NavierStokesR3.ComparisonYoung
end

/-! Merged from `NavierStokes.R3.ComparisonRateBound`. -/
/-!
# A uniform rate bound from the localized energy estimate

The Sobolev estimate for the cutoff velocity contains fixed multiplicative
constants. They are absorbed into a single coefficient before applying the
uniform Young estimate. The resulting error decays as `1 / R`, and no sign
condition on the energy coefficient or energy value is used.
-/


noncomputable section

namespace NavierStokesR3.ComparisonRateBound

private theorem rpow_le_square_mul_rpow {B Q x p : ℝ}
    (hB : 0 ≤ B) (hx : 0 ≤ x) (hQ : 1 ≤ Q) (hBQ : B ≤ Q * x)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2) :
    B ^ p ≤ Q ^ 2 * x ^ p := by
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  calc
    B ^ p ≤ (Q * x) ^ p := Real.rpow_le_rpow hB hBQ hp0
    _ = Q ^ p * x ^ p := Real.mul_rpow hQ0 hx
    _ ≤ Q ^ (2 : ℝ) * x ^ p := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hQ hp2) (Real.rpow_nonneg hx _)
    _ = Q ^ 2 * x ^ p := by rw [Real.rpow_two]

/-- Fixed constants in the cutoff Sobolev estimate preserve uniform absorption
of the full pressure and transport error. -/
theorem exists_uniform_flux_absorption {C1 C2 S M δ : ℝ}
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hS : 0 ≤ S) (hM : 0 ≤ M)
    (hδ : 0 < δ) :
    ∃ D ≥ 0, ∀ R ≥ 1, ∀ A ≥ 0, ∀ B ≥ 0, B ≤ S * (A + M / R) →
      C1 / R * B ^ (3 / 2 : ℝ) +
        C2 * ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) +
          R ^ (-7 / 4 : ℝ) * B ^ (3 / 4 : ℝ)) ≤ δ * A ^ 2 + D / R := by
  let Q : ℝ := max 1 (S * max 1 M)
  have hQ1 : 1 ≤ Q := le_max_left _ _
  have hSQ : S ≤ Q := by
    calc
      S = S * 1 := by ring
      _ ≤ S * max 1 M := mul_le_mul_of_nonneg_left (le_max_left _ _) hS
      _ ≤ Q := le_max_right _ _
  have hSMQ : S * M ≤ Q :=
    (mul_le_mul_of_nonneg_left (le_max_right 1 M) hS).trans (le_max_right _ _)
  have hQ0 : 0 ≤ Q := (mul_nonneg hS hM).trans hSMQ
  have hQsq1 : 1 ≤ Q ^ 2 := by nlinarith [sq_nonneg (Q - 1)]
  let C : ℝ := (C1 + C2) * Q ^ 2
  have hC : 0 ≤ C := mul_nonneg (add_nonneg hC1 hC2) (sq_nonneg _)
  have hC1Q : C1 * Q ^ 2 ≤ C :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC2) (sq_nonneg _)
  have hC2Q : C2 * Q ^ 2 ≤ C :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC1) (sq_nonneg _)
  obtain ⟨D, hD, hD_bound⟩ := ComparisonYoung.exists_cutoff_absorption hC hδ
  refine ⟨D, hD, ?_⟩
  intro R hR A hA B hB hSobolev
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hInv : 0 ≤ R⁻¹ := (inv_pos.mpr hRpos).le
  let x : ℝ := A + R⁻¹
  have hx : 0 ≤ x := add_nonneg hA hInv
  have hBQ : B ≤ Q * x := by
    calc
      B ≤ S * (A + M / R) := hSobolev
      _ = S * A + (S * M) * R⁻¹ := by ring
      _ ≤ Q * A + Q * R⁻¹ := add_le_add
        (mul_le_mul_of_nonneg_right hSQ hA)
        (mul_le_mul_of_nonneg_right hSMQ hInv)
      _ = Q * x := by dsimp [x]; ring
  have hhalf : B ^ (1 / 2 : ℝ) ≤ Q ^ 2 * x ^ (1 / 2 : ℝ) :=
    rpow_le_square_mul_rpow hB hx hQ1 hBQ (by norm_num) (by norm_num)
  have hthree : B ^ (3 / 2 : ℝ) ≤ Q ^ 2 * x ^ (3 / 2 : ℝ) :=
    rpow_le_square_mul_rpow hB hx hQ1 hBQ (by norm_num) (by norm_num)
  have hquarter : B ^ (3 / 4 : ℝ) ≤ Q ^ 2 * x ^ (3 / 4 : ℝ) :=
    rpow_le_square_mul_rpow hB hx hQ1 hBQ (by norm_num) (by norm_num)
  have hhalfOne : B ^ (1 / 2 : ℝ) + 1 ≤ Q ^ 2 * (x ^ (1 / 2 : ℝ) + 1) := by
    calc
      _ ≤ Q ^ 2 * x ^ (1 / 2 : ℝ) + Q ^ 2 := add_le_add hhalf hQsq1
      _ = _ := by ring
  have hfactor : C2 * (B ^ (1 / 2 : ℝ) + 1) ≤ C * (x ^ (1 / 2 : ℝ) + 1) := by
    calc
      _ ≤ C2 * (Q ^ 2 * (x ^ (1 / 2 : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hhalfOne hC2
      _ = (C2 * Q ^ 2) * (x ^ (1 / 2 : ℝ) + 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC2Q (by positivity)
  have hRminus2 : R ^ (-2 : ℝ) = 1 / R ^ 2 := by
    rw [Real.rpow_neg hRpos.le, Real.rpow_two, one_div]
  have hlinear : A / R + 1 / R ^ 2 = R⁻¹ * A + R ^ (-2 : ℝ) := by
    rw [hRminus2]
    ring
  have hlinear0 : 0 ≤ R⁻¹ * A + R ^ (-2 : ℝ) :=
    add_nonneg (mul_nonneg hInv hA) (Real.rpow_nonneg hRpos.le _)
  have hpressure : C2 * ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2)) ≤
      C * (x ^ (1 / 2 : ℝ) + 1) * (R⁻¹ * A + R ^ (-2 : ℝ)) := by
    rw [hlinear, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hfactor hlinear0
  have hcommutator : C2 * (R ^ (-7 / 4 : ℝ) * B ^ (3 / 4 : ℝ)) ≤
      C * R ^ (-7 / 4 : ℝ) * x ^ (3 / 4 : ℝ) := by
    calc
      _ = (C2 * R ^ (-7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ) := by ring
      _ ≤ (C2 * R ^ (-7 / 4 : ℝ)) * (Q ^ 2 * x ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hquarter (mul_nonneg hC2 (Real.rpow_nonneg hRpos.le _))
      _ = (C2 * Q ^ 2) * (R ^ (-7 / 4 : ℝ) * x ^ (3 / 4 : ℝ)) := by ring
      _ ≤ C * (R ^ (-7 / 4 : ℝ) * x ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right hC2Q (by positivity)
      _ = _ := by ring
  have htransport : C1 / R * B ^ (3 / 2 : ℝ) ≤
      C * R⁻¹ * x ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ C1 / R * (Q ^ 2 * x ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hthree (div_nonneg hC1 hRpos.le)
      _ = (C1 * Q ^ 2) * (R⁻¹ * x ^ (3 / 2 : ℝ)) := by ring
      _ ≤ C * (R⁻¹ * x ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hC1Q (by positivity)
      _ = _ := by ring
  have hsum : C1 / R * B ^ (3 / 2 : ℝ) +
      C2 * ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) +
        R ^ (-7 / 4 : ℝ) * B ^ (3 / 4 : ℝ)) ≤
      C * (x ^ (1 / 2 : ℝ) + 1) * (R⁻¹ * A + R ^ (-2 : ℝ)) +
        C * R ^ (-7 / 4 : ℝ) * x ^ (3 / 4 : ℝ) +
        C * R⁻¹ * x ^ (3 / 2 : ℝ) := by
    nlinarith only [hpressure, hcommutator, htransport]
  exact hsum.trans (hD_bound A hA R hR)

/-- One radius-independent constant turns the full localized energy inequality
into the differential inequality required by Gronwall. -/
theorem exists_uniform_rate_bound {C0 C1 C2 S M : ℝ}
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hS : 0 ≤ S) (hM : 0 ≤ M) :
    ∃ D ≥ 0, ∀ R ≥ 1, ∀ A ≥ 0, ∀ B ≥ 0, B ≤ S * (A + M / R) →
      ∀ E E' G : ℝ,
        (1 / 2 : ℝ) * E' + A ^ 2 ≤ G * E + C0 / R ^ 2 +
          C1 / R * B ^ (3 / 2 : ℝ) +
          C2 * ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) +
            R ^ (-7 / 4 : ℝ) * B ^ (3 / 4 : ℝ)) →
        E' ≤ 2 * G * E + D / R := by
  obtain ⟨D, hD, hflux⟩ := exists_uniform_flux_absorption hC1 hC2 hS hM
    (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨2 * (C0 + D), by positivity, ?_⟩
  intro R hR A hA B hB hSobolev E E' G henergy
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hRsq : R ≤ R ^ 2 := by nlinarith [sq_nonneg (R - 1)]
  have hC0radius : C0 / R ^ 2 ≤ C0 / R :=
    div_le_div_of_nonneg_left hC0 hRpos hRsq
  have hbound := hflux R hR A hA B hB hSobolev
  have hdivide : 2 * (C0 + D) / R = 2 * (C0 / R + D / R) := by ring
  rw [hdivide]
  nlinarith only [henergy, hbound, hC0radius, sq_nonneg A]

end NavierStokesR3.ComparisonRateBound


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

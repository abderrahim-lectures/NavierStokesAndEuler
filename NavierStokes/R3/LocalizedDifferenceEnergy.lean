import NavierStokes.R3.CompactEnergy
import NavierStokes.R3.ComparisonSetup
import NavierStokes.R3.LocalizedTransport

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

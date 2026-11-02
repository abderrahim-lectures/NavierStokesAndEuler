import NavierStokes.R3.ComparisonCutoffs
import NavierStokes.R3.WeightedSobolev
import NavierStokes.R3.PressureRecoveryHelpers
import NavierStokes.R3.RieszTestOperators
import NavierStokes.R3.PressureRecovery
import NavierStokes.R3.LocalizedTransport
import NavierStokes.R3.PressureFunctionals
import NavierStokes.R3.RieszLinearityDecay
import NavierStokes.R3.HeatKernelCommutator
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Canonical pressure flux

The pressure is paired with compact smooth tests through its canonical Riesz
functional. Every integral used to split the weighted pairing is shown to be
integrable before its norm is estimated.
-/
/-! Merged from `NavierStokes.R3.PressureFluxTest`. -/
/-!
# The compact test function in the pressure flux

The identity `φ² r = D(φ⁸)[w]` places the localized pressure flux in the
commutator form.  Its estimates use only the unweighted velocity energy and
the weighted velocity and gradient norms.
-/


noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace NavierStokesR3.PressureFluxTest

open ProblemStatement Comparison

/-- The scalar test function for the pressure commutator. -/
noncomputable def r (φ : Space → ℝ) (w : Space → Space) (x : Space) : ℝ :=
  8 * φ x ^ 5 * (fderiv ℝ φ x (w x))

theorem multiplier_r_eq_weight_deriv {φ : Space → ℝ} (w : Space → Space)
    {x : Space} (hφ : DifferentiableAt ℝ φ x) :
    φ x ^ 2 * r φ w x = fderiv ℝ (fun y => φ y ^ 8) x (w x) := by
  have hd : fderiv ℝ (fun y => φ y ^ 8) x = (8 * φ x ^ 7) • fderiv ℝ φ x := by
    simpa only [Function.comp_def, Nat.cast_ofNat, Nat.reduceSub] using
      ((hasDerivAt_pow 8 (φ x)).comp_hasFDerivAt x hφ.hasFDerivAt).fderiv
  rw [hd]
  simp only [r, _root_.smul_apply, smul_eq_mul]
  ring

theorem r_smooth {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (r φ w) :=
  (contDiff_const.mul (hφ.pow 5)).mul
    ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply hw)

theorem r_hasCompactSupport {φ : Space → ℝ} (hs : HasCompactSupport φ)
    (w : Space → Space) : HasCompactSupport (r φ w) := by
  apply hs.mono
  intro x hx
  change φ x ≠ 0
  intro hzero
  apply hx
  simp [r, hzero]

theorem memLp_r {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w)
    (p : ℝ≥0∞) : MemLp (r φ w) p volume :=
  (r_smooth hφ hw).continuous.memLp_of_hasCompactSupport (r_hasCompactSupport hs w)

theorem memLp_fderiv_r {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w)
    (p : ℝ≥0∞) : MemLp (fderiv ℝ (r φ w)) p volume :=
  ((r_smooth hφ hw).fderiv_right (m := ∞) (by simp)).continuous.memLp_of_hasCompactSupport
    ((r_hasCompactSupport hs w).fderiv ℝ)

theorem norm_r_le {φ : Space → ℝ} {w : Space → Space} {x : Space}
    (hφ0 : 0 ≤ φ x) (hφ1 : φ x ≤ 1) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ‖fderiv ℝ φ x‖ ≤ L) :
    ‖r φ w x‖ ≤ (8 * L) * ‖(φ x ^ 3) • w x‖ := by
  have hp2 : φ x ^ 2 ≤ 1 := pow_le_one₀ hφ0 hφ1
  have hp : φ x ^ 5 ≤ φ x ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hp2 (pow_nonneg hφ0 3)]
  have happly : ‖fderiv ℝ φ x (w x)‖ ≤ L * ‖w x‖ :=
    ((fderiv ℝ φ x).le_opNorm (w x)).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  calc
    ‖r φ w x‖ = 8 * φ x ^ 5 * ‖fderiv ℝ φ x (w x)‖ := by
      simp [r, norm_mul, Real.norm_eq_abs, abs_of_nonneg hφ0]
    _ ≤ 8 * φ x ^ 5 * (L * ‖w x‖) :=
      mul_le_mul_of_nonneg_left happly (by positivity)
    _ ≤ (8 * L) * (φ x ^ 3 * ‖w x‖) := by
      nlinarith [mul_le_mul_of_nonneg_right hp (mul_nonneg hL0 (norm_nonneg (w x)))]
    _ = (8 * L) * ‖(φ x ^ 3) • w x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hφ0 3)]

/-- The test belongs to `L⁴`, with the exact endpoint interpolation exponents. -/
theorem memLp_and_lpNorm_r_four_le {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w)
    (hw2 : MemLp w 2 volume) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x, ‖fderiv ℝ φ x‖ ≤ L) :
    MemLp (r φ w) 4 volume ∧
      comparisonLpNorm 4 (r φ w) ≤ 8 * L * comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
        comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (3 / 4 : ℝ) := by
  have hw6 := WeightedSobolev.memLp_cutoff_pow_smul hφ.continuous hs hw.continuous
    (by norm_num : (4 : ℕ) ≠ 0) 6
  obtain ⟨hw4, hbound⟩ := WeightedInterpolation.cutoff_interpolation_four
    hφ.continuous.aestronglyMeasurable hφ0 hw2 hw6
  refine ⟨memLp_r hφ hs hw 4, ?_⟩
  calc
    comparisonLpNorm 4 (r φ w) ≤ comparisonLpNorm 4 (fun x => (8 * L) • (φ x ^ 3 • w x)) := by
      apply LpNormTools.lpNorm_mono_of_norm_le (hw4.const_smul (8 * L))
      intro x
      change ‖r φ w x‖ ≤ ‖(8 * L) • (φ x ^ 3 • w x)‖
      rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 8 * L)]
      exact norm_r_le (hφ0 x) (hφ1 x) hL0 (hL x)
    _ = (8 * L) * comparisonLpNorm 4 (fun x => φ x ^ 3 • w x) := by
      rw [LpNormTools.lpNorm_const_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ 8 * L)]
    _ ≤ (8 * L) * (comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
        comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 8 * L * comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
        comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (3 / 4 : ℝ) := by ring

private theorem norm_fderiv_product_le {f g : Space → ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y => f y * g y) x‖ ≤
      ‖f x‖ * ‖fderiv ℝ g x‖ + ‖g x‖ * ‖fderiv ℝ f x‖ := by
  rw [fderiv_fun_mul hf hg]
  exact (norm_add_le _ _).trans (add_le_add
    (ContinuousLinearMap.opNorm_smul_le _ _) (ContinuousLinearMap.opNorm_smul_le _ _))

private theorem norm_fderiv_apply_le {φ : Space → ℝ} {w : Space → Space} {x : Space}
    (hφ : DifferentiableAt ℝ (fderiv ℝ φ) x) (hw : DifferentiableAt ℝ w x) :
    ‖fderiv ℝ (fun y => fderiv ℝ φ y (w y)) x‖ ≤
      ‖fderiv ℝ φ x‖ * ‖fderiv ℝ w x‖ + ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖ := by
  have hflip : ‖(fderiv ℝ (fderiv ℝ φ) x).flip (w x)‖ ≤
      ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    change ‖fderiv ℝ (fderiv ℝ φ) x z (w x)‖ ≤ _
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ φ) x z‖ * ‖w x‖ :=
        (fderiv ℝ (fderiv ℝ φ) x z).le_opNorm _
      _ ≤ (‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖z‖) * ‖w x‖ :=
        mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ φ) x).le_opNorm z)
          (norm_nonneg _)
      _ = _ := by ring
  rw [fderiv_clm_apply hφ hw]
  exact (norm_add_le _ _).trans
    (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) hflip)

/-- Product differentiation before replacing the cutoff derivative norms by constants. -/
theorem norm_fderiv_r_le_raw {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hw : ContDiff ℝ ∞ w) (x : Space) (hφ0 : 0 ≤ φ x) :
    ‖fderiv ℝ (r φ w) x‖ ≤ 8 *
      (φ x ^ 5 * ‖fderiv ℝ φ x‖ * ‖fderiv ℝ w x‖ +
        φ x ^ 5 * ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖ +
        5 * φ x ^ 4 * ‖fderiv ℝ φ x‖ ^ 2 * ‖w x‖) := by
  have hdφ : DifferentiableAt ℝ φ x := (contDiff_infty.1 hφ 1).differentiable (by simp) x
  have hdw : DifferentiableAt ℝ w x := (contDiff_infty.1 hw 1).differentiable (by simp) x
  have hdDφ : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  let q : Space → ℝ := fun y => fderiv ℝ φ y (w y)
  have hdq : DifferentiableAt ℝ q x := hdDφ.clm_apply hdw
  have hr : r φ w = fun y => 8 * (φ y ^ 5 * q y) := by
    funext y
    simp only [r, q]
    ring
  have hpow : ‖fderiv ℝ (fun y => φ y ^ 5) x‖ ≤
      5 * φ x ^ 4 * ‖fderiv ℝ φ x‖ := by
    have heq : fderiv ℝ (fun y => φ y ^ 5) x = (5 * φ x ^ 4) • fderiv ℝ φ x := by
      simpa only [Function.comp_def, Nat.cast_ofNat, Nat.reduceSub] using
        ((hasDerivAt_pow 5 (φ x)).comp_hasFDerivAt x hdφ.hasFDerivAt).fderiv
    rw [heq]
    calc
      _ ≤ ‖(5 : ℝ) * φ x ^ 4‖ * ‖fderiv ℝ φ x‖ :=
        ContinuousLinearMap.opNorm_smul_le (5 * φ x ^ 4) (fderiv ℝ φ x)
      _ = _ := by rw [Real.norm_of_nonneg (by positivity : 0 ≤ 5 * φ x ^ 4)]
  have hq : ‖q x‖ ≤ ‖fderiv ℝ φ x‖ * ‖w x‖ := (fderiv ℝ φ x).le_opNorm _
  have hDq : ‖fderiv ℝ q x‖ ≤ ‖fderiv ℝ φ x‖ * ‖fderiv ℝ w x‖ +
      ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖ := norm_fderiv_apply_le hdDφ hdw
  calc
    ‖fderiv ℝ (r φ w) x‖ ≤ 8 * ‖fderiv ℝ (fun y => φ y ^ 5 * q y) x‖ := by
      rw [hr, fderiv_const_mul (a := fun y => φ y ^ 5 * q y) ((hdφ.pow 5).mul hdq) 8]
      simpa using ContinuousLinearMap.opNorm_smul_le (8 : ℝ)
        (fderiv ℝ (fun y => φ y ^ 5 * q y) x)
    _ ≤ 8 * (φ x ^ 5 * ‖fderiv ℝ q x‖ +
        ‖q x‖ * ‖fderiv ℝ (fun y => φ y ^ 5) x‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hφ0 5)] using!
        norm_fderiv_product_le (hdφ.pow 5) hdq
    _ ≤ 8 * (φ x ^ 5 * (‖fderiv ℝ φ x‖ * ‖fderiv ℝ w x‖ +
        ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖) +
        (‖fderiv ℝ φ x‖ * ‖w x‖) * (5 * φ x ^ 4 * ‖fderiv ℝ φ x‖)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add (mul_le_mul_of_nonneg_left hDq (pow_nonneg hφ0 5))
      exact mul_le_mul hq hpow (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Only the weighted velocity derivative occurs in the pointwise bound. -/
theorem norm_fderiv_r_le_amplitude {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hw : ContDiff ℝ ∞ w) (x : Space)
    (hφ0 : 0 ≤ φ x) (hφ1 : φ x ≤ 1) {L J : ℝ} (hL0 : 0 ≤ L)
    (hL : ‖fderiv ℝ φ x‖ ≤ L) (hJ : ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ J) :
    ‖fderiv ℝ (r φ w) x‖ ≤
      (24 * L) * WeightedSobolev.cutoffGradientAmplitude φ w x +
        (40 * L ^ 2 + 8 * J) * ‖w x‖ := by
  have hp4 : φ x ^ 4 ≤ 1 := pow_le_one₀ hφ0 hφ1
  have hp5 : φ x ^ 5 ≤ 1 := pow_le_one₀ hφ0 hφ1
  have hp54 : φ x ^ 5 ≤ φ x ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hφ1 (pow_nonneg hφ0 4)]
  have hgrad := GradientOperator.norm_fderiv_le_three_mul_sqrt_gradientSq w x
  have h1 : φ x ^ 5 * ‖fderiv ℝ φ x‖ * ‖fderiv ℝ w x‖ ≤
      3 * L * WeightedSobolev.cutoffGradientAmplitude φ w x := by
    calc
      _ ≤ (φ x ^ 4 * L) * (3 * Real.sqrt (gradientSq w x)) :=
        mul_le_mul (mul_le_mul hp54 hL (norm_nonneg _) (pow_nonneg hφ0 4)) hgrad
          (norm_nonneg _) (mul_nonneg (pow_nonneg hφ0 4) hL0)
      _ = _ := by unfold WeightedSobolev.cutoffGradientAmplitude; ring
  have h2 : φ x ^ 5 * ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖ ≤ J * ‖w x‖ := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [one_mul] using
      mul_le_mul hp5 hJ (norm_nonneg (fderiv ℝ (fderiv ℝ φ) x)) zero_le_one
  have hsquare : ‖fderiv ℝ φ x‖ ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hL 2
  have h3 : 5 * φ x ^ 4 * ‖fderiv ℝ φ x‖ ^ 2 * ‖w x‖ ≤
      5 * L ^ 2 * ‖w x‖ := by
    have hh : φ x ^ 4 * ‖fderiv ℝ φ x‖ ^ 2 ≤ L ^ 2 := by
      simpa only [one_mul] using mul_le_mul hp4 hsquare (sq_nonneg _) zero_le_one
    calc
      _ = 5 * (φ x ^ 4 * ‖fderiv ℝ φ x‖ ^ 2) * ‖w x‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hh (by norm_num)) (norm_nonneg _)
  calc
    ‖fderiv ℝ (r φ w) x‖ ≤ _ := norm_fderiv_r_le_raw hφ hw x hφ0
    _ ≤ 8 * (3 * L * WeightedSobolev.cutoffGradientAmplitude φ w x +
        J * ‖w x‖ + 5 * L ^ 2 * ‖w x‖) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) (by norm_num)
    _ = _ := by ring

/-- The derivative is square integrable and controlled by weighted dissipation. -/
theorem memLp_and_lpNorm_fderiv_r_two_le {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w)
    (hw2 : MemLp w 2 volume) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {L J : ℝ} (hL0 : 0 ≤ L) (hJ0 : 0 ≤ J)
    (hL : ∀ x, ‖fderiv ℝ φ x‖ ≤ L)
    (hJ : ∀ x, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ J) :
    MemLp (fderiv ℝ (r φ w)) 2 volume ∧
      comparisonLpNorm 2 (fderiv ℝ (r φ w)) ≤
        (24 * L) * Real.sqrt (∫ x, φ x ^ 8 * gradientSq w x) +
          (40 * L ^ 2 + 8 * J) * comparisonLpNorm 2 w := by
  let G := WeightedSobolev.cutoffGradientAmplitude φ w
  have hw1 := contDiff_infty.1 hw 1
  have hG : MemLp G 2 volume :=
    WeightedSobolev.memLp_cutoffGradientAmplitude hφ.continuous hs hw1 2
  have hG24 : MemLp (fun x => (24 * L) • G x) 2 volume := hG.const_smul (24 * L)
  have hw40 : MemLp (fun x => (40 * L ^ 2 + 8 * J) • ‖w x‖) 2 volume :=
    hw2.norm.const_smul (40 * L ^ 2 + 8 * J)
  have hc : 0 ≤ 40 * L ^ 2 + 8 * J := by positivity
  refine ⟨memLp_fderiv_r hφ hs hw 2, ?_⟩
  calc
    comparisonLpNorm 2 (fderiv ℝ (r φ w)) ≤
        comparisonLpNorm 2 (fun x => (24 * L) • G x + (40 * L ^ 2 + 8 * J) • ‖w x‖) := by
      apply LpNormTools.lpNorm_mono_of_norm_le (hG24.add hw40)
      intro x
      have hp := norm_fderiv_r_le_amplitude hφ hw x (hφ0 x) (hφ1 x) hL0 (hL x) (hJ x)
      simpa only [Pi.add_apply, smul_eq_mul, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ (24 * L) * G x + (40 * L ^ 2 + 8 * J) * ‖w x‖ by
          have := WeightedSobolev.cutoffGradientAmplitude_nonneg φ w x
          dsimp [G] at *
          positivity)] using hp
    _ ≤ comparisonLpNorm 2 (fun x => (24 * L) • G x) +
        comparisonLpNorm 2 (fun x => (40 * L ^ 2 + 8 * J) • ‖w x‖) :=
      LpNormTools.lpNorm_add_le (by norm_num) hG24 hw40
    _ = (24 * L) * Real.sqrt (∫ x, φ x ^ 8 * gradientSq w x) +
        (40 * L ^ 2 + 8 * J) * comparisonLpNorm 2 w := by
      rw [LpNormTools.lpNorm_const_smul, LpNormTools.lpNorm_const_smul]
      have hGeq := WeightedSobolev.lpNorm_cutoffGradientAmplitude hφ.continuous hs hw1
      change comparisonLpNorm 2 G = _ at hGeq
      rw [hGeq]
      simp [comparisonLpNorm, eLpNorm_norm w hw2.aestronglyMeasurable,
        Real.norm_eq_abs, abs_of_nonneg hL0, abs_of_nonneg hc]


/-- The actual test at radius `R` in the fixed cutoff family. -/
def cutoffTest (R : ℝ) (w : Space → Space) : Space → ℝ :=
  r (ComparisonCutoffs.cutoff R) w

theorem cutoffTest_flux_identity (R : ℝ) (w : Space → Space) (x : Space) :
    ComparisonCutoffs.multiplier R x * cutoffTest R w x =
      fderiv ℝ (ComparisonCutoffs.weight R) x (w x) :=
  multiplier_r_eq_weight_deriv w
    ((contDiff_infty.1 (ComparisonCutoffs.cutoff_smooth R) 1).differentiable (by simp) x)

theorem cutoffTest_smooth (R : ℝ) {w : Space → Space} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (cutoffTest R w) := r_smooth (ComparisonCutoffs.cutoff_smooth R) hw

theorem cutoffTest_hasCompactSupport {R : ℝ} (hR : 0 < R) (w : Space → Space) :
    HasCompactSupport (cutoffTest R w) :=
  r_hasCompactSupport (ComparisonCutoffs.cutoff_hasCompactSupport hR) w



theorem cutoffTest_four_bound {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) :
    MemLp (cutoffTest R w) 4 volume ∧
      comparisonLpNorm 4 (cutoffTest R w) ≤ (8 * ComparisonCutoffs.derivativeConstant 1 / R) *
        comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
          comparisonLpNorm 6 (fun x => ComparisonCutoffs.cutoff R x ^ 4 • w x) ^ (3 / 4 : ℝ) := by
  have h := memLp_and_lpNorm_r_four_le (ComparisonCutoffs.cutoff_smooth R)
    (ComparisonCutoffs.cutoff_hasCompactSupport hR) hw hw2
    (ComparisonCutoffs.cutoff_nonneg R) (ComparisonCutoffs.cutoff_le_one R)
    (div_nonneg (ComparisonCutoffs.derivativeConstant_pos 1).le hR.le)
    (ComparisonCutoffs.cutoff_fderiv_le hR)
  simpa only [cutoffTest, mul_div_assoc] using h

/-- A fixed constant for the derivative bound of the pressure test. -/
def cutoffDerivativeConstant : ℝ :=
  max (24 * ComparisonCutoffs.derivativeConstant 1)
    (40 * ComparisonCutoffs.derivativeConstant 1 ^ 2 + 8 * ComparisonCutoffs.derivativeConstant 2)

theorem cutoffDerivativeConstant_pos : 0 < cutoffDerivativeConstant :=
  lt_of_lt_of_le (mul_pos (by norm_num) (ComparisonCutoffs.derivativeConstant_pos 1))
    (le_max_left _ _)

theorem cutoffTest_derivative_bound {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) :
    MemLp (fderiv ℝ (cutoffTest R w)) 2 volume ∧
      comparisonLpNorm 2 (fderiv ℝ (cutoffTest R w)) ≤
        (cutoffDerivativeConstant / R) *
          Real.sqrt (∫ x, ComparisonCutoffs.cutoff R x ^ 8 * gradientSq w x) +
        (cutoffDerivativeConstant / R ^ 2) * comparisonLpNorm 2 w := by
  have h := memLp_and_lpNorm_fderiv_r_two_le (ComparisonCutoffs.cutoff_smooth R)
    (ComparisonCutoffs.cutoff_hasCompactSupport hR) hw hw2
    (ComparisonCutoffs.cutoff_nonneg R) (ComparisonCutoffs.cutoff_le_one R)
    (div_nonneg (ComparisonCutoffs.derivativeConstant_pos 1).le hR.le)
    (div_nonneg (ComparisonCutoffs.derivativeConstant_pos 2).le (sq_nonneg R))
    (ComparisonCutoffs.cutoff_fderiv_le hR) (ComparisonCutoffs.cutoff_second_fderiv_le hR)
  refine ⟨h.1, h.2.trans ?_⟩
  calc
    _ = ((24 * ComparisonCutoffs.derivativeConstant 1) / R) *
          Real.sqrt (∫ x, ComparisonCutoffs.cutoff R x ^ 8 * gradientSq w x) +
        ((40 * ComparisonCutoffs.derivativeConstant 1 ^ 2 +
          8 * ComparisonCutoffs.derivativeConstant 2) / R ^ 2) * comparisonLpNorm 2 w := by
      field_simp [hR.ne']
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right
        ((div_le_div_iff_of_pos_right hR).2 (le_max_left _ _)) (Real.sqrt_nonneg _))
      (mul_le_mul_of_nonneg_right
        ((div_le_div_iff_of_pos_right (sq_pos_of_pos hR)).2 (le_max_right _ _))
        (LpNormTools.lpNorm_nonneg 2 w))

end NavierStokesR3.PressureFluxTest

/-! Merged from `NavierStokes.R3.LocalizedTensorBounds`. -/
/-!
# Weighted tensor bounds for the localized pressure

The tensor difference is expanded around the reference velocity. Its two
cross terms use `L³` of that velocity and `L²` of the difference; the quadratic
term uses the cutoff interpolation estimate. All norms remain finite explicitly.
-/


noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace NavierStokesR3.LocalizedTensorBounds

open ProblemStatement Comparison

private theorem six_fifths_ne_zero : (6 / 5 : ℝ≥0∞) ≠ 0 :=
  (ENNReal.toReal_pos_iff.mp (by norm_num : 0 < (6 / 5 : ℝ≥0∞).toReal)).1.ne'

private theorem six_fifths_ne_top : (6 / 5 : ℝ≥0∞) ≠ ⊤ :=
  (ENNReal.toReal_pos_iff.mp (by norm_num : 0 < (6 / 5 : ℝ≥0∞).toReal)).2.ne

private theorem twelve_fifths_ne_zero : (12 / 5 : ℝ≥0∞) ≠ 0 :=
  (ENNReal.toReal_pos_iff.mp (by norm_num : 0 < (12 / 5 : ℝ≥0∞).toReal)).1.ne'

/-- Scalar Hölder with finite real-valued norms. -/
theorem scalar_product_bound {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    {f g : Space → ℝ} (hf : MemLp f p volume) (hg : MemLp g q volume) :
    MemLp (fun x => f x * g x) r volume ∧
      comparisonLpNorm r (fun x => f x * g x) ≤ comparisonLpNorm p f * comparisonLpNorm q g := by
  have hprod : MemLp (fun x => f x * g x) r volume := hf.mul' hg
  have hb : eLpNorm (fun x => f x * g x) r volume ≤
      eLpNorm f p volume * eLpNorm g q volume := by
    simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (fun a b : ℝ => a * b) 1
      continuous_mul hf.aestronglyMeasurable hg.aestronglyMeasurable
      (Eventually.of_forall fun x => by simp [norm_mul])
  refine ⟨hprod, ?_⟩
  simpa only [comparisonLpNorm, ENNReal.toReal_mul] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) hb

/-- The scalar product of the two vector magnitudes belongs to `L^(6/5)`. -/
theorem cross_norm_bound {u w : Space → Space}
    (hu : MemLp u 3 volume) (hw : MemLp w 2 volume) :
    MemLp (fun x => ‖u x‖ * ‖w x‖) (6 / 5) volume ∧
      comparisonLpNorm (6 / 5) (fun x => ‖u x‖ * ‖w x‖) ≤ comparisonLpNorm 3 u * comparisonLpNorm 2 w := by
  let : ENNReal.HolderTriple (3 : ℝ≥0∞) 2 (6 / 5) := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness)
      (ENNReal.inv_ne_top.mpr six_fifths_ne_zero)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num⟩
  simpa only [comparisonLpNorm, eLpNorm_norm u hu.aestronglyMeasurable,
    eLpNorm_norm w hw.aestronglyMeasurable] using scalar_product_bound (r := 6 / 5) hu.norm hw.norm

/-- The quadratic weighted difference has the endpoint interpolation bound. -/
theorem quadratic_cutoff_bound {φ : Space → ℝ} {w : Space → Space}
    (hφm : AEStronglyMeasurable φ volume) (hφ0 : ∀ x, 0 ≤ φ x)
    (hw : MemLp w 2 volume)
    (hweighted : MemLp (fun x => φ x ^ 4 • w x) 6 volume) :
    MemLp (fun x => ‖φ x • w x‖ ^ 2) (6 / 5) volume ∧
      comparisonLpNorm (6 / 5) (fun x => ‖φ x • w x‖ ^ 2) ≤
        comparisonLpNorm 2 w ^ (3 / 2 : ℝ) *
          comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (1 / 2 : ℝ) := by
  obtain ⟨hmem, hb⟩ := WeightedInterpolation.cutoff_interpolation_twelve_fifths
    hφm hφ0 hw hweighted
  let : ENNReal.HolderTriple (12 / 5 : ℝ≥0∞) (12 / 5) (6 / 5) := ⟨by
    have h12 := ENNReal.inv_ne_top.mpr twelve_fifths_ne_zero
    apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.mpr ⟨h12, h12⟩)
      (ENNReal.inv_ne_top.mpr six_fifths_ne_zero)).mp
    rw [ENNReal.toReal_add h12 h12]
    norm_num⟩
  obtain ⟨hprod, hprodb⟩ := scalar_product_bound (r := 6 / 5) hmem.norm hmem.norm
  have hQ : MemLp (fun x => ‖φ x • w x‖ ^ 2) (6 / 5) volume := by
    simpa only [pow_two] using hprod
  have hQb : comparisonLpNorm (6 / 5) (fun x => ‖φ x • w x‖ ^ 2) ≤
      comparisonLpNorm (12 / 5) (fun x => φ x • w x) ^ 2 := by
    simpa only [pow_two, comparisonLpNorm,
      eLpNorm_norm (fun x => φ x • w x) hmem.aestronglyMeasurable] using hprodb
  have hA := LpNormTools.lpNorm_nonneg (12 / 5) (fun x => φ x • w x)
  have hM := LpNormTools.lpNorm_nonneg 2 w
  have hB := LpNormTools.lpNorm_nonneg 6 (fun x => φ x ^ 4 • w x)
  refine ⟨hQ, hQb.trans ?_⟩
  calc
    comparisonLpNorm (12 / 5) (fun x => φ x • w x) ^ 2 ≤
        (comparisonLpNorm 2 w ^ (3 / 4 : ℝ) *
          comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (1 / 4 : ℝ)) ^ 2 := by
      exact pow_le_pow_left₀ hA hb 2
    _ = comparisonLpNorm 2 w ^ (3 / 2 : ℝ) *
        comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast _ 2,
        Real.mul_rpow (Real.rpow_nonneg hM _) (Real.rpow_nonneg hB _),
        ← Real.rpow_mul hM, ← Real.rpow_mul hB]
      norm_num

/-- The tensor identity uses the actual difference of the two velocities. -/
theorem tensorDiff_eq (u v : VelocityField) (t : ℝ) (i j : Fin 3) (x : Space) :
    tensorDiff u v t i j x =
      u (t, x) i * (u - v) (t, x) j +
        (u - v) (t, x) i * u (t, x) j -
        (u - v) (t, x) i * (u - v) (t, x) j := by
  change u (t, x) i * u (t, x) j - v (t, x) i * v (t, x) j =
    u (t, x) i * (u (t, x) j - v (t, x) j) +
      (u (t, x) i - v (t, x) i) * u (t, x) j -
      (u (t, x) i - v (t, x) i) * (u (t, x) j - v (t, x) j)
  ring

theorem continuous_component {f : Space → Space} (hf : Continuous f) (i : Fin 3) :
    Continuous (fun x => f x i) :=
  (continuous_apply i).comp ((EuclideanSpace.equiv (Fin 3) ℝ).continuous.comp hf)

theorem continuous_tensorDiff {u v : VelocityField} {t : ℝ}
    (hu : Continuous (fun x => u (t, x))) (hv : Continuous (fun x => v (t, x)))
    (i j : Fin 3) : Continuous (tensorDiff u v t i j) :=
  ((continuous_component hu i).mul (continuous_component hu j)).sub
    ((continuous_component hv i).mul (continuous_component hv j))

/-- Pointwise domination is uniform in both tensor indices. -/
theorem norm_weighted_tensorDiff_le (u v : VelocityField) (t : ℝ) (i j : Fin 3)
    (x : Space) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖s ^ 2 * tensorDiff u v t i j x‖ ≤
      2 * (‖u (t, x)‖ * ‖(u - v) (t, x)‖) + ‖s • (u - v) (t, x)‖ ^ 2 := by
  let a := u (t, x)
  let w := (u - v) (t, x)
  have hcross1 : ‖a i * w j‖ ≤ ‖a‖ * ‖w‖ := by
    rw [norm_mul]
    exact mul_le_mul (PiLp.norm_apply_le a i) (PiLp.norm_apply_le w j)
      (norm_nonneg _) (norm_nonneg _)
  have hcross2 : ‖w i * a j‖ ≤ ‖w‖ * ‖a‖ := by
    rw [norm_mul]
    exact mul_le_mul (PiLp.norm_apply_le w i) (PiLp.norm_apply_le a j)
      (norm_nonneg _) (norm_nonneg _)
  have hquad : ‖w i * w j‖ ≤ ‖w‖ * ‖w‖ := by
    rw [norm_mul]
    exact mul_le_mul (PiLp.norm_apply_le w i) (PiLp.norm_apply_le w j)
      (norm_nonneg _) (norm_nonneg _)
  have ht : ‖tensorDiff u v t i j x‖ ≤ 2 * (‖a‖ * ‖w‖) + ‖w‖ ^ 2 := by
    rw [tensorDiff_eq]
    calc
      ‖a i * w j + w i * a j - w i * w j‖ ≤
          ‖a i * w j + w i * a j‖ + ‖w i * w j‖ := norm_sub_le _ _
      _ ≤ (‖a i * w j‖ + ‖w i * a j‖) + ‖w i * w j‖ :=
        add_le_add_left (norm_add_le _ _) _
      _ ≤ (‖a‖ * ‖w‖ + ‖w‖ * ‖a‖) + ‖w‖ * ‖w‖ :=
        add_le_add (add_le_add hcross1 hcross2) hquad
      _ = _ := by ring
  have hs2 : s ^ 2 ≤ 1 := pow_le_one₀ hs0 hs1
  calc
    ‖s ^ 2 * tensorDiff u v t i j x‖ = s ^ 2 * ‖tensorDiff u v t i j x‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg s)]
    _ ≤ s ^ 2 * (2 * (‖a‖ * ‖w‖) + ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg s)
    _ ≤ 2 * (‖a‖ * ‖w‖) + ‖s • w‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
      nlinarith [mul_nonneg (sub_nonneg.mpr hs2) (mul_nonneg (norm_nonneg a) (norm_nonneg w))]

/-- Compactness supplies finite weighted tensor norms without any growth
assumption on either velocity. -/
theorem weighted_tensorDiff_memLp {φ : Space → ℝ} {u v : VelocityField} {t : ℝ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (hu : Continuous (fun x => u (t, x))) (hv : Continuous (fun x => v (t, x)))
    (i j : Fin 3) (p : ℝ≥0∞) :
    MemLp (fun x => φ x ^ 2 * tensorDiff u v t i j x) p volume := by
  have hp : HasCompactSupport (fun x => φ x ^ 2) :=
    hs.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
  exact ((hφ.pow 2).mul (continuous_tensorDiff hu hv i j)).memLp_of_hasCompactSupport hp.mul_right

/-- The weighted tensor estimate used by the localized pressure argument.
It has the same constant for every pair of indices. -/
theorem weighted_tensorDiff_bound {φ : Space → ℝ} {u v : VelocityField} {t : ℝ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (hu : Continuous (fun x => u (t, x))) (hv : Continuous (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hu3 : MemLp (fun x => u (t, x)) 3 volume)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) (i j : Fin 3) :
    MemLp (fun x => φ x ^ 2 * tensorDiff u v t i j x) (6 / 5) volume ∧
      comparisonLpNorm (6 / 5) (fun x => φ x ^ 2 * tensorDiff u v t i j x) ≤
        comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
          cutoffL6 φ (u - v) t ^ (1 / 2 : ℝ) +
        2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t, x)) := by
  let P : Space → ℝ := fun x => ‖u (t, x)‖ * ‖(u - v) (t, x)‖
  let Q : Space → ℝ := fun x => ‖φ x • (u - v) (t, x)‖ ^ 2
  obtain ⟨hP, hPb⟩ := cross_norm_bound hu3 hw2
  have hweighted := WeightedSobolev.memLp_cutoff_pow_smul hφ hs (hu.sub hv)
    (by norm_num : (4 : ℕ) ≠ 0) 6
  obtain ⟨hQ, hQb⟩ := quadratic_cutoff_bound hφ.aestronglyMeasurable hφ0 hw2 hweighted
  change MemLp P (6 / 5) volume at hP
  change comparisonLpNorm (6 / 5) P ≤ _ at hPb
  change MemLp Q (6 / 5) volume at hQ
  change comparisonLpNorm (6 / 5) Q ≤ _ at hQb
  have h2P : MemLp (fun x => (2 : ℝ) • P x) (6 / 5) volume := hP.const_smul (2 : ℝ)
  refine ⟨weighted_tensorDiff_memLp hφ hs hu hv i j (6 / 5), ?_⟩
  calc
    comparisonLpNorm (6 / 5) (fun x => φ x ^ 2 * tensorDiff u v t i j x) ≤
        comparisonLpNorm (6 / 5) (fun x => (2 : ℝ) • P x + Q x) := by
      apply LpNormTools.lpNorm_mono_of_norm_le (h2P.add hQ)
      intro x
      change ‖φ x ^ 2 * tensorDiff u v t i j x‖ ≤ ‖2 * P x + Q x‖
      have hn : ‖2 * P x + Q x‖ = 2 * P x + Q x := by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        dsimp [P, Q]
        positivity
      rw [hn]
      exact norm_weighted_tensorDiff_le u v t i j x (hφ0 x) (hφ1 x)
    _ ≤ comparisonLpNorm (6 / 5) (fun x => (2 : ℝ) • P x) + comparisonLpNorm (6 / 5) Q :=
      LpNormTools.lpNorm_add_le (by
        apply (ENNReal.toReal_le_toReal ENNReal.one_ne_top six_fifths_ne_top).mp
        norm_num) h2P hQ
    _ = 2 * comparisonLpNorm (6 / 5) P + comparisonLpNorm (6 / 5) Q := by
      rw [LpNormTools.lpNorm_const_smul]
      norm_num
    _ ≤ _ := by
      change 2 * comparisonLpNorm (6 / 5) P + comparisonLpNorm (6 / 5) Q ≤
        comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
          comparisonLpNorm 6 (fun x => φ x ^ 4 • (u - v) (t, x)) ^ (1 / 2 : ℝ) +
        2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t, x))
      nlinarith

end NavierStokesR3.LocalizedTensorBounds

/-! Merged from `NavierStokes.R3.PressureFluxIdentity` (in a section, so its `open`s cannot leak). -/
section
/-!
# From scalar pressure-gradient identification to the cutoff pressure flux

This module is an integration-by-parts bridge. Its input is an explicit
identification of every compact scalar pressure-gradient pairing. It does not
assume a pressure-flux formula or any bound on the pressure at infinity.
-/


noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff BigOperators

namespace NavierStokesR3.PressureFluxIdentity

open ProblemStatement Comparison PressureRecovery HarmonicTestFunctionals
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness

theorem fluxFunction_smooth {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun x : Space => fderiv ℝ χ x (w x)) :=
  (hχ.fderiv_right (m := ∞) (by simp)).clm_apply hw

theorem fluxFunction_hasCompactSupport {χ : Space → ℝ}
    (hcχ : HasCompactSupport χ) (w : Space → Space) :
    HasCompactSupport (fun x : Space => fderiv ℝ χ x (w x)) := by
  apply (hcχ.fderiv ℝ).mono
  intro x hx
  change fderiv ℝ χ x ≠ 0
  intro hzero
  apply hx
  simp only [hzero, _root_.zero_apply]

theorem integrable_pressure_flux {χ π : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hπ : ContDiff ℝ ∞ π) (hw : ContDiff ℝ ∞ w)
    (hcχ : HasCompactSupport χ) :
    Integrable (fun x : Space => π x * fderiv ℝ χ x (w x)) :=
  ConservativeDifference.integrable_mul_test hπ.continuous
    (fluxFunction_smooth hχ hw).continuous (fluxFunction_hasCompactSupport hcχ w)

/-- The scalar compact test associated to one component of the weighted velocity. -/
def weightedComponent (χ : Space → ℝ) (w : Space → Space) (k : Fin 3) : Space → ℝ :=
  fun x => χ x * w x k

theorem weightedComponent_smooth {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (k : Fin 3) :
    ContDiff ℝ ∞ (weightedComponent χ w k) :=
  hχ.mul (component_contDiff hw k)

theorem weightedComponent_hasCompactSupport {χ : Space → ℝ}
    (hcχ : HasCompactSupport χ) (w : Space → Space) (k : Fin 3) :
    HasCompactSupport (weightedComponent χ w k) := hcχ.mul_right

theorem sum_partial_weightedComponent {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w)
    (hdiv : ∀ x : Space, (∑ k : Fin 3, partialD k w x k) = 0) (x : Space) :
    (∑ k : Fin 3, partialD k (weightedComponent χ w k) x) = fderiv ℝ χ x (w x) := by
  calc
    (∑ k : Fin 3, partialD k (weightedComponent χ w k) x) =
        ∑ k : Fin 3, spatialPartial k (fun y => χ y • w y) x k := by
      apply Finset.sum_congr rfl
      intro k _
      change spatialPartial k (fun y => (χ y • w y) k) x = _
      exact ConservativeDifference.partial_component (hχ.smul hw) k k x
    _ = fderiv ℝ χ x (w x) := by
      simpa only [hdiv x, mul_zero, add_zero] using
        LocalizedDifferenceEnergy.divergence_weighted hχ hw x

/-- The compact flux test is the sum of the differentiated component tests. -/
theorem sum_partial_realTest_weightedComponent {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (hcχ : HasCompactSupport χ)
    (hdiv : ∀ x : Space, (∑ k : Fin 3, partialD k w x k) = 0) :
    (∑ k : Fin 3, partialCLM k (realTest (weightedComponent χ w k)
      (weightedComponent_smooth hχ hw k) (weightedComponent_hasCompactSupport hcχ w k))) =
    realTest (fun x : Space => fderiv ℝ χ x (w x))
      (fluxFunction_smooth hχ hw) (fluxFunction_hasCompactSupport hcχ w) := by
  ext x
  simp only [sum_apply, partialCLM_realTest, realTest_apply]
  calc
    (∑ k : Fin 3, ((spatialPartial k (weightedComponent χ w k) x : ℝ) : ℂ)) =
        ((∑ k : Fin 3, partialD k (weightedComponent χ w k) x : ℝ) : ℂ) :=
      (map_sum Complex.ofRealCLM _ _).symm
    _ = (fderiv ℝ χ x (w x) : ℂ) :=
      congrArg Complex.ofReal (sum_partial_weightedComponent hχ hw hdiv x)

/-- The sum of all canonical pressure pairings is a complex-linear functional. -/
def canonicalPressureLinear (g : Fin 3 → Fin 3 → Space → ℝ)
    (hg : ∀ i j : Fin 3, Integrable (g i j)) : ComplexTest →ₗ[ℂ] ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, PressureFunctionals.pressurePairLinear i j (g i j) (hg i j)

@[simp] theorem canonicalPressureLinear_apply (g : Fin 3 → Fin 3 → Space → ℝ)
    (hg : ∀ i j : Fin 3, Integrable (g i j)) (ψ : ComplexTest) :
    canonicalPressureLinear g hg ψ = ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (g i j) ψ := by
  simp only [canonicalPressureLinear, LinearMap.sum_apply, PressureFunctionals.pressurePairLinear_apply]


/-- Compact integration by parts turns the given scalar pressure-gradient
identification into the actual cutoff pressure flux. -/
theorem pressure_flux_eq_of_gradient_identification
    {π χ : Space → ℝ} {w : Space → Space} {g : Fin 3 → Fin 3 → Space → ℝ}
    (hπ : ContDiff ℝ ∞ π) (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w)
    (hcχ : HasCompactSupport χ) (hg : ∀ i j : Fin 3, Integrable (g i j))
    (hdiv : ∀ x : Space, (∑ k : Fin 3, partialD k w x k) = 0)
    (hgrad : ∀ (k : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ)
      (hcψ : HasCompactSupport ψ),
      (∫ x : Space, partialD k π x * ψ x) =
        -(∑ i : Fin 3, ∑ j : Fin 3,
          pressurePair i j (g i j) (partialCLM k (realTest ψ hψ hcψ))).re) :
    (∫ x : Space, π x * fderiv ℝ χ x (w x)) =
      (∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (g i j)
        (realTest (fun x : Space => fderiv ℝ χ x (w x))
          (fluxFunction_smooth hχ hw) (fluxFunction_hasCompactSupport hcχ w))).re := by
  let η : Fin 3 → ComplexTest := fun k =>
    partialCLM k (realTest (weightedComponent χ w k)
      (weightedComponent_smooth hχ hw k) (weightedComponent_hasCompactSupport hcχ w k))
  let Q : ComplexTest →ₗ[ℂ] ℂ := canonicalPressureLinear g hg
  have hsum : (∑ k : Fin 3, η k) =
      realTest (fun x : Space => fderiv ℝ χ x (w x))
        (fluxFunction_smooth hχ hw) (fluxFunction_hasCompactSupport hcχ w) :=
    sum_partial_realTest_weightedComponent hχ hw hcχ hdiv
  have hint (k : Fin 3) :
      Integrable (fun x : Space => π x * partialD k (weightedComponent χ w k) x) :=
    ConservativeDifference.integrable_mul_test hπ.continuous
      (spatial_partial_contDiff (weightedComponent_smooth hχ hw k) k).continuous
      (CompactEnergy.compact_partial (weightedComponent_hasCompactSupport hcχ w k) k)
  have hscalar (k : Fin 3) :
      (∫ x : Space, π x * partialD k (weightedComponent χ w k) x) = (Q (η k)).re := by
    have hibp :
        (∫ x : Space, partialD k π x * weightedComponent χ w k x) =
          -(∫ x : Space, π x * partialD k (weightedComponent χ w k) x) := by
      simpa only [partialD, mul_comm] using
        CompactEnergy.integral_mul_partial (weightedComponent_smooth hχ hw k) hπ
          (weightedComponent_hasCompactSupport hcχ w k) k
    have h := neg_injective (hibp.symm.trans (hgrad k (weightedComponent χ w k)
      (weightedComponent_smooth hχ hw k) (weightedComponent_hasCompactSupport hcχ w k)))
    simpa only [Q, η, canonicalPressureLinear_apply] using h
  have hfluxsum :
      (∫ x : Space, π x * fderiv ℝ χ x (w x)) =
        ∑ k : Fin 3, ∫ x : Space, π x * partialD k (weightedComponent χ w k) x := by
    calc
      (∫ x : Space, π x * fderiv ℝ χ x (w x)) =
          ∫ x : Space, ∑ k : Fin 3, π x * partialD k (weightedComponent χ w k) x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change π x * fderiv ℝ χ x (w x) =
            ∑ k : Fin 3, π x * partialD k (weightedComponent χ w k) x
          rw [← sum_partial_weightedComponent hχ hw hdiv x, Finset.mul_sum]
      _ = _ := integral_finsetSum _ (fun k _ => hint k)
  calc
    (∫ x : Space, π x * fderiv ℝ χ x (w x)) =
        ∑ k : Fin 3, ∫ x : Space, π x * partialD k (weightedComponent χ w k) x := hfluxsum
    _ = ∑ k : Fin 3, (Q (η k)).re := Finset.sum_congr rfl (fun k _ => hscalar k)
    _ = (∑ k : Fin 3, Q (η k)).re :=
      (map_sum Complex.reCLM (fun k => Q (η k)) Finset.univ).symm
    _ = (Q (∑ k : Fin 3, η k)).re :=
      congrArg Complex.re (map_sum Q η Finset.univ).symm
    _ = _ := by
      rw [hsum]
      exact congrArg Complex.re (canonicalPressureLinear_apply g hg _)

end NavierStokesR3.PressureFluxIdentity
end


/-! Merged from `NavierStokes.R3.ActualPressureFlux`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# The actual pressure flux equals the canonical pressure flux

The scalar gradient identification is supplied by the proved pressure recovery
theorem. The only compact support in this identity is that of the cutoff.
-/


noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NavierStokesR3.ActualPressureFlux

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicUniqueness
open Comparison PressureRecovery PressureFluxIdentity

theorem difference_slice_smooth {T t : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ht : t ∈ Ioo 0 T) :
    ContDiff ℝ ∞ (fun x : Space => (u - v) (t, x)) :=
  spatial_smooth (H.smooth_u.sub H.smooth_v) (Ioo_subset_Icc_self ht)

theorem actual_pressure_flux_integrable {T t : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ht : t ∈ Ioo 0 T) {χ : Space → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    Integrable (fun x : Space => (p - q) (t, x) * fderiv ℝ χ x ((u - v) (t, x))) :=
  integrable_pressure_flux hχ
    (spatial_smooth (H.smooth_p.sub H.smooth_q) (Ioo_subset_Icc_self ht))
    (difference_slice_smooth H ht) hcχ

/-- The pressure flux of the actual difference equation has the canonical
Riesz-pairing representation, with no additional pressure hypothesis. -/
theorem pressure_flux_eq_canonical {T t : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ht : t ∈ Ioo 0 T) {χ : Space → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    (∫ x : Space, (p - q) (t, x) * fderiv ℝ χ x ((u - v) (t, x))) =
      (∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorDiff u v t i j)
        (realTest (fun x : Space => fderiv ℝ χ x ((u - v) (t, x)))
          (fluxFunction_smooth hχ (difference_slice_smooth H ht))
          (fluxFunction_hasCompactSupport hcχ (fun x : Space => (u - v) (t, x))))).re := by
  obtain ⟨_M, _hM, hg⟩ := H.tensor_bound
  have hdiv : ∀ x : Space,
      (∑ k : Fin 3, partialD k (fun y => (u - v) (t, y)) x k) = 0 := by
    intro x
    change spatialDivergence (u - v) t x = 0
    rw [spatialDivergence_sub (spatial_smooth H.smooth_u (Ioo_subset_Icc_self ht))
      (spatial_smooth H.smooth_v (Ioo_subset_Icc_self ht)),
      H.div_u t ht, H.div_v t ht, sub_self]
  exact pressure_flux_eq_of_gradient_identification
    (spatial_smooth (H.smooth_p.sub H.smooth_q) (Ioo_subset_Icc_self ht))
    hχ (difference_slice_smooth H ht) hcχ
    (fun i j => (hg t (Ioo_subset_Icc_self ht) i j).1) hdiv
    (fun k ψ hψ hcψ => gradient_recovery H ht hψ hcψ k)

end NavierStokesR3.ActualPressureFlux


end



noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology BigOperators

namespace NavierStokesR3.PressureFlux

open ProblemStatement Comparison

theorem lpNorm_ofReal (p : ℝ≥0∞) (f : Space → ℝ) (hf : AEStronglyMeasurable f volume) :
    comparisonLpNorm p (fun x => (f x : ℂ)) = comparisonLpNorm p f := by
  apply congrArg ENNReal.toReal
  exact eLpNorm_congr_norm_ae (Complex.continuous_ofReal.comp_aestronglyMeasurable hf) hf
    (Eventually.of_forall fun x => Complex.norm_real (f x))

theorem norm_fderiv_ofReal {f : Space → ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f x) :
    ‖fderiv ℝ (fun y => (f y : ℂ)) x‖ = ‖fderiv ℝ f x‖ := by
  have hd : fderiv ℝ (fun y => (f y : ℂ)) x = Complex.ofRealCLM.comp (fderiv ℝ f x) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  rw [hd, show Complex.ofRealCLM = Complex.ofRealLI.toContinuousLinearMap from rfl]
  exact LinearIsometry.norm_toContinuousLinearMap_comp Complex.ofRealLI

theorem lpNorm_fderiv_realTest (p : ℝ≥0∞) (f : Space → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    comparisonLpNorm p (fderiv ℝ (fun x => PressureRecovery.realTest f hf hc x)) =
      comparisonLpNorm p (fderiv ℝ f) := by
  have hmeas : AEStronglyMeasurable
      (fderiv ℝ (fun x => PressureRecovery.realTest f hf hc x)) volume := by
    have hEq : (fun x => PressureRecovery.realTest f hf hc x) = fun x => (f x : ℂ) := rfl
    rw [hEq]
    exact ((Complex.ofRealCLM.contDiff.comp hf).continuous_fderiv
      (by simp)).aestronglyMeasurable
  apply congrArg ENNReal.toReal
  refine eLpNorm_congr_norm_ae hmeas ?_ (Eventually.of_forall fun x =>
    norm_fderiv_ofReal ((contDiff_infty.1 hf 1).differentiable (by simp) x))
  exact ((contDiff_infty.1 hf 1).continuous_fderiv (by simp)).aestronglyMeasurable

theorem cutoff_lipschitz {R : ℝ} (hR : 0 < R) (x y : Space) :
    |ComparisonCutoffs.cutoff R x - ComparisonCutoffs.cutoff R y| ≤
      (ComparisonCutoffs.derivativeConstant 1 / R) * ‖x - y‖ := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ (univ : Set Space)) =>
      (contDiff_infty.1 (ComparisonCutoffs.cutoff_smooth R) 1).differentiable (by simp) z)
    (fun z (_ : z ∈ (univ : Set Space)) => ComparisonCutoffs.cutoff_fderiv_le hR z)
    (convex_univ : Convex ℝ (univ : Set Space)) (mem_univ y) (mem_univ x)
  exact h

private instance holder_six_fifths_six :
    ENNReal.HolderTriple (6 / 5) 6 1 := ⟨by
  have hz : (6 / 5 : ℝ≥0∞) ≠ 0 :=
    (ENNReal.toReal_pos_iff.mp (by norm_num : 0 < (6 / 5 : ℝ≥0∞).toReal)).1.ne'
  have hn := ENNReal.inv_ne_top.mpr hz
  apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.mpr ⟨hn, by norm_num⟩)
    (by norm_num)).mp
  rw [ENNReal.toReal_add hn (by norm_num)]
  norm_num⟩

theorem integrable_holder_pair {f : Space → ℝ} {g : Space → ℂ}
    (hf : MemLp f (6 / 5) volume) (hg : MemLp g 6 volume) :
    Integrable (fun x => (f x : ℂ) * g x) volume :=
  hf.ofReal.integrable_mul hg

theorem norm_holder_pair_le {f : Space → ℝ} {g : Space → ℂ}
    (hf : MemLp f (6 / 5) volume) (hg : MemLp g 6 volume) :
    ‖∫ x, (f x : ℂ) * g x‖ ≤ comparisonLpNorm (6 / 5) f * comparisonLpNorm 6 g := by
  have hfc : MemLp (fun x => (f x : ℂ)) (6 / 5) volume := hf.ofReal
  have he : eLpNorm (fun x => (f x : ℂ) * g x) 1 volume ≤
      eLpNorm (fun x => (f x : ℂ)) (6 / 5) volume * eLpNorm g 6 volume := by
    simpa only [ENNReal.coe_one, one_mul] using
      eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (fun a b : ℂ => a * b) 1
        continuous_mul hfc.aestronglyMeasurable
        hg.aestronglyMeasurable
        (Eventually.of_forall fun x => by simp [norm_mul])
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top hfc.eLpNorm_ne_top hg.eLpNorm_ne_top) he
  change comparisonLpNorm 1 (fun x => (f x : ℂ) * g x) ≤
    (eLpNorm (fun x => (f x : ℂ)) (6 / 5) volume * eLpNorm g 6 volume).toReal at ht
  rw [ENNReal.toReal_mul] at ht
  change comparisonLpNorm 1 (fun x => (f x : ℂ) * g x) ≤
    comparisonLpNorm (6 / 5) (fun x => (f x : ℂ)) * comparisonLpNorm 6 g at ht
  rw [lpNorm_ofReal _ _ hf.aestronglyMeasurable] at ht
  calc
    ‖∫ x, (f x : ℂ) * g x‖ ≤ ∫ x, ‖(f x : ℂ) * g x‖ := norm_integral_le_integral_norm _
    _ = comparisonLpNorm 1 (fun x => (f x : ℂ) * g x) :=
      (LpNormTools.lpNorm_one_eq_integral_norm (integrable_holder_pair hf hg)).symm
    _ ≤ _ := ht

/-- The scalar test in the localized pressure flux. -/
noncomputable def fluxFunction (χ : Space → ℝ) (w : Space → Space) (x : Space) : ℝ :=
  fderiv ℝ χ x (w x)

theorem fluxFunction_smooth {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fluxFunction χ w) :=
  (hχ.fderiv_right (m := ∞) (by simp)).clm_apply hw

theorem fluxFunction_compact {χ : Space → ℝ} (hc : HasCompactSupport χ)
    (w : Space → Space) : HasCompactSupport (fluxFunction χ w) := by
  apply (hc.fderiv ℝ).mono
  intro x hx
  change fderiv ℝ χ x ≠ 0
  intro hz
  apply hx
  simp [fluxFunction, hz]

/-- The raw complex canonical pairing, with no pressure function selected. -/
def canonicalFlux (g : Fin 3 → Fin 3 → Space → ℝ) (f : Space → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (g i j) (PressureRecovery.realTest f hf hc)


theorem norm_canonicalFlux_le {g : Fin 3 → Fin 3 → Space → ℝ} {f : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {C : ℝ}
    (hbound : ∀ i j : Fin 3,
      ‖pressurePair i j (g i j) (PressureRecovery.realTest f hf hc)‖ ≤ C) :
    ‖canonicalFlux g f hf hc‖ ≤ 9 * C := by
  calc
    _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3,
        pressurePair i j (g i j) (PressureRecovery.realTest f hf hc)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        ‖pressurePair i j (g i j) (PressureRecovery.realTest f hf hc)‖ :=
      Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, C :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hbound i j))
    _ = 9 * C := by simp; ring

/-- The compact Schwartz test used on the uncommuted side of the Riesz operator. -/
def rTest (R : ℝ) (hR : 0 < R) (w : Space → Space) (hw : ContDiff ℝ ∞ w) :
    ComplexTest :=
  PressureRecovery.realTest (PressureFluxTest.cutoffTest R w)
    (PressureFluxTest.cutoffTest_smooth R hw) (PressureFluxTest.cutoffTest_hasCompactSupport hR w)

/-- The actual flux test `Dχ_R[w]`, represented in the Schwartz space. -/
def fluxTest (R : ℝ) (hR : 0 < R) (w : Space → Space) (hw : ContDiff ℝ ∞ w) :
    ComplexTest :=
  PressureRecovery.realTest (fluxFunction (ComparisonCutoffs.weight R) w)
    (fluxFunction_smooth (ComparisonCutoffs.weight_smooth R) hw)
    (fluxFunction_compact (ComparisonCutoffs.weight_hasCompactSupport hR) w)

@[simp] theorem rTest_apply (R : ℝ) (hR : 0 < R) (w : Space → Space)
    (hw : ContDiff ℝ ∞ w) (x : Space) :
    rTest R hR w hw x = (PressureFluxTest.cutoffTest R w x : ℂ) := rfl

@[simp] theorem fluxTest_apply (R : ℝ) (hR : 0 < R) (w : Space → Space)
    (hw : ContDiff ℝ ∞ w) (x : Space) :
    fluxTest R hR w hw x = (fderiv ℝ (ComparisonCutoffs.weight R) x (w x) : ℂ) := rfl

theorem fluxTest_eq_multiplier_rTest (R : ℝ) (hR : 0 < R) (w : Space → Space)
    (hw : ContDiff ℝ ∞ w) (x : Space) :
    fluxTest R hR w hw x = ComparisonCutoffs.cutoff R x ^ 2 • rTest R hR w hw x := by
  rw [fluxTest_apply, rTest_apply, ← PressureFluxTest.cutoffTest_flux_identity]
  simp [ComparisonCutoffs.multiplier, Complex.real_smul]

theorem lpNorm_rTest (R : ℝ) (hR : 0 < R) (w : Space → Space)
    (hw : ContDiff ℝ ∞ w) (p : ℝ≥0∞) :
    comparisonLpNorm p (rTest R hR w hw : Space → ℂ) = comparisonLpNorm p (PressureFluxTest.cutoffTest R w) :=
  lpNorm_ofReal _ _ (PressureFluxTest.cutoffTest_smooth R hw).continuous.aestronglyMeasurable

theorem lpNorm_fderiv_rTest (R : ℝ) (hR : 0 < R) (w : Space → Space)
    (hw : ContDiff ℝ ∞ w) :
    comparisonLpNorm 2 (fderiv ℝ (fun x => rTest R hR w hw x)) =
      comparisonLpNorm 2 (fderiv ℝ (PressureFluxTest.cutoffTest R w)) :=
  lpNorm_fderiv_realTest _ _ _ _

/-- Canonical flux for a time slice of the difference of two velocities. -/
def canonicalCutoffFlux (R : ℝ) (hR : 0 < R) (u v : VelocityField) (t : ℝ)
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x))) : ℂ :=
  canonicalFlux (tensorDiff u v t)
    (fluxFunction (ComparisonCutoffs.weight R) (fun x => (u - v) (t, x)))
    (fluxFunction_smooth (ComparisonCutoffs.weight_smooth R) (hu.sub hv))
    (fluxFunction_compact (ComparisonCutoffs.weight_hasCompactSupport hR) _)


theorem norm_canonicalCutoffFlux_le (R : ℝ) (hR : 0 < R) (u v : VelocityField) (t : ℝ)
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    {C : ℝ} (hbound : ∀ i j : Fin 3, ‖pressurePair i j (tensorDiff u v t i j)
      (fluxTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))‖ ≤ C) :
    ‖canonicalCutoffFlux R hR u v t hu hv‖ ≤ 9 * C :=
  norm_canonicalFlux_le _ _ hbound

theorem actual_flux_eq_canonicalCutoffFlux {T t R : ℝ} {u v : VelocityField}
    {p q : PressureField} (H : PressureRecovery.Hypotheses T u v p q)
    (ht : t ∈ Ioo 0 T) (hR : 0 < R)
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x))) :
    (∫ x, (p - q) (t, x) * fderiv ℝ (ComparisonCutoffs.weight R) x ((u - v) (t, x))) =
      (canonicalCutoffFlux R hR u v t hu hv).re := by
  simpa only [canonicalCutoffFlux, canonicalFlux, fluxFunction] using!
    ActualPressureFlux.pressure_flux_eq_canonical H ht
      (ComparisonCutoffs.weight_smooth R) (ComparisonCutoffs.weight_hasCompactSupport hR)

theorem actual_flux_integrable_and_le_canonicalNorm {T t R : ℝ} {u v : VelocityField}
    {p q : PressureField} (H : PressureRecovery.Hypotheses T u v p q)
    (ht : t ∈ Ioo 0 T) (hR : 0 < R)
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x))) :
    Integrable (fun x => (p - q) (t, x) *
      fderiv ℝ (ComparisonCutoffs.weight R) x ((u - v) (t, x))) volume ∧
    |∫ x, (p - q) (t, x) * fderiv ℝ (ComparisonCutoffs.weight R) x ((u - v) (t, x))| ≤
      ‖canonicalCutoffFlux R hR u v t hu hv‖ := by
  refine ⟨ActualPressureFlux.actual_pressure_flux_integrable H ht
    (ComparisonCutoffs.weight_smooth R) (ComparisonCutoffs.weight_hasCompactSupport hR), ?_⟩
  rw [actual_flux_eq_canonicalCutoffFlux H ht hR hu hv]
  exact Complex.abs_re_le_norm _

/-- The commutator integral in the heat-kernel estimate. -/
def commutatorPair (i j : Fin 3) (h g : Space → ℝ) (ψ ψh : ComplexTest) : ℂ :=
  ∫ x, g x • (rieszTest i j ψh x - h x • rieszTest i j ψ x)


theorem pressurePair_decomposition (i j : Fin 3) {h g : Space → ℝ}
    (hg : Integrable g volume) (hhg : MemLp (fun x => h x * g x) (6 / 5) volume)
    (ψ ψh : ComplexTest) :
    pressurePair i j g ψh =
      (∫ x, (h x * g x : ℝ) * rieszTest i j ψ x) + commutatorPair i j h g ψ ψh := by
  have hgc : Integrable (fun x => (g x : ℂ)) volume := by
    simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp hg
  have hq := RieszTestOperators.integrable_mul_rieszTest i j ψh hgc
  have hl := integrable_holder_pair hhg (RieszTestOperators.memLp_rieszTest_six i j ψ)
  have he : commutatorPair i j h g ψ ψh = pressurePair i j g ψh -
      (∫ x, (h x * g x : ℝ) * rieszTest i j ψ x) := by
    rw [commutatorPair, pressurePair, ← integral_sub hq hl]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [Complex.real_smul, Complex.ofReal_mul]
      ring
  simpa only [add_comm] using (eq_sub_iff_add_eq.mp he).symm


/-- The fixed constant in the actual Riesz-test Sobolev inequality. -/
def rieszSobolevConstant : ℝ := 3 * WeightedSobolev.sobolevConstant

theorem rieszSobolevConstant_nonneg : 0 ≤ rieszSobolevConstant :=
  mul_nonneg (by norm_num) WeightedSobolev.sobolevConstant_nonneg

def localPairConstant : ℝ := rieszSobolevConstant * PressureFluxTest.cutoffDerivativeConstant

theorem localPairConstant_nonneg : 0 ≤ localPairConstant :=
  mul_nonneg rieszSobolevConstant_nonneg PressureFluxTest.cutoffDerivativeConstant_pos.le

theorem riesz_rTest_bound {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) (i j : Fin 3) :
    comparisonLpNorm 6 (rieszTest i j (rTest R hR w hw)) ≤ localPairConstant *
      (Real.sqrt (∫ x, ComparisonCutoffs.cutoff R x ^ 8 * gradientSq w x) / R +
        comparisonLpNorm 2 w / R ^ 2) := by
  calc
    _ ≤ rieszSobolevConstant * comparisonLpNorm 2 (fderiv ℝ (fun x => rTest R hR w hw x)) := by
      simpa only [rieszSobolevConstant, WeightedSobolev.sobolevConstant] using
        RieszTestOperators.lpNorm_six_rieszTest_le i j (rTest R hR w hw)
    _ = rieszSobolevConstant * comparisonLpNorm 2 (fderiv ℝ (PressureFluxTest.cutoffTest R w)) := by
      rw [lpNorm_fderiv_rTest]
    _ ≤ rieszSobolevConstant * ((PressureFluxTest.cutoffDerivativeConstant / R) *
        Real.sqrt (∫ x, ComparisonCutoffs.cutoff R x ^ 8 * gradientSq w x) +
          (PressureFluxTest.cutoffDerivativeConstant / R ^ 2) * comparisonLpNorm 2 w) :=
      mul_le_mul_of_nonneg_left (PressureFluxTest.cutoffTest_derivative_bound hR hw hw2).2
        rieszSobolevConstant_nonneg
    _ = _ := by unfold localPairConstant; ring

theorem rTest_four_bound {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) :
    comparisonLpNorm 4 (rTest R hR w hw : Space → ℂ) ≤
      (8 * ComparisonCutoffs.derivativeConstant 1 / R) * comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
        comparisonLpNorm 6 (fun x => ComparisonCutoffs.cutoff R x ^ 4 • w x) ^ (3 / 4 : ℝ) := by
  rw [lpNorm_rTest]
  exact (PressureFluxTest.cutoffTest_four_bound hR hw hw2).2

/-- The local part of one canonical pressure component is an actual integrable pairing. -/
theorem localized_pair_bound {R : ℝ} (hR : 0 < R) {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hu3 : MemLp (fun x => u (t, x)) 3 volume) (i j : Fin 3) :
    Integrable (fun x => (ComparisonCutoffs.multiplier R x * tensorDiff u v t i j x : ℝ) *
      rieszTest i j (rTest R hR (fun x => (u - v) (t, x)) (hu.sub hv)) x) volume ∧
    ‖∫ x, (ComparisonCutoffs.multiplier R x * tensorDiff u v t i j x : ℝ) *
      rieszTest i j (rTest R hR (fun x => (u - v) (t, x)) (hu.sub hv)) x‖ ≤
      localPairConstant *
        (comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
            cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) +
          2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t, x))) *
        (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R +
          comparisonLpNorm 2 (fun x => (u - v) (t, x)) / R ^ 2) := by
  have ht := LocalizedTensorBounds.weighted_tensorDiff_bound
    (ComparisonCutoffs.cutoff_smooth R).continuous
    (ComparisonCutoffs.cutoff_hasCompactSupport hR) hu.continuous hv.continuous hw2 hu3
    (ComparisonCutoffs.cutoff_nonneg R) (ComparisonCutoffs.cutoff_le_one R) i j
  have hr := RieszTestOperators.memLp_rieszTest_six i j
    (rTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))
  refine ⟨integrable_holder_pair ht.1 hr, ?_⟩
  have hM := LpNormTools.lpNorm_nonneg 2 (fun x => (u - v) (t, x))
  have hU := LpNormTools.lpNorm_nonneg 3 (fun x => u (t, x))
  have hB := LpNormTools.lpNorm_nonneg 6 (fun x => ComparisonCutoffs.cutoff R x ^ 4 • (u - v) (t, x))
  calc
    _ ≤ comparisonLpNorm (6 / 5) (fun x => ComparisonCutoffs.cutoff R x ^ 2 * tensorDiff u v t i j x) *
        comparisonLpNorm 6 (rieszTest i j (rTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))) :=
      norm_holder_pair_le ht.1 hr
    _ ≤ (comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
            cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) +
          2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t, x))) *
        (localPairConstant * (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R +
          comparisonLpNorm 2 (fun x => (u - v) (t, x)) / R ^ 2)) := by
      apply mul_le_mul ht.2 (riesz_rTest_bound hR (hu.sub hv) hw2 i j)
        (LpNormTools.lpNorm_nonneg _ _)
      unfold cutoffL6
      positivity
    _ = _ := by ring

theorem norm_cutoff_pressurePair_le_local_commutator {R : ℝ} (hR : 0 < R)
    {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hu3 : MemLp (fun x => u (t, x)) 3 volume) (i j : Fin 3)
    (hg : Integrable (tensorDiff u v t i j) volume) :
    ‖pressurePair i j (tensorDiff u v t i j)
      (fluxTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))‖ ≤
      localPairConstant *
        (comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
            cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) +
          2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t, x))) *
        (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R +
          comparisonLpNorm 2 (fun x => (u - v) (t, x)) / R ^ 2) +
      ‖commutatorPair i j (ComparisonCutoffs.multiplier R) (tensorDiff u v t i j)
        (rTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))
        (fluxTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))‖ := by
  have ht := LocalizedTensorBounds.weighted_tensorDiff_bound
    (ComparisonCutoffs.cutoff_smooth R).continuous
    (ComparisonCutoffs.cutoff_hasCompactSupport hR) hu.continuous hv.continuous hw2 hu3
    (ComparisonCutoffs.cutoff_nonneg R) (ComparisonCutoffs.cutoff_le_one R) i j
  rw [pressurePair_decomposition i j hg ht.1]
  exact (norm_add_le _ _).trans (add_le_add_left (localized_pair_bound hR hu hv hw2 hu3 i j).2 _)

/-- The coefficient after fixing uniform bounds for the three data norms. -/
def uniformCoefficient (C₁ C₂ M₀ U₀ G₀ : ℝ) : ℝ :=
  C₁ * (M₀ ^ (3 / 2 : ℝ) + 2 * M₀ * U₀) * (M₀ + 1) +
    C₂ * G₀ * M₀ ^ (1 / 4 : ℝ)

theorem uniformCoefficient_nonneg {C₁ C₂ M₀ U₀ G₀ : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hM₀ : 0 ≤ M₀) (hU₀ : 0 ≤ U₀) (hG₀ : 0 ≤ G₀) :
    0 ≤ uniformCoefficient C₁ C₂ M₀ U₀ G₀ := by
  unfold uniformCoefficient
  positivity

/-- Collecting constants uses only the fixed data-norm bounds, not the radius. -/
theorem uniform_expression_bound {C₁ C₂ M₀ U₀ G₀ M U G A B R : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hM₀ : 0 ≤ M₀) (hU₀ : 0 ≤ U₀) (hG₀ : 0 ≤ G₀)
    (hM : 0 ≤ M) (hU : 0 ≤ U) (_hG : 0 ≤ G) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hMM : M ≤ M₀) (hUU : U ≤ U₀) (hGG : G ≤ G₀) (hR : 0 < R) :
    C₁ * (M ^ (3 / 2 : ℝ) * B ^ (1 / 2 : ℝ) + 2 * M * U) *
        (A / R + M / R ^ 2) +
      C₂ * G * M ^ (1 / 4 : ℝ) * R ^ (-(7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ) ≤
    uniformCoefficient C₁ C₂ M₀ U₀ G₀ *
      ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) +
        R ^ (-(7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ)) := by
  have hMp := Real.rpow_le_rpow hM hMM (by norm_num : 0 ≤ (3 / 2 : ℝ))
  have hMp₄ := Real.rpow_le_rpow hM hMM (by norm_num : 0 ≤ (1 / 4 : ℝ))
  have hB₁ := Real.rpow_nonneg hB (1 / 2 : ℝ)
  have hB₃ := Real.rpow_nonneg hB (3 / 4 : ℝ)
  have hM₀p := Real.rpow_nonneg hM₀ (3 / 2 : ℝ)
  have hM₀p₄ := Real.rpow_nonneg hM₀ (1 / 4 : ℝ)
  have hRp := Real.rpow_nonneg hR.le (-(7 / 4 : ℝ))
  have hMU : 2 * M * U ≤ 2 * M₀ * U₀ :=
    mul_le_mul (mul_le_mul_of_nonneg_left hMM (by norm_num)) hUU hU (by positivity)
  have hT : M ^ (3 / 2 : ℝ) * B ^ (1 / 2 : ℝ) + 2 * M * U ≤
      (M₀ ^ (3 / 2 : ℝ) + 2 * M₀ * U₀) * (B ^ (1 / 2 : ℝ) + 1) := by
    have h := add_le_add (mul_le_mul_of_nonneg_right hMp hB₁) hMU
    have hm0u0 : 0 ≤ 2 * M₀ * U₀ := by positivity
    exact h.trans (by nlinarith only [hM₀p, mul_nonneg hm0u0 hB₁])
  have hAR : 0 ≤ A / R := div_nonneg hA hR.le
  have hInv : 0 ≤ 1 / R ^ 2 := by positivity
  have hD : A / R + M / R ^ 2 ≤ (M₀ + 1) * (A / R + 1 / R ^ 2) := by
    have hdiv := (div_le_div_iff_of_pos_right (sq_pos_of_pos hR)).2 hMM
    have hdiv' : M / R ^ 2 ≤ M₀ * (1 / R ^ 2) := by simpa only [mul_one_div] using hdiv
    nlinarith only [hdiv', mul_nonneg hM₀ hAR, hInv]
  have hlocal :
      C₁ * (M ^ (3 / 2 : ℝ) * B ^ (1 / 2 : ℝ) + 2 * M * U) * (A / R + M / R ^ 2) ≤
      (C₁ * (M₀ ^ (3 / 2 : ℝ) + 2 * M₀ * U₀) * (M₀ + 1)) *
        ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2)) := by
    calc
      _ ≤ (C₁ * ((M₀ ^ (3 / 2 : ℝ) + 2 * M₀ * U₀) * (B ^ (1 / 2 : ℝ) + 1))) *
          ((M₀ + 1) * (A / R + 1 / R ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hT hC₁) hD (by positivity) (by positivity)
      _ = _ := by ring
  have hcoeff : C₂ * G * M ^ (1 / 4 : ℝ) ≤ C₂ * G₀ * M₀ ^ (1 / 4 : ℝ) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hGG hC₂) hMp₄
      (Real.rpow_nonneg hM _) (mul_nonneg hC₂ hG₀)
  have hcomm : C₂ * G * M ^ (1 / 4 : ℝ) * R ^ (-(7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ) ≤
      (C₂ * G₀ * M₀ ^ (1 / 4 : ℝ)) * (R ^ (-(7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ)) := by
    calc
      _ = (C₂ * G * M ^ (1 / 4 : ℝ)) * (R ^ (-(7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hRp hB₃)
  have hK₁ : 0 ≤ C₁ * (M₀ ^ (3 / 2 : ℝ) + 2 * M₀ * U₀) * (M₀ + 1) := by positivity
  have hK₂ : 0 ≤ C₂ * G₀ * M₀ ^ (1 / 4 : ℝ) := by positivity
  have hE₁ : 0 ≤ (B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) := by positivity
  have hE₂ : 0 ≤ R ^ (-(7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ) := mul_nonneg hRp hB₃
  unfold uniformCoefficient
  nlinarith only [add_le_add hlocal hcomm, mul_nonneg hK₁ hE₂, mul_nonneg hK₂ hE₁]

theorem rpow_three_fourths_div {R : ℝ} (hR : 0 < R) :
    R ^ (-(3 / 4 : ℝ)) / R = R ^ (-(7 / 4 : ℝ)) := by
  rw [div_eq_mul_inv, ← Real.rpow_neg_one R, ← Real.rpow_add hR]
  norm_num

/-- The fixed coefficient after combining the commutator and test-function bounds. -/
def commutatorConstant : ℝ :=
  (Comparison.rieszCommutatorConstant * max (2 * ComparisonCutoffs.derivativeConstant 1) 1) *
    (8 * ComparisonCutoffs.derivativeConstant 1)

theorem commutatorConstant_nonneg : 0 ≤ commutatorConstant := by
  have hH := Comparison.rieszCommutatorConstant_pos.le
  have hD := (ComparisonCutoffs.derivativeConstant_pos 1).le
  have hm : 0 ≤ max (2 * ComparisonCutoffs.derivativeConstant 1) 1 :=
    zero_le_one.trans (le_max_right _ _)
  unfold commutatorConstant
  positivity

theorem cutoff_commutator_bound {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) {g : Space → ℝ}
    (hg : Integrable g volume) (i j : Fin 3) :
    ‖commutatorPair i j (ComparisonCutoffs.multiplier R) g
      (rTest R hR w hw) (fluxTest R hR w hw)‖ ≤
      commutatorConstant * comparisonLpNorm 1 g * comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
        R ^ (-(7 / 4 : ℝ)) *
          comparisonLpNorm 6 (fun x => ComparisonCutoffs.cutoff R x ^ 4 • w x) ^ (3 / 4 : ℝ) := by
  have h := Comparison.riesz_commutator_pair_bound i j hR
    (ComparisonCutoffs.cutoff_smooth R).continuous.measurable
    (ComparisonCutoffs.cutoff_mem_Icc R) (cutoff_lipschitz hR) hg
    (rTest R hR w hw) (fluxTest R hR w hw)
    (fluxTest_eq_multiplier_rTest R hR w hw) ((rTest R hR w hw).memLp 4)
  have hH := Comparison.rieszCommutatorConstant_pos.le
  have hD := (ComparisonCutoffs.derivativeConstant_pos 1).le
  have hm : 0 ≤ max (2 * ComparisonCutoffs.derivativeConstant 1) 1 :=
    zero_le_one.trans (le_max_right _ _)
  have hG := LpNormTools.lpNorm_nonneg 1 g
  have hRp := Real.rpow_nonneg hR.le (-(3 / 4 : ℝ))
  calc
    _ ≤ (Comparison.rieszCommutatorConstant * max (2 * ComparisonCutoffs.derivativeConstant 1) 1) *
        R ^ (-(3 / 4 : ℝ)) * comparisonLpNorm 1 g * comparisonLpNorm 4 (rTest R hR w hw : Space → ℂ) := h
    _ ≤ (Comparison.rieszCommutatorConstant * max (2 * ComparisonCutoffs.derivativeConstant 1) 1) *
        R ^ (-(3 / 4 : ℝ)) * comparisonLpNorm 1 g *
          ((8 * ComparisonCutoffs.derivativeConstant 1 / R) * comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
            comparisonLpNorm 6 (fun x => ComparisonCutoffs.cutoff R x ^ 4 • w x) ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (rTest_four_bound hR hw hw2) (by positivity)
    _ = _ := by
      rw [← rpow_three_fourths_div hR]
      unfold commutatorConstant
      ring

/-- One actual canonical pressure component, with the three data norms explicit. -/
theorem cutoff_pressurePair_bound {R : ℝ} (hR : 0 < R) {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hu3 : MemLp (fun x => u (t, x)) 3 volume) (i j : Fin 3)
    (hg : Integrable (tensorDiff u v t i j) volume) :
    ‖pressurePair i j (tensorDiff u v t i j)
      (fluxTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))‖ ≤
      localPairConstant *
        (comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
            cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) +
          2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t, x))) *
        (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R +
          comparisonLpNorm 2 (fun x => (u - v) (t, x)) / R ^ 2) +
      commutatorConstant * comparisonLpNorm 1 (tensorDiff u v t i j) *
        comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (1 / 4 : ℝ) * R ^ (-(7 / 4 : ℝ)) *
          cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (3 / 4 : ℝ) :=
  (norm_cutoff_pressurePair_le_local_commutator hR hu hv hw2 hu3 i j hg).trans
    (add_le_add_right (cutoff_commutator_bound hR (hu.sub hv) hw2 hg i j) _)

/-- The full canonical flux with an explicit bound on each tensor component's `L¹` norm. -/
theorem canonicalCutoffFlux_bound {R : ℝ} (hR : 0 < R) {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hu3 : MemLp (fun x => u (t, x)) 3 volume)
    (hg : ∀ i j : Fin 3, Integrable (tensorDiff u v t i j) volume)
    {G : ℝ} (hG : ∀ i j : Fin 3, comparisonLpNorm 1 (tensorDiff u v t i j) ≤ G) :
    ‖canonicalCutoffFlux R hR u v t hu hv‖ ≤ 9 *
      (localPairConstant *
        (comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
            cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) +
          2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t, x))) *
        (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R +
          comparisonLpNorm 2 (fun x => (u - v) (t, x)) / R ^ 2) +
      commutatorConstant * G * comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (1 / 4 : ℝ) *
        R ^ (-(7 / 4 : ℝ)) * cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (3 / 4 : ℝ)) := by
  apply norm_canonicalCutoffFlux_le
  intro i j
  refine (cutoff_pressurePair_bound hR hu hv hw2 hu3 i j (hg i j)).trans (add_le_add_right ?_ _)
  have hM := Real.rpow_nonneg
    (LpNormTools.lpNorm_nonneg 2 (fun x => (u - v) (t, x))) (1 / 4 : ℝ)
  have hB := Real.rpow_nonneg
    (LpNormTools.lpNorm_nonneg 6 (fun x => ComparisonCutoffs.cutoff R x ^ 4 • (u - v) (t, x)))
    (3 / 4 : ℝ)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hG i j) commutatorConstant_nonneg) hM)
      (Real.rpow_nonneg hR.le _)) hB

/-- One constant works for all radii and all smooth slices satisfying the fixed norm bounds. -/
theorem exists_uniform_canonicalCutoffFlux_bound (M₀ U₀ G₀ : ℝ)
    (hM₀ : 0 ≤ M₀) (hU₀ : 0 ≤ U₀) (hG₀ : 0 ≤ G₀) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ (R : ℝ) (hR : 1 ≤ R) (u v : VelocityField) (t : ℝ)
      (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x))),
      MemLp (fun x => (u - v) (t, x)) 2 volume →
      MemLp (fun x => u (t, x)) 3 volume →
      (∀ i j : Fin 3, Integrable (tensorDiff u v t i j) volume) →
      comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤ M₀ →
      comparisonLpNorm 3 (fun x => u (t, x)) ≤ U₀ →
      (∀ i j : Fin 3, comparisonLpNorm 1 (tensorDiff u v t i j) ≤ G₀) →
      ‖canonicalCutoffFlux R (zero_lt_one.trans_le hR) u v t hu hv‖ ≤ CP *
        ((cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) + 1) *
          (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R + 1 / R ^ 2) +
          R ^ (-(7 / 4 : ℝ)) * cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (3 / 4 : ℝ)) := by
  refine ⟨9 * uniformCoefficient localPairConstant commutatorConstant M₀ U₀ G₀,
    mul_nonneg (by norm_num)
      (uniformCoefficient_nonneg localPairConstant_nonneg commutatorConstant_nonneg hM₀ hU₀ hG₀), ?_⟩
  intro R hR u v t hu hv hw2 hu3 hg hM hU hG
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hA : 0 ≤ dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t := Real.sqrt_nonneg _
  have hB : 0 ≤ cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t :=
    LpNormTools.lpNorm_nonneg _ _
  have hn := uniform_expression_bound localPairConstant_nonneg commutatorConstant_nonneg
    hM₀ hU₀ hG₀ (LpNormTools.lpNorm_nonneg 2 (fun x => (u - v) (t, x)))
    (LpNormTools.lpNorm_nonneg 3 (fun x => u (t, x))) hG₀ hA hB hM hU (le_refl G₀) hR0
  have hp := canonicalCutoffFlux_bound hR0 hu hv hw2 hu3 hg hG
  simpa only [mul_assoc] using hp.trans (mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 9))

/-- The physical pressure flux has a single bound uniform in time and cutoff radius.
All hypotheses on the pressure are exactly those already present in pressure recovery. -/
theorem exists_uniform_actual_pressure_flux_bound {T : ℝ} {u v : VelocityField}
    {p q : PressureField} (H : PressureRecovery.Hypotheses T u v p q)
    (M₀ U₀ G₀ : ℝ) (hM₀ : 0 ≤ M₀) (hU₀ : 0 ≤ U₀) (hG₀ : 0 ≤ G₀)
    (hM : ∀ t ∈ Icc 0 T, MemLp (fun x => (u - v) (t, x)) 2 volume ∧
      comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤ M₀)
    (hU : ∀ t ∈ Icc 0 T, MemLp (fun x => u (t, x)) 3 volume ∧
      comparisonLpNorm 3 (fun x => u (t, x)) ≤ U₀)
    (hG : ∀ t ∈ Icc 0 T, ∀ i j : Fin 3,
      Integrable (tensorDiff u v t i j) volume ∧ comparisonLpNorm 1 (tensorDiff u v t i j) ≤ G₀) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ R : ℝ, 1 ≤ R → ∀ t ∈ Ioo 0 T,
      |∫ x, (p - q) (t, x) * fderiv ℝ (ComparisonCutoffs.weight R) x ((u - v) (t, x))| ≤ CP *
        ((cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) + 1) *
          (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R + 1 / R ^ 2) +
          R ^ (-(7 / 4 : ℝ)) * cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (3 / 4 : ℝ)) := by
  obtain ⟨CP, hCP, hbound⟩ := exists_uniform_canonicalCutoffFlux_bound M₀ U₀ G₀ hM₀ hU₀ hG₀
  refine ⟨CP, hCP, ?_⟩
  intro R hR t ht
  have ht' : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have hu := NavierStokes.PeriodicUniqueness.spatial_smooth H.smooth_u ht'
  have hv := NavierStokes.PeriodicUniqueness.spatial_smooth H.smooth_v ht'
  exact (actual_flux_integrable_and_le_canonicalNorm H ht (zero_lt_one.trans_le hR) hu hv).2.trans
    (hbound R hR u v t hu hv (hM t ht').1 (hU t ht').1 (fun i j => (hG t ht' i j).1)
      (hM t ht').2 (hU t ht').2 (fun i j => (hG t ht' i j).2))

end NavierStokesR3.PressureFlux

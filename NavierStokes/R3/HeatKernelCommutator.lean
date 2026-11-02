import NavierStokes.R3.HeatKernelCancellation
import NavierStokes.R3.HeatKernelFourier
import NavierStokes.R3.ComparisonFourierSetup
import NavierStokes.R3.HeatKernelFubini
import NavierStokes.R3.HeatKernelPairedBound

/-!
# The pressure commutator

The Fourier-defined double Riesz operator has the actual heat representation.
We first subtract the two time-integrable heat evolutions, insert the cutoff
difference, and only then use the absolute-integrability theorem to interchange
time and space. The resulting kernel has the proved radial `L^(4/3)` majorant.
-/

/-! Merged from `NavierStokes.R3.FourierConvolution`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# An inverse Fourier multiplier as a convolution

For integrable `A` and `ψ`, the inverse Fourier transform of `A * Fourier ψ`
is the convolution of `inverseFourier A` with `ψ`.  Absolute product
integrability also proves that the spatial convolution exists at every point;
no global integrability of `inverseFourier A` is required.
-/


noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace NavierStokesR3.Comparison

open ProblemStatement

private theorem integrable_inverseFourierProduct {A ψ : Space → ℂ}
    (hA : Integrable A) (hψ : Integrable ψ) (x : Space) :
    Integrable (fun p : Space × Space =>
      Real.fourierChar ⟪p.1, x - p.2⟫ • (A p.1 * ψ p.2))
      ((volume : Measure Space).prod (volume : Measure Space)) := by
  have hp : Continuous (fun p : Space × Space => Real.fourierChar ⟪p.1, x - p.2⟫) :=
    Real.continuous_fourierChar.comp
      (continuous_fst.inner (continuous_const.sub continuous_snd))
  refine (hA.norm.mul_prod hψ.norm).mono' ?_ ?_
  · exact hp.aestronglyMeasurable.smul
      (hA.aestronglyMeasurable.comp_fst.mul hψ.aestronglyMeasurable.comp_snd)
  · exact Filter.Eventually.of_forall fun p => by
      simp only [Circle.norm_smul, norm_mul, le_refl]

private theorem inverseFourierProduct_integral_frequency (A ψ : Space → ℂ)
    (x y : Space) :
    (∫ ξ : Space, Real.fourierChar ⟪ξ, x - y⟫ • (A ξ * ψ y)) =
      FourierTransform.fourierInv A (x - y) * ψ y := by
  rw [Real.fourierInv_eq]
  simp only [Circle.smul_def, smul_eq_mul, ← mul_assoc, integral_mul_const]

private theorem inverseFourierProduct_integral_space (A ψ : Space → ℂ)
    (x ξ : Space) :
    (∫ y : Space, Real.fourierChar ⟪ξ, x - y⟫ • (A ξ * ψ y)) =
      Real.fourierChar ⟪ξ, x⟫ • (A ξ * FourierTransform.fourier ψ ξ) := by
  rw [Real.fourier_eq]
  calc
    (∫ y : Space, Real.fourierChar ⟪ξ, x - y⟫ • (A ξ * ψ y)) =
        ∫ y : Space, Real.fourierChar ⟪ξ, x⟫ •
          (A ξ * (Real.fourierChar (-⟪y, ξ⟫) • ψ y)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      have hphase : Real.fourierChar ⟪ξ, x - y⟫ =
          Real.fourierChar ⟪ξ, x⟫ * Real.fourierChar (-⟪y, ξ⟫) := by
        rw [← Real.fourierChar.map_add_eq_mul]
        congr 1
        rw [inner_sub_right, real_inner_comm y ξ]
        ring
      rw [hphase, mul_smul]
      simp only [Circle.smul_def, smul_eq_mul]
      ring
    _ = Real.fourierChar ⟪ξ, x⟫ •
        (A ξ * ∫ y : Space, Real.fourierChar (-⟪y, ξ⟫) • ψ y) := by
      simp only [Circle.smul_def, smul_eq_mul, integral_const_mul]

/-- Convolution with an inverse Fourier transform is integrable at every fixed point. -/
theorem integrable_fourierIntegralInv_convolution {A ψ : Space → ℂ}
    (hA : Integrable A) (hψ : Integrable ψ) (x : Space) :
    Integrable (fun y : Space => FourierTransform.fourierInv A (x - y) * ψ y) := by
  apply (integrable_inverseFourierProduct hA hψ x).integral_prod_right.congr
  exact Filter.Eventually.of_forall fun y =>
    inverseFourierProduct_integral_frequency A ψ x y

/-- Multiplication by an integrable Fourier multiplier becomes a spatial convolution. -/
theorem fourierIntegralInv_mul_fourier {A ψ : Space → ℂ}
    (hA : Integrable A) (hψ : Integrable ψ) (x : Space) :
    FourierTransform.fourierInv (fun ξ : Space => A ξ * FourierTransform.fourier ψ ξ) x =
      ∫ y : Space, FourierTransform.fourierInv A (x - y) * ψ y := by
  calc
    FourierTransform.fourierInv (fun ξ : Space => A ξ * FourierTransform.fourier ψ ξ) x =
        ∫ ξ : Space, ∫ y : Space,
          Real.fourierChar ⟪ξ, x - y⟫ • (A ξ * ψ y) := by
      rw [Real.fourierInv_eq]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ =>
        (inverseFourierProduct_integral_space A ψ x ξ).symm
    _ = ∫ y : Space, ∫ ξ : Space,
        Real.fourierChar ⟪ξ, x - y⟫ • (A ξ * ψ y) :=
      integral_integral_swap (integrable_inverseFourierProduct hA hψ x)
    _ = ∫ y : Space, FourierTransform.fourierInv A (x - y) * ψ y := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y =>
        inverseFourierProduct_integral_frequency A ψ x y

end NavierStokesR3.Comparison


end



noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace NavierStokesR3.Comparison

open ProblemStatement

private theorem real_smul_as_complex_mul (a : ℝ) (z : ℂ) :
    a • z = (a : ℂ) * z := by
  rw [Algebra.smul_def]
  rfl

private theorem integrable_real_smul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℂ} (hf : Integrable f μ) (a : ℝ) :
    Integrable (fun x => a • f x) μ := by
  simpa only [real_smul_as_complex_mul] using hf.const_mul (a : ℂ)

/-- Each positive-time Fourier multiplier is convolution with the actual heat Hessian. -/
theorem heatSecondTest_eq_convolution {s : ℝ} (hs : 0 < s) (i j : Fin 3)
    (ψ : ComplexTest) (x : Space) :
    heatSecondTest s i j ψ x =
      ∫ y : Space, heatKernelSecond s i j (x - y) • ψ y := by
  change FourierTransform.fourierInv (fun ξ : Space =>
    (heatSecondSymbol s i j ξ : ℂ) * FourierTransform.fourier (fun y => ψ y) ξ) x = _
  rw [fourierIntegralInv_mul_fourier (integrable_heatSecondSymbol_space hs i j)
    ψ.integrable x]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [fourierIntegralInv_heatSecondSymbol hs i j (x - y), real_smul_as_complex_mul]

/-- The spatial heat-Hessian convolution is integrable at each positive time. -/
theorem heatSecondTest_convolution_integrable {s : ℝ} (hs : 0 < s) (i j : Fin 3)
    (ψ : ComplexTest) (x : Space) :
    Integrable (fun y : Space => heatKernelSecond s i j (x - y) • ψ y) := by
  apply (integrable_fourierIntegralInv_convolution
    (integrable_heatSecondSymbol_space hs i j) ψ.integrable x).congr
  filter_upwards [] with y
  rw [fourierIntegralInv_heatSecondSymbol hs i j (x - y), real_smul_as_complex_mul]

/-- The pointwise Riesz commutator equals the absolutely convergent cancelled
heat kernel. The cutoff difference is inserted before spatial/time Fubini. -/
theorem riesz_commutator_eq_heatKernel (i j : Fin 3)
    {φ : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (ψ ψh : ComplexTest) (hψh : ∀ x, ψh x = φ x ^ 2 • ψ x)
    (hψ4 : MemLp (fun x => ψ x) 4 volume) (x : Space) :
    rieszTest i j ψh x - φ x ^ 2 • rieszTest i j ψ x =
      ∫ y : Space, heatCommutatorKernel i j φ x y • ψ y := by
  have htime1 := integrableOn_heatSecondTest i j ψh x
  have htime2 := integrable_real_smul (integrableOn_heatSecondTest i j ψ x) (φ x ^ 2)
  rw [rieszTest_eq_integral_heatSecondTest i j ψh x,
    rieszTest_eq_integral_heatSecondTest i j ψ x, ← integral_smul,
    ← integral_sub htime1 htime2]
  calc
    (∫ s : ℝ in Ioi 0,
        (heatSecondTest s i j ψh x - φ x ^ 2 • heatSecondTest s i j ψ x)) =
        ∫ s : ℝ in Ioi 0, ∫ y : Space,
          (heatKernelSecond s i j (x - y) * cutoffSquareDifference φ x y) • ψ y := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [heatSecondTest_eq_convolution hs i j ψh x,
        heatSecondTest_eq_convolution hs i j ψ x, ← integral_smul,
        ← integral_sub (heatSecondTest_convolution_integrable hs i j ψh x)
          (integrable_real_smul (heatSecondTest_convolution_integrable hs i j ψ x) (φ x ^ 2))]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hψh y]
      exact cutoffSquareDifference_smul (heatKernelSecond s i j (x - y)) φ (ψ y) x y
    _ = ∫ y : Space, heatCommutatorKernel i j φ x y • ψ y := by
      exact cancelledTimeKernel_integral_swap
        (heatKernelSecond_joint_measurable i j) hφm ψ.continuous.measurable
        (fun z hz => heatKernelSecond_integrable_time i j hz)
        heatKernelTimeConstant_pos.le hR
        (fun z hz => heatKernelSecond_integral_abs_le i j hz)
        hφ hLip hψ4 x

/-- The paired pressure commutator bound for the actual Fourier-defined Riesz operator. -/
theorem riesz_commutator_pair_bound (i j : Fin 3)
    {φ g : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (hg : Integrable g volume)
    (ψ ψh : ComplexTest) (hψh : ∀ x, ψh x = φ x ^ 2 • ψ x)
    (hψ4 : MemLp (fun x => ψ x) 4 volume) :
    ‖∫ x : Space, g x • (rieszTest i j ψh x - φ x ^ 2 • rieszTest i j ψ x)‖ ≤
      (rieszCommutatorConstant * max (2 * L) 1) * R ^ (-(3 / 4) : ℝ) *
        comparisonLpNorm 1 g * comparisonLpNorm 4 (fun x => ψ x) := by
  have heq : (fun x : Space => g x •
      (rieszTest i j ψh x - φ x ^ 2 • rieszTest i j ψ x)) =
      (fun x : Space => g x • ∫ y : Space, heatCommutatorKernel i j φ x y • ψ y) := by
    funext x
    rw [riesz_commutator_eq_heatKernel i j hR hφm hφ hLip ψ ψh hψh hψ4 x]
  rw [heq]
  exact heatKernel_paired_commutator_bound i j hR hφm hφ hLip hg hψ4

end NavierStokesR3.Comparison

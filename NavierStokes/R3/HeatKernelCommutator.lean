import NavierStokes.R3.ComparisonSetup
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import NavierStokes.R3.RieszTestOperators
import NavierStokes.R3.ComparisonFourierSetup
import NavierStokes.R3.RieszSymbolRegularity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Fourier.Inversion
import NavierStokes.R3.PairedKernelBound
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The pressure commutator

The Fourier-defined double Riesz operator has the actual heat representation.
We first subtract the two time-integrable heat evolutions, insert the cutoff
difference, and only then use the absolute-integrability theorem to interchange
time and space. The resulting kernel has the proved radial `L^(4/3)` majorant.
-/
/-! Merged from `NavierStokes.R3.HeatKernel` (in a section, so its `open`s cannot leak). -/
section
/-!
# The three dimensional heat kernel

The definitions in this file are the ordinary Gaussian heat kernel and its
coordinate Hessian.  The latter is proved to agree with the spatial derivatives
used in the comparison argument.
-/


noncomputable section

open scoped ContDiff

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- The Euclidean heat kernel in three spatial dimensions. -/
def heatKernel (s : ℝ) (z : Space) : ℝ :=
  (4 * Real.pi * s) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖z‖ ^ 2) / (4 * s))

/-- The explicit coordinate Hessian of the Euclidean heat kernel. -/
def heatKernelSecond (s : ℝ) (i j : Fin 3) (z : Space) : ℝ :=
  (z i * z j / (4 * s ^ 2) - (if i = j then 1 else 0) / (2 * s)) *
    heatKernel s z


theorem heatKernel_nonneg {s : ℝ} (hs : 0 ≤ s) (z : Space) :
    0 ≤ heatKernel s z := by
  unfold heatKernel
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)

theorem hasFDerivAt_heatKernel {s : ℝ} (hs : 0 < s) (z : Space) :
    HasFDerivAt (heatKernel s)
      ((-(heatKernel s z / (2 * s))) • innerSL ℝ z) z := by
  have he : HasFDerivAt (fun x : Space => -(‖x‖ ^ 2) / (4 * s))
      ((4 * s)⁻¹ • (-((2 : ℝ) • innerSL ℝ z))) z := by
    simpa only [Pi.neg_apply, div_eq_mul_inv, mul_comm, two_smul] using
      (hasStrictFDerivAt_norm_sq z).hasFDerivAt.neg.const_mul ((4 * s)⁻¹)
  convert! he.exp.const_mul ((4 * Real.pi * s) ^ (-(3 / 2 : ℝ))) using 1
  ext y
  simp only [_root_.smul_apply, _root_.neg_apply,
    innerSL_apply_apply, smul_eq_mul]
  unfold heatKernel
  field_simp
  ; ring

theorem partial_heatKernel {s : ℝ} (hs : 0 < s) (i : Fin 3) (z : Space) :
    partialD i (heatKernel s) z = -(z i / (2 * s)) * heatKernel s z := by
  unfold partialD NavierStokes.PeriodicIntegration.spatialPartial
  rw [(hasFDerivAt_heatKernel hs z).fderiv]
  simp [NavierStokes.ProblemStatement.coordinateVector,
    EuclideanSpace.inner_single_right]
  ring

theorem differentiable_heatKernel {s : ℝ} (hs : 0 < s) :
    Differentiable ℝ (heatKernel s) := fun z =>
  (hasFDerivAt_heatKernel hs z).differentiableAt


/-- The explicit Gaussian Hessian is the actual iterated coordinate derivative. -/
theorem heatKernelSecond_eq_partial {s : ℝ} (hs : 0 < s)
    (i j : Fin 3) (z : Space) :
    heatKernelSecond s i j z = partialD i (partialD j (heatKernel s)) z := by
  have hfirst : partialD j (heatKernel s) =
      (fun x : Space => -(x j / (2 * s)) * heatKernel s x) :=
    funext (partial_heatKernel hs j)
  have hc : HasFDerivAt (fun x : Space => x j)
      (innerSL ℝ (NavierStokes.ProblemStatement.coordinateVector j)) z := by
    convert! (innerSL ℝ (NavierStokes.ProblemStatement.coordinateVector j)).hasFDerivAt
      (x := z) using 1
    ext x
    simp [NavierStokes.ProblemStatement.coordinateVector,
      EuclideanSpace.inner_single_left]
  have hg : HasFDerivAt (fun x : Space => -(x j / (2 * s)))
      ((-((2 * s)⁻¹)) • innerSL ℝ (NavierStokes.ProblemStatement.coordinateVector j)) z := by
    convert! hc.const_mul (-((2 * s)⁻¹)) using 1
    ext x
    ring
  rw [hfirst]
  unfold partialD NavierStokes.PeriodicIntegration.spatialPartial
  change heatKernelSecond s i j z = fderiv ℝ ((fun x : Space => -(x j / (2 * s))) * heatKernel s) z (NavierStokes.ProblemStatement.coordinateVector i)
  rw [(hg.mul (hasFDerivAt_heatKernel hs z)).fderiv]
  by_cases hij : i = j
  · subst i
    simp [heatKernelSecond, NavierStokes.ProblemStatement.coordinateVector, EuclideanSpace.inner_single_right]
    ; field_simp
    ; ring
  · simp [heatKernelSecond, hij,
      NavierStokes.ProblemStatement.coordinateVector, EuclideanSpace.inner_single_right]
    ; field_simp
    ; ring

/-- A radial envelope for every component of the Gaussian Hessian. -/
theorem norm_heatKernelSecond_le {s : ℝ} (hs : 0 < s)
    (i j : Fin 3) (z : Space) :
    ‖heatKernelSecond s i j z‖ ≤
      (‖z‖ ^ 2 / (4 * s ^ 2) + 1 / (2 * s)) * heatKernel s z := by
  have hden₁ : 0 < 4 * s ^ 2 := by positivity
  have hden₂ : 0 < 2 * s := by positivity
  have hcoord : ‖z i * z j‖ ≤ ‖z‖ ^ 2 := by
    rw [norm_mul, pow_two]
    exact mul_le_mul (PiLp.norm_apply_le z i) (PiLp.norm_apply_le z j)
      (norm_nonneg _) (norm_nonneg _)
  have hdiag : ‖(if i = j then (1 : ℝ) else 0)‖ ≤ 1 := by
    split_ifs <;> norm_num
  have hcoeff :
      ‖z i * z j / (4 * s ^ 2) - (if i = j then 1 else 0) / (2 * s)‖ ≤
        ‖z‖ ^ 2 / (4 * s ^ 2) + 1 / (2 * s) := by
    calc
      _ ≤ ‖z i * z j / (4 * s ^ 2)‖ +
          ‖(if i = j then (1 : ℝ) else 0) / (2 * s)‖ := norm_sub_le _ _
      _ = ‖z i * z j‖ / (4 * s ^ 2) +
          ‖(if i = j then (1 : ℝ) else 0)‖ / (2 * s) := by
        simp only [norm_div, Real.norm_eq_abs, abs_of_pos hden₁, abs_of_pos hden₂]
      _ ≤ _ := add_le_add
        (div_le_div_of_nonneg_right hcoord hden₁.le)
        (div_le_div_of_nonneg_right hdiag hden₂.le)
  rw [heatKernelSecond, norm_mul, Real.norm_of_nonneg (heatKernel_nonneg hs.le z)]
  exact mul_le_mul_of_nonneg_right hcoeff (heatKernel_nonneg hs.le z)

end NavierStokesR3.Comparison
end

/-! Merged from `NavierStokes.R3.HeatKernelFourier`. -/
/-!
# Fourier representation of the heat kernel

The ordinary Gaussian Fourier formula is normalized to the three dimensional
heat kernel used in the comparison proof. Two justified differentiations of
the inverse Fourier integral identify the Hessian multiplier with its kernel.
-/
/-! Merged from `NavierStokes.R3.RieszHeatRepresentation` (in a section, so its `open`s cannot leak). -/
section
/-!
# Heat multipliers for the double Riesz transform

The Fourier convention has a factor `2 * π` in the character.  Consequently the
heat semigroup has multiplier `exp (-4 * π² * s * ‖ξ‖²)`.  Integrating its second
spatial derivative over positive time recovers the double Riesz multiplier.
-/


noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace NavierStokesR3.Comparison

open ProblemStatement

private theorem realAlgebraMap_apply (r : ℝ) : (algebraMap ℝ ℂ) r = (r : ℂ) := rfl

/-- The Fourier multiplier of a second derivative of the heat semigroup. -/
def heatSecondSymbol (s : ℝ) (i j : Fin 3) (ξ : Space) : ℝ :=
  -(4 * Real.pi ^ 2 * (ξ i * ξ j)) *
    Real.exp (-(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * s)

@[simp] theorem heatSecondSymbol_zero (s : ℝ) (i j : Fin 3) :
    heatSecondSymbol s i j 0 = 0 := by
  simp [heatSecondSymbol]

/-- Positive-time integrability holds also at the zero frequency. -/
theorem integrableOn_heatSecondSymbol (i j : Fin 3) (ξ : Space) :
    IntegrableOn (fun s => heatSecondSymbol s i j ξ) (Ioi 0) := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp only [heatSecondSymbol_zero]
    exact integrableOn_zero
  · have hpos : 0 < 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by
      positivity
    exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos hpos) 0).const_mul _

/-- Integrating the heat second-derivative multiplier gives the double Riesz symbol. -/
theorem integral_heatSecondSymbol (i j : Fin 3) (ξ : Space) :
    (∫ s : ℝ in Ioi 0, heatSecondSymbol s i j ξ) = rieszSymbol i j ξ := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp [rieszSymbol]
  · have hpos : 0 < 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by
      positivity
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hnorm : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
    simp only [heatSecondSymbol]
    rw [integral_const_mul,
      integral_exp_mul_Ioi (neg_neg_of_pos hpos)]
    simp only [mul_zero, Real.exp_zero]
    unfold rieszSymbol
    field_simp

/-- The absolute time integral is the absolute value of the Riesz symbol. -/
theorem integral_norm_heatSecondSymbol (i j : Fin 3) (ξ : Space) :
    (∫ s : ℝ in Ioi 0, ‖heatSecondSymbol s i j ξ‖) = ‖rieszSymbol i j ξ‖ := by
  rw [← integral_heatSecondSymbol i j ξ]
  simp only [heatSecondSymbol, norm_mul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), integral_const_mul]
  rw [abs_of_nonneg (integral_nonneg fun _ => (Real.exp_pos _).le)]

/-- A second derivative of the heat evolution, expressed in frequency space. -/
def heatSecondTest (s : ℝ) (i j : Fin 3) (ψ : ComplexTest) : Space → ℂ :=
  FourierTransform.fourierInv (fun ξ : Space =>
    (heatSecondSymbol s i j ξ : ℂ) * (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ)

private theorem heatSecondTest_eq_integral (s : ℝ) (i j : Fin 3)
    (ψ : ComplexTest) (x : Space) :
    heatSecondTest s i j ψ x =
      ∫ ξ : Space, heatSecondSymbol s i j ξ •
        (Real.fourierChar ⟪ξ, x⟫ • (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ) := by
  rw [heatSecondTest, Real.fourierInv_eq]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [Circle.smul_def, smul_eq_mul, Algebra.smul_def, realAlgebraMap_apply]
  ring

private theorem integrable_heatFourierProduct (i j : Fin 3) (ψ : ComplexTest)
    (x : Space) :
    Integrable (fun p : Space × ℝ => heatSecondSymbol p.2 i j p.1 •
      (Real.fourierChar ⟪p.1, x⟫ • (FourierTransform.fourierCLE ℂ ComplexTest ψ) p.1))
      ((volume : Measure Space).prod ((volume : Measure ℝ).restrict (Ioi 0))) := by
  let ψhat : ComplexTest := FourierTransform.fourierCLE ℂ ComplexTest ψ
  have hs : Continuous (fun p : Space × ℝ => heatSecondSymbol p.2 i j p.1) := by
    unfold heatSecondSymbol
    fun_prop
  have hc : Continuous (fun p : Space × ℝ => heatSecondSymbol p.2 i j p.1 •
      (Real.fourierChar ⟪p.1, x⟫ • ψhat p.1)) :=
    hs.smul ((Real.continuous_fourierChar.comp
      (continuous_fst.inner continuous_const)).smul (ψhat.continuous.comp continuous_fst))
  have hm : AEStronglyMeasurable (fun p : Space × ℝ =>
      heatSecondSymbol p.2 i j p.1 • (Real.fourierChar ⟪p.1, x⟫ • ψhat p.1))
      ((volume : Measure Space).prod ((volume : Measure ℝ).restrict (Ioi 0))) :=
    hc.aestronglyMeasurable
  refine (integrable_prod_iff hm).2 ⟨?_, ?_⟩
  · have hslice (ξ : Space) : Integrable
        (fun s : ℝ => heatSecondSymbol s i j ξ •
          (Real.fourierChar ⟪ξ, x⟫ • ψhat ξ))
        ((volume : Measure ℝ).restrict (Ioi 0)) :=
      (integrableOn_heatSecondSymbol i j ξ).smul_const
        (Real.fourierChar ⟪ξ, x⟫ • ψhat ξ)
    exact Filter.Eventually.of_forall hslice
  · refine ψhat.integrable.norm.mono' hm.norm.integral_prod_right' ?_
    filter_upwards [] with ξ
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp only [norm_smul, Circle.norm_smul, integral_mul_const,
      integral_norm_heatSecondSymbol]
    exact mul_le_of_le_one_left (norm_nonneg _) (RieszTestOperators.norm_rieszSymbol_le i j ξ)

/-- The positive-time representation converges absolutely at each spatial point. -/
theorem integrableOn_heatSecondTest (i j : Fin 3) (ψ : ComplexTest) (x : Space) :
    IntegrableOn (fun s => heatSecondTest s i j ψ x) (Ioi 0) := by
  apply (integrable_heatFourierProduct i j ψ x).integral_prod_right.congr
  exact Filter.Eventually.of_forall fun s => (heatSecondTest_eq_integral s i j ψ x).symm

/-- The actual double Riesz test operator is the positive-time heat integral. -/
theorem rieszTest_eq_integral_heatSecondTest (i j : Fin 3) (ψ : ComplexTest) (x : Space) :
    rieszTest i j ψ x = ∫ s : ℝ in Ioi 0, heatSecondTest s i j ψ x := by
  calc
    rieszTest i j ψ x = ∫ ξ : Space, ∫ s : ℝ in Ioi 0,
        heatSecondSymbol s i j ξ •
          (Real.fourierChar ⟪ξ, x⟫ • (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ) := by
      rw [rieszTest, Real.fourierInv_eq]
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [integral_smul_const, integral_heatSecondSymbol]
      simp only [Circle.smul_def, smul_eq_mul, Algebra.smul_def, realAlgebraMap_apply]
      ring
    _ = ∫ s : ℝ in Ioi 0, ∫ ξ : Space, heatSecondSymbol s i j ξ •
        (Real.fourierChar ⟪ξ, x⟫ • (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ) :=
      integral_integral_swap (integrable_heatFourierProduct i j ψ x)
    _ = ∫ s : ℝ in Ioi 0, heatSecondTest s i j ψ x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s => (heatSecondTest_eq_integral s i j ψ x).symm

end NavierStokesR3.Comparison
end


/-! Merged from `NavierStokes.R3.GaussianMoments`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# Gaussian moments for Fourier differentiation

The zeroth, first and second norm moments of a Gaussian are integrable.
The only polynomial estimate used here absorbs the square of the norm into
a Gaussian with half the decay rate.
-/


noncomputable section

open MeasureTheory

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- A real Gaussian, regarded as a complex-valued function, is integrable. -/
theorem integrable_complex_gaussian {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Space => (Real.exp (-a * ‖x‖ ^ 2) : ℂ)) := by
  simpa only [zero_mul, add_zero, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_pow] using
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (b := (a : ℂ)) (by simpa only [Complex.ofReal_re] using ha) 0 (0 : Space)

/-- The ordinary real Gaussian is integrable on three-dimensional space. -/
theorem integrable_gaussian {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Space => Real.exp (-a * ‖x‖ ^ 2)) := by
  refine (integrable_complex_gaussian ha).norm.congr ?_
  filter_upwards with x
  exact Complex.norm_of_nonneg (Real.exp_nonneg _)

private theorem sq_mul_gaussian_le (a r : ℝ) (ha : 0 < a) :
    r ^ 2 * Real.exp (-a * r ^ 2) ≤
      (2 / a) * Real.exp (-(a / 2) * r ^ 2) := by
  have hlinear : (a / 2) * r ^ 2 ≤ Real.exp ((a / 2) * r ^ 2) := by
    linarith [Real.add_one_le_exp ((a / 2) * r ^ 2)]
  have hmul := mul_le_mul_of_nonneg_right hlinear (Real.exp_nonneg (-a * r ^ 2))
  have he : Real.exp ((a / 2) * r ^ 2) * Real.exp (-a * r ^ 2) =
      Real.exp (-(a / 2) * r ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hmul
  calc
    r ^ 2 * Real.exp (-a * r ^ 2) =
        (2 / a) * (((a / 2) * r ^ 2) * Real.exp (-a * r ^ 2)) := by
      field_simp [ha.ne']

    _ ≤ (2 / a) * Real.exp (-(a / 2) * r ^ 2) :=
      mul_le_mul_of_nonneg_left hmul (by positivity)

/-- The second norm moment of a Gaussian is integrable. -/
theorem integrable_norm_sq_gaussian {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Space => ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2)) := by
  have hc : Continuous (fun x : Space => ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2)) := by
    fun_prop
  refine ((integrable_gaussian (a := a / 2) (by positivity)).const_mul (2 / a)).mono'
    hc.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact sq_mul_gaussian_le a ‖x‖ ha

/-- The first norm moment follows from the zeroth and second moments. -/
theorem integrable_norm_gaussian {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Space => ‖x‖ * Real.exp (-a * ‖x‖ ^ 2)) := by
  have hc : Continuous (fun x : Space => ‖x‖ * Real.exp (-a * ‖x‖ ^ 2)) := by
    fun_prop
  refine ((integrable_gaussian ha).add (integrable_norm_sq_gaussian ha)).mono'
    hc.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    ‖x‖ * Real.exp (-a * ‖x‖ ^ 2) ≤
        (1 + ‖x‖ ^ 2) * Real.exp (-a * ‖x‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      nlinarith [sq_nonneg (‖x‖ - 1 / 2)]
    _ = Real.exp (-a * ‖x‖ ^ 2) + ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2) := by ring

end NavierStokesR3.Comparison


end



noncomputable section

open MeasureTheory

namespace NavierStokesR3.Comparison

open ProblemStatement

theorem fourierIntegral_gaussian_real {a : ℝ} (ha : 0 < a) (z : Space) :
    FourierTransform.fourier (fun ξ : Space => (Real.exp (-a * ‖ξ‖ ^ 2) : ℂ)) z =
      (((Real.pi / a) ^ (3 / 2 : ℝ) *
        Real.exp (-Real.pi ^ 2 * ‖z‖ ^ 2 / a) : ℝ) : ℂ) := by
  have hdim : Module.finrank ℝ Space = 3 := by
    simp [Space, NavierStokes.ProblemStatement.Space]
  have hpow : ((Real.pi : ℂ) / (a : ℂ)) ^ ((3 : ℂ) / 2) =
      (((Real.pi / a) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_div, Complex.ofReal_cpow (by positivity)]
    simp
  have h := fourier_gaussian_innerProductSpace
    (V := Space) (b := (a : ℂ)) (by simpa using ha) z
  rw [hdim] at h
  norm_num only [Nat.cast_ofNat] at h
  rw [hpow] at h
  simpa only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_pow] using h

/-- Inverse Fourier transform of the heat semigroup's Gaussian multiplier. -/
theorem fourierIntegralInv_heatGaussian {s : ℝ} (hs : 0 < s) (z : Space) :
    FourierTransform.fourierInv
        (fun ξ : Space => (Real.exp (-(4 * Real.pi ^ 2 * s) * ‖ξ‖ ^ 2) : ℂ)) z =
      (heatKernel s z : ℂ) := by
  have ha : 0 < 4 * Real.pi ^ 2 * s := by positivity
  have hb : 0 < 4 * Real.pi * s := by positivity
  rw [Real.fourierInv_eq_fourier_neg, fourierIntegral_gaussian_real ha]
  simp only [norm_neg]
  have hratio : Real.pi / (4 * Real.pi ^ 2 * s) = (4 * Real.pi * s)⁻¹ := by
    field_simp [Real.pi_ne_zero, hs.ne']
  have hpower : (Real.pi / (4 * Real.pi ^ 2 * s)) ^ (3 / 2 : ℝ) =
      (4 * Real.pi * s) ^ (-(3 / 2 : ℝ)) := by
    rw [hratio, Real.rpow_def_of_pos (inv_pos.mpr hb), Real.rpow_def_of_pos hb,
      Real.log_inv]
    congr 1
    ring
  have hexponent : -Real.pi ^ 2 * ‖z‖ ^ 2 / (4 * Real.pi ^ 2 * s) =
      -(‖z‖ ^ 2) / (4 * s) := by
    field_simp [Real.pi_ne_zero, hs.ne']
  rw [hpower, hexponent]
  rfl

private theorem continuous_complex_coordinate (i : Fin 3) :
    Continuous (fun x : Space => (x i : ℂ)) := by
  exact Complex.continuous_ofReal.comp
    ((continuous_apply i).comp (EuclideanSpace.equiv (Fin 3) ℝ).continuous)

private theorem norm_coordinate_multiplier_le (c : ℂ) (i : Fin 3)
    (f : Space → ℂ) (ξ : Space) :
    ‖c * (ξ i : ℂ) * f ξ‖ ≤ ‖c‖ * (‖ξ‖ * ‖f ξ‖) := by
  have hcoord : ‖(ξ i : ℂ)‖ ≤ ‖ξ‖ := by
    simpa only [Complex.norm_real] using PiLp.norm_apply_le ξ i
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖c‖ * ‖ξ‖ * ‖f ξ‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoord (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

private theorem integrable_coordinate_multiplier {f : Space → ℂ}
    (c : ℂ) (i : Fin 3) (hf : AEStronglyMeasurable f)
    (h1 : Integrable (fun ξ : Space => ‖ξ‖ * ‖f ξ‖)) :
    Integrable (fun ξ : Space => c * (ξ i : ℂ) * f ξ) := by
  apply (h1.const_mul ‖c‖).mono'
  · exact (continuous_const.mul (continuous_complex_coordinate i)).aestronglyMeasurable.mul hf
  · filter_upwards with ξ
    exact norm_coordinate_multiplier_le c i f ξ

private theorem integrable_coordinate_multiplier_moment {f : Space → ℂ}
    (c : ℂ) (i : Fin 3) (hf : AEStronglyMeasurable f)
    (h2 : Integrable (fun ξ : Space => ‖ξ‖ ^ 2 * ‖f ξ‖)) :
    Integrable (fun ξ : Space => ‖ξ‖ * ‖c * (ξ i : ℂ) * f ξ‖) := by
  have hF : AEStronglyMeasurable (fun ξ : Space => c * (ξ i : ℂ) * f ξ) :=
    (continuous_const.mul (continuous_complex_coordinate i)).aestronglyMeasurable.mul hf
  apply (h2.const_mul ‖c‖).mono'
  · exact continuous_norm.aestronglyMeasurable.mul hF.norm
  · filter_upwards with ξ
    rw [norm_mul, norm_norm, norm_norm]
    calc
      _ ≤ ‖ξ‖ * (‖c‖ * (‖ξ‖ * ‖f ξ‖)) :=
        mul_le_mul_of_nonneg_left (norm_coordinate_multiplier_le c i f ξ) (norm_nonneg _)
      _ = _ := by ring

private theorem partialD_ofReal {f : Space → ℝ} (hf : Differentiable ℝ f)
    (i : Fin 3) (z : Space) :
    partialD i (fun x : Space => (f x : ℂ)) z = (partialD (E := ℝ) i f z : ℂ) := by
  unfold partialD NavierStokes.PeriodicIntegration.spatialPartial
  change fderiv ℝ (Complex.ofRealCLM ∘ f) z
    (NavierStokes.ProblemStatement.coordinateVector i) = _
  rw [((Complex.ofRealCLM.hasFDerivAt).comp z (hf z).hasFDerivAt).fderiv]
  rfl

private theorem differentiable_partial_heatKernel {s : ℝ} (hs : 0 < s) (j : Fin 3) :
    Differentiable ℝ (partialD j (heatKernel s)) := by
  have hc : Differentiable ℝ (fun x : Space => x j) := by
    convert! (innerSL ℝ (NavierStokes.ProblemStatement.coordinateVector j)).differentiable
      using 1
    ext x
    simp [NavierStokes.ProblemStatement.coordinateVector, EuclideanSpace.inner_single_left]
  rw [show partialD j (heatKernel s) =
    (fun x : Space => -(x j / (2 * s)) * heatKernel s x) from
    funext (partial_heatKernel hs j)]
  simpa only [div_eq_mul_inv] using!
    ((hc.mul_const ((2 * s)⁻¹)).neg.mul (differentiable_heatKernel hs))

private theorem secondPartial_ofReal_heatKernel {s : ℝ} (hs : 0 < s)
    (i j : Fin 3) (z : Space) :
    partialD i (partialD j (fun x : Space => (heatKernel s x : ℂ))) z =
      (heatKernelSecond s i j z : ℂ) := by
  have hfirst : partialD j (fun x : Space => (heatKernel s x : ℂ)) =
      (fun x : Space => (partialD (E := ℝ) j (heatKernel s) x : ℂ)) :=
    funext (partialD_ofReal (differentiable_heatKernel hs) j)
  rw [hfirst, partialD_ofReal (differentiable_partial_heatKernel hs j) i z,
    ← heatKernelSecond_eq_partial hs i j z]

private theorem heatKernelFourierData {s : ℝ} (hs : 0 < s) (i j : Fin 3) :
    Integrable (fun ξ : Space => (heatSecondSymbol s i j ξ : ℂ)) ∧
      ∀ z : Space, FourierTransform.fourierInv
        (fun ξ : Space => (heatSecondSymbol s i j ξ : ℂ)) z =
          (heatKernelSecond s i j z : ℂ) := by
  let a : ℝ := 4 * Real.pi ^ 2 * s
  let g : Space → ℂ := fun ξ => (Real.exp (-a * ‖ξ‖ ^ 2) : ℂ)
  let c : ℂ := 2 * Real.pi * Complex.I
  let f1 : Space → ℂ := fun ξ => c * (ξ j : ℂ) * g ξ
  let f2 : Space → ℂ := fun ξ => c * (ξ i : ℂ) * f1 ξ
  have ha : 0 < a := by dsimp [a]; positivity
  have hg : Integrable g := integrable_complex_gaussian ha
  have hg1 : Integrable (fun ξ : Space => ‖ξ‖ * ‖g ξ‖) := by
    simpa only [g, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      integrable_norm_gaussian ha
  have hg2 : Integrable (fun ξ : Space => ‖ξ‖ ^ 2 * ‖g ξ‖) := by
    simpa only [g, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      integrable_norm_sq_gaussian ha
  have hf1 : Integrable f1 :=
    integrable_coordinate_multiplier c j hg.aestronglyMeasurable hg1
  have hf1moment : Integrable (fun ξ : Space => ‖ξ‖ * ‖f1 ξ‖) :=
    integrable_coordinate_multiplier_moment c j hg.aestronglyMeasurable hg2
  have hf2 : Integrable f2 :=
    integrable_coordinate_multiplier c i hf1.aestronglyMeasurable hf1moment
  have hf2eq : f2 = (fun ξ : Space => (heatSecondSymbol s i j ξ : ℂ)) := by
    funext ξ
    dsimp [f2, f1, g, c, a]
    unfold heatSecondSymbol
    have he : -(4 * Real.pi ^ 2 * s) * ‖ξ‖ ^ 2 =
        -(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * s := by ring
    rw [he]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  have h0 : FourierTransform.fourierInv g = (fun x : Space => (heatKernel s x : ℂ)) := by
    funext x
    exact fourierIntegralInv_heatGaussian hs x
  have hd1 : partialD j (FourierTransform.fourierInv g) = FourierTransform.fourierInv f1 := by
    funext x
    unfold partialD NavierStokes.PeriodicIntegration.spatialPartial
    simpa [f1, c, NavierStokes.ProblemStatement.coordinateVector,
      EuclideanSpace.inner_single_right] using
      RieszTestOperators.fderiv_fourierInv_apply hg hg1 x
        (NavierStokes.ProblemStatement.coordinateVector j)
  have hd2 : partialD i (FourierTransform.fourierInv f1) = FourierTransform.fourierInv f2 := by
    funext x
    unfold partialD NavierStokes.PeriodicIntegration.spatialPartial
    simpa [f2, c, NavierStokes.ProblemStatement.coordinateVector,
      EuclideanSpace.inner_single_right] using
      RieszTestOperators.fderiv_fourierInv_apply hf1 hf1moment x
        (NavierStokes.ProblemStatement.coordinateVector i)
  constructor
  · rw [← hf2eq]
    exact hf2
  · intro z
    rw [← hf2eq, ← hd2, ← hd1, h0]
    exact secondPartial_ofReal_heatKernel hs i j z

/-- The positive-time heat Hessian multiplier is integrable in frequency. -/
theorem integrable_heatSecondSymbol_space {s : ℝ} (hs : 0 < s) (i j : Fin 3) :
    Integrable (fun ξ : Space => (heatSecondSymbol s i j ξ : ℂ)) :=
  (heatKernelFourierData hs i j).1

/-- The inverse Fourier transform of the heat Hessian multiplier is its actual kernel. -/
theorem fourierIntegralInv_heatSecondSymbol {s : ℝ} (hs : 0 < s)
    (i j : Fin 3) (z : Space) :
    FourierTransform.fourierInv (fun ξ : Space => (heatSecondSymbol s i j ξ : ℂ)) z =
      (heatKernelSecond s i j z : ℂ) :=
  (heatKernelFourierData hs i j).2 z

end NavierStokesR3.Comparison

/-! Merged from `NavierStokes.R3.RadialKernelBounds` (in a section, so its `open`s cannot leak). -/
section
/-!
# The radial majorant of the cutoff commutator

The cancellation factor `min (‖z‖ / R) 1` makes the singular kernel belong to
`L^(4/3)` in three dimensions. The proof uses the layer-cake formula and the
volume of balls, so no principal-value integral occurs in this module.
-/


noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- The positive radial majorant after inserting the cutoff difference. -/
def radialCommutatorKernel (R : ℝ) (z : Space) : ℝ :=
  ‖z‖ ^ (-3 : ℝ) * min (‖z‖ / R) 1

theorem radialCommutatorKernel_nonneg {R : ℝ} (hR : 0 < R) (z : Space) :
    0 ≤ radialCommutatorKernel R z := by
  unfold radialCommutatorKernel
  positivity

theorem radialCommutatorKernel_measurable (R : ℝ) :
    Measurable (radialCommutatorKernel R) := by
  unfold radialCommutatorKernel
  fun_prop

@[simp] theorem radialCommutatorKernel_zero (R : ℝ) :
    radialCommutatorKernel R 0 = 0 := by
  simp [radialCommutatorKernel]

private theorem kernel_one_le_cube (z : Space) :
    radialCommutatorKernel 1 z ≤ ‖z‖ ^ (-3 : ℝ) := by
  unfold radialCommutatorKernel
  exact mul_le_of_le_one_right (Real.rpow_nonneg (norm_nonneg _) _) (min_le_right _ _)

private theorem kernel_one_le_square (z : Space) :
    radialCommutatorKernel 1 z ≤ ‖z‖ ^ (-2 : ℝ) := by
  by_cases hz : z = 0
  · simp [hz]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  calc
    radialCommutatorKernel 1 z ≤ ‖z‖ ^ (-3 : ℝ) * ‖z‖ := by
      unfold radialCommutatorKernel
      gcongr
      simp
    _ = ‖z‖ ^ (-2 : ℝ) := by
      calc
        _ = ‖z‖ ^ (-3 : ℝ) * ‖z‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hn]; norm_num

private theorem kernel_one_power_le_four (z : Space) :
    radialCommutatorKernel 1 z ^ (4 / 3 : ℝ) ≤ ‖z‖ ^ (-4 : ℝ) := by
  calc
    _ ≤ (‖z‖ ^ (-3 : ℝ)) ^ (4 / 3 : ℝ) :=
      Real.rpow_le_rpow (radialCommutatorKernel_nonneg (by norm_num) z)
        (kernel_one_le_cube z) (by norm_num)
    _ = _ := by rw [← Real.rpow_mul (norm_nonneg _)]; norm_num

private theorem kernel_one_power_le_eight_thirds (z : Space) :
    radialCommutatorKernel 1 z ^ (4 / 3 : ℝ) ≤ ‖z‖ ^ (-(8 / 3) : ℝ) := by
  calc
    _ ≤ (‖z‖ ^ (-2 : ℝ)) ^ (4 / 3 : ℝ) :=
      Real.rpow_le_rpow (radialCommutatorKernel_nonneg (by norm_num) z)
        (kernel_one_le_square z) (by norm_num)
    _ = _ := by rw [← Real.rpow_mul (norm_nonneg _)]; norm_num

private theorem levelset_measure_le_ball {f : Space → ℝ} {q t : ℝ}
    (hq : q < 0) (ht : 0 < t) (hf : ∀ z, f z ≤ ‖z‖ ^ q) :
    volume {z | t ≤ f z} ≤ volume (Metric.closedBall (0 : Space) (t ^ q⁻¹)) := by
  apply measure_mono
  intro z hz
  have hn : 0 < ‖z‖ := by
    by_contra hn
    have hnz : ‖z‖ = 0 := le_antisymm (not_lt.mp hn) (norm_nonneg _)
    have := hz.trans (hf z)
    rw [hnz, Real.zero_rpow hq.ne] at this
    exact (not_le_of_gt ht) this
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (Real.le_rpow_inv_iff_of_neg hn ht hq).mpr (hz.trans (hf z))

private theorem ball_measure_power (t q : ℝ) (ht : 0 < t) :
    volume (Metric.closedBall (0 : Space) (t ^ q)) =
      ENNReal.ofReal (t ^ (q * 3)) * volume (Metric.ball (0 : Space) 1) := by
  rw [Measure.addHaar_closedBall volume (0 : Space) (Real.rpow_nonneg ht.le _)]
  congr 2
  simp only [Space, NavierStokes.ProblemStatement.Space, finrank_euclideanSpace,
    Fintype.card_fin]
  rw [Real.rpow_mul ht.le]
  exact (Real.rpow_natCast (t ^ q) 3).symm

private theorem kernel_one_power_integrable :
    Integrable (fun z : Space => radialCommutatorKernel 1 z ^ (4 / 3 : ℝ)) := by
  let f : Space → ℝ := fun z => radialCommutatorKernel 1 z ^ (4 / 3 : ℝ)
  have hm : Measurable f := (radialCommutatorKernel_measurable 1).pow_const _
  have hn : ∀ z, 0 ≤ f z := fun z =>
    Real.rpow_nonneg (radialCommutatorKernel_nonneg (by norm_num) z) _
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  change HasFiniteIntegral f volume
  rw [hasFiniteIntegral_iff_enorm, lintegral_enorm_of_nonneg hn,
    lintegral_eq_lintegral_meas_le volume (Filter.Eventually.of_forall hn) hm.aemeasurable]
  calc
    (∫⁻ t in Ioi (0 : ℝ), volume {z | t ≤ f z}) ≤
        ∫⁻ t in Ioc (0 : ℝ) 1 ∪ Ioi 1, volume {z | t ≤ f z} :=
      lintegral_mono_set Ioi_subset_Ioc_union_Ioi
    _ ≤ (∫⁻ t in Ioc (0 : ℝ) 1, volume {z | t ≤ f z}) +
        ∫⁻ t in Ioi (1 : ℝ), volume {z | t ≤ f z} := lintegral_union_le _ _ _
    _ < ∞ := by
      apply ENNReal.add_lt_top.mpr
      constructor
      · calc
          (∫⁻ t in Ioc (0 : ℝ) 1, volume {z | t ≤ f z}) ≤
              ∫⁻ t in Ioc (0 : ℝ) 1,
                ENNReal.ofReal (t ^ (-(3 / 4) : ℝ)) *
                  volume (Metric.ball (0 : Space) 1) := by
            apply setLIntegral_mono' measurableSet_Ioc
            intro t ht
            calc
              volume {z | t ≤ f z} ≤
                  volume (Metric.closedBall (0 : Space) (t ^ ((-4 : ℝ)⁻¹))) :=
                levelset_measure_le_ball (by norm_num) ht.1 kernel_one_power_le_four
              _ = _ := by
                rw [ball_measure_power t _ ht.1]
                norm_num
          _ < ∞ := by
            rw [lintegral_mul_const' _ _ measure_ball_lt_top.ne]
            apply ENNReal.mul_lt_top _ measure_ball_lt_top
            apply IntegrableOn.setLIntegral_lt_top
            rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
            exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
      · calc
          (∫⁻ t in Ioi (1 : ℝ), volume {z | t ≤ f z}) ≤
              ∫⁻ t in Ioi (1 : ℝ),
                ENNReal.ofReal (t ^ (-(9 / 8) : ℝ)) *
                  volume (Metric.ball (0 : Space) 1) := by
            apply setLIntegral_mono' measurableSet_Ioi
            intro t ht
            have ht0 : 0 < t := zero_lt_one.trans ht
            calc
              volume {z | t ≤ f z} ≤
                  volume (Metric.closedBall (0 : Space) (t ^ ((-(8 / 3) : ℝ)⁻¹))) :=
                levelset_measure_le_ball (by norm_num) ht0 kernel_one_power_le_eight_thirds
              _ = _ := by
                rw [ball_measure_power t _ ht0]
                norm_num
          _ < ∞ := by
            rw [lintegral_mul_const' _ _ measure_ball_lt_top.ne]
            exact ENNReal.mul_lt_top
              (IntegrableOn.setLIntegral_lt_top
                (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one))
              measure_ball_lt_top

/-- Dilation of the cutoff kernel. -/
theorem radialCommutatorKernel_scale {R : ℝ} (hR : 0 < R) (z : Space) :
    radialCommutatorKernel R z =
      R ^ (-3 : ℝ) * radialCommutatorKernel 1 (R⁻¹ • z) := by
  simp only [radialCommutatorKernel, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR), div_one]
  rw [Real.mul_rpow (inv_nonneg.mpr hR.le) (norm_nonneg z), Real.inv_rpow hR.le]
  have hpow : R ^ (-3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hR _).ne'
  simp only [div_eq_mul_inv, mul_comm R⁻¹ ‖z‖]
  field_simp

private theorem kernel_power_scale {R : ℝ} (hR : 0 < R) (z : Space) :
    radialCommutatorKernel R z ^ (4 / 3 : ℝ) =
      R ^ (-4 : ℝ) * radialCommutatorKernel 1 (R⁻¹ • z) ^ (4 / 3 : ℝ) := by
  rw [radialCommutatorKernel_scale hR, Real.mul_rpow (Real.rpow_nonneg hR.le _)
    (radialCommutatorKernel_nonneg (by norm_num) _), ← Real.rpow_mul hR.le]
  norm_num

/-- The `4/3` power of the radial kernel is integrable. -/
theorem radialCommutatorKernel_power_integrable {R : ℝ} (hR : 0 < R) :
    Integrable (fun z : Space => radialCommutatorKernel R z ^ (4 / 3 : ℝ)) := by
  have h := (kernel_one_power_integrable.comp_smul (inv_ne_zero hR.ne')).const_mul
    (R ^ (-4 : ℝ))
  simpa only [kernel_power_scale hR] using h

/-- The actual cancellation kernel belongs to `L^(4/3)`. -/
theorem radialCommutatorKernel_memLp {R : ℝ} (hR : 0 < R) :
    MemLp (radialCommutatorKernel R) (4 / 3 : ℝ≥0∞) volume := by
  apply (integrable_norm_rpow_iff
    (radialCommutatorKernel_measurable R).aestronglyMeasurable
    (by norm_num : (4 / 3 : ℝ≥0∞) ≠ 0)
    (ENNReal.div_lt_top (by norm_num) (by norm_num)).ne).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat, Real.norm_eq_abs,
    abs_of_nonneg (radialCommutatorKernel_nonneg hR _)] using
    radialCommutatorKernel_power_integrable hR

private theorem kernel_power_integral_scale {R : ℝ} (hR : 0 < R) :
    (∫ z : Space, radialCommutatorKernel R z ^ (4 / 3 : ℝ)) =
      R ^ (-1 : ℝ) * ∫ z : Space, radialCommutatorKernel 1 z ^ (4 / 3 : ℝ) := by
  have hpow : R ^ (-4 : ℝ) * R ^ (3 : ℕ) = R ^ (-1 : ℝ) := by
    calc
      _ = R ^ (-4 : ℝ) * R ^ (3 : ℝ) := by
        exact congrArg (fun a => R ^ (-4 : ℝ) * a) (Real.rpow_natCast R 3).symm
      _ = R ^ ((-4 : ℝ) + 3) := (Real.rpow_add hR _ _).symm
      _ = _ := by norm_num
  simp_rw [kernel_power_scale hR]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume
    (fun z : Space => radialCommutatorKernel 1 z ^ (4 / 3 : ℝ)) hR.le]
  simp only [Space, NavierStokes.ProblemStatement.Space, finrank_euclideanSpace,
    Fintype.card_fin, smul_eq_mul, ← mul_assoc, hpow]

private theorem kernel_lpNorm_formula {R : ℝ} (hR : 0 < R) :
    comparisonLpNorm (4 / 3) (radialCommutatorKernel R) =
      (∫ z : Space, radialCommutatorKernel R z ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
  unfold comparisonLpNorm
  rw [(radialCommutatorKernel_memLp hR).eLpNorm_eq_integral_rpow_norm
    (by norm_num) (ENNReal.div_lt_top (by norm_num) (by norm_num)).ne]
  have hp : (4 / 3 : ℝ≥0∞).toReal = (4 / 3 : ℝ) := by norm_num
  rw [hp]
  have hinv : (4 / 3 : ℝ)⁻¹ = (3 / 4 : ℝ) := by norm_num
  rw [hinv]
  have hnorm : (fun z : Space => ‖radialCommutatorKernel R z‖ ^ (4 / 3 : ℝ)) =
      (fun z : Space => radialCommutatorKernel R z ^ (4 / 3 : ℝ)) := by
    funext z
    rw [Real.norm_eq_abs, abs_of_nonneg (radialCommutatorKernel_nonneg hR z)]
  have hi : 0 ≤ ∫ z : Space, radialCommutatorKernel R z ^ (4 / 3 : ℝ) :=
    integral_nonneg fun z => Real.rpow_nonneg (radialCommutatorKernel_nonneg hR z) _
  rw [hnorm, ENNReal.toReal_ofReal (Real.rpow_nonneg hi _)]

/-- The norm has exactly the scale required by the cutoff commutator. -/
theorem radialCommutatorKernel_lpNorm_scale {R : ℝ} (hR : 0 < R) :
    comparisonLpNorm (4 / 3) (radialCommutatorKernel R) =
      comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) * R ^ (-(3 / 4) : ℝ) := by
  have hi : 0 ≤ ∫ z : Space, radialCommutatorKernel 1 z ^ (4 / 3 : ℝ) :=
    integral_nonneg fun z =>
      Real.rpow_nonneg (radialCommutatorKernel_nonneg zero_lt_one z) _
  rw [kernel_lpNorm_formula hR, kernel_lpNorm_formula zero_lt_one,
    kernel_power_integral_scale hR,
    Real.mul_rpow (Real.rpow_nonneg hR.le _) hi, ← Real.rpow_mul hR.le]
  norm_num ; ring


end NavierStokesR3.Comparison
end

/-! Merged from `NavierStokes.R3.HeatKernelTimeBound`. -/
/-!
# Integration in time for the heat-kernel Hessian

The reciprocal substitution reduces the inverse-time Gaussian integrals to
the ordinary Gamma integral. These estimates are uniform in the spatial
indices and give the inverse-cube kernel bound in three dimensions.
-/


noncomputable section

open Set MeasureTheory

namespace NavierStokesR3.Comparison

open ProblemStatement

private theorem inverseTimeGamma_transform (a p s : ℝ) (hs : 0 < s) :
    (|(-1 : ℝ)| * s ^ ((-1 : ℝ) - 1)) •
        ((s ^ (-1 : ℝ)) ^ (p - 1) * Real.exp (-(a * s ^ (-1 : ℝ)))) =
      s ^ (-(p + 1)) * Real.exp (-a / s) := by
  norm_num only [abs_neg, abs_one, one_mul, smul_eq_mul]
  rw [← Real.rpow_mul hs.le, ← mul_assoc, ← Real.rpow_add hs]
  congr 1
  · congr 1
    ring
  · rw [Real.rpow_neg_one]
    simp only [div_eq_mul_inv, neg_mul]

/-- The inverse-time Gaussian power is integrable for every positive shape
parameter and positive spatial scale. -/
theorem integrableOn_inverseTimeGamma {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    IntegrableOn (fun s : ℝ => s ^ (-(p + 1)) * Real.exp (-a / s)) (Ioi 0) := by
  have hg : IntegrableOn (fun t : ℝ => t ^ (p - 1) * Real.exp (-(a * t)))
      (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := p - 1) (b := a) (by linarith) (by norm_num) ha)
  have h := (integrableOn_Ioi_comp_rpow_iff
    (fun t : ℝ => t ^ (p - 1) * Real.exp (-(a * t)))
    (p := (-1 : ℝ)) (by norm_num)).mpr hg
  exact h.congr_fun (fun s hs => inverseTimeGamma_transform a p s hs) measurableSet_Ioi

/-- Reciprocal substitution evaluates the inverse-time Gamma integral. -/
theorem integral_inverseTimeGamma {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    (∫ s : ℝ in Ioi 0, s ^ (-(p + 1)) * Real.exp (-a / s)) =
      a ^ (-p) * Real.Gamma p := by
  calc
    (∫ s : ℝ in Ioi 0, s ^ (-(p + 1)) * Real.exp (-a / s)) =
        ∫ s : ℝ in Ioi 0, (|(-1 : ℝ)| * s ^ ((-1 : ℝ) - 1)) •
          ((s ^ (-1 : ℝ)) ^ (p - 1) * Real.exp (-(a * s ^ (-1 : ℝ)))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      exact (inverseTimeGamma_transform a p s hs).symm
    _ = ∫ t : ℝ in Ioi 0, t ^ (p - 1) * Real.exp (-(a * t)) :=
      integral_comp_rpow_Ioi (fun t : ℝ => t ^ (p - 1) * Real.exp (-(a * t)))
        (by norm_num : (-1 : ℝ) ≠ 0)
    _ = (1 / a) ^ p * Real.Gamma p :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi hp ha
    _ = a ^ (-p) * Real.Gamma p := by
      rw [one_div, Real.inv_rpow ha.le, Real.rpow_neg ha.le]

private theorem square_quarter_rpow (r p : ℝ) (hr : 0 < r) :
    (r ^ 2 / 4) ^ (-p) = 4 ^ p * r ^ (-2 * p) := by
  rw [Real.div_rpow (sq_nonneg r) (by norm_num : (0 : ℝ) ≤ 4),
    ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), div_inv_eq_mul]
  convert! mul_comm (r ^ ((2 : ℝ) * -p)) (4 ^ p) using 1
  congr 1
  ring_nf

/-- The scale occurring in the heat kernel gives the expected homogeneous
power after integration in time. -/
theorem integral_inverseTimeGamma_square_scale {r p : ℝ} (hr : 0 < r) (hp : 0 < p) :
    (∫ s : ℝ in Ioi 0, s ^ (-(p + 1)) * Real.exp (-(r ^ 2 / 4) / s)) =
      4 ^ p * r ^ (-2 * p) * Real.Gamma p := by
  rw [integral_inverseTimeGamma (by positivity) hp, square_quarter_rpow r p hr]

/-- A common, nonnegative majorant of the nine coordinate Hessians. -/
def heatKernelSecondTimeEnvelope (r s : ℝ) : ℝ :=
  (4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
    (r ^ 2 / 4 * (s ^ (-((5 / 2 : ℝ) + 1)) * Real.exp (-(r ^ 2 / 4) / s)) +
      1 / 2 * (s ^ (-((3 / 2 : ℝ) + 1)) * Real.exp (-(r ^ 2 / 4) / s)))

/-- One universal constant for the time-integrated three dimensional heat
kernel Hessian. Its exact value is immaterial to the commutator estimate. -/
def heatKernelTimeConstant : ℝ :=
  (4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
    (4 ^ (5 / 2 : ℝ) / 4 * Real.Gamma (5 / 2) +
      4 ^ (3 / 2 : ℝ) / 2 * Real.Gamma (3 / 2))

theorem heatKernelTimeConstant_pos : 0 < heatKernelTimeConstant := by
  unfold heatKernelTimeConstant
  positivity


theorem heatKernelSecondTimeEnvelope_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (heatKernelSecondTimeEnvelope r) (Ioi 0) := by
  have ha : 0 < r ^ 2 / 4 := by positivity
  exact (((integrableOn_inverseTimeGamma ha (by norm_num : (0 : ℝ) < 5 / 2)).const_mul
    (r ^ 2 / 4)).add
      ((integrableOn_inverseTimeGamma ha (by norm_num : (0 : ℝ) < 3 / 2)).const_mul
        (1 / 2))).const_mul _

theorem integral_heatKernelSecondTimeEnvelope {r : ℝ} (hr : 0 < r) :
    (∫ s : ℝ in Ioi 0, heatKernelSecondTimeEnvelope r s) =
      heatKernelTimeConstant * r ^ (-3 : ℝ) := by
  have ha : 0 < r ^ 2 / 4 := by positivity
  have hfive := integrableOn_inverseTimeGamma ha (by norm_num : (0 : ℝ) < 5 / 2)
  have hthree := integrableOn_inverseTimeGamma ha (by norm_num : (0 : ℝ) < 3 / 2)
  have hpow : r ^ 2 * r ^ (-5 : ℝ) = r ^ (-3 : ℝ) := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr]
    norm_num
  simp only [heatKernelSecondTimeEnvelope, integral_const_mul,
    integral_add (hfive.const_mul (r ^ 2 / 4)) (hthree.const_mul (1 / 2))]
  rw [integral_inverseTimeGamma_square_scale hr (by norm_num : (0 : ℝ) < 5 / 2),
    integral_inverseTimeGamma_square_scale hr (by norm_num : (0 : ℝ) < 3 / 2)]
  norm_num only [show (-2 : ℝ) * (5 / 2) = -5 by norm_num,
    show (-2 : ℝ) * (3 / 2) = -3 by norm_num]
  unfold heatKernelTimeConstant
  calc
    _ = (4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
        (4 ^ (5 / 2 : ℝ) / 4 * Real.Gamma (5 / 2) * (r ^ 2 * r ^ (-5 : ℝ)) +
          4 ^ (3 / 2 : ℝ) / 2 * Real.Gamma (3 / 2) * r ^ (-3 : ℝ)) := by ring
    _ = _ := by rw [hpow]; ring

private theorem heatKernel_invTime_decomposition {s : ℝ} (hs : 0 < s)
    (z : Space) (a b : ℝ) :
    (a / (4 * s ^ 2) + b / (2 * s)) * heatKernel s z =
      (4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
        (a / 4 * (s ^ (-((5 / 2 : ℝ) + 1)) *
          Real.exp (-(‖z‖ ^ 2 / 4) / s)) +
        b / 2 * (s ^ (-((3 / 2 : ℝ) + 1)) *
          Real.exp (-(‖z‖ ^ 2 / 4) / s))) := by
  have hfive : s ^ (-((5 / 2 : ℝ) + 1)) = s ^ (-(3 / 2 : ℝ)) / s ^ 2 := by
    rw [show -((5 / 2 : ℝ) + 1) = -(3 / 2 : ℝ) - (2 : ℕ) by norm_num]
    exact Real.rpow_sub_natCast hs.ne' _ _
  have hthree : s ^ (-((3 / 2 : ℝ) + 1)) = s ^ (-(3 / 2 : ℝ)) / s := by
    rw [show -((3 / 2 : ℝ) + 1) = -(3 / 2 : ℝ) - 1 by norm_num]
    exact Real.rpow_sub_one hs.ne' _
  have he : Real.exp (-(‖z‖ ^ 2) / (4 * s)) =
      Real.exp (-(‖z‖ ^ 2 / 4) / s) := by
    congr 1
    simp only [neg_div, div_div]
  unfold heatKernel
  rw [hfive, hthree, Real.mul_rpow (show 0 ≤ (4 : ℝ) * Real.pi by positivity) hs.le, he]
  field_simp [hs.ne']


/-- The Gaussian coordinate Hessian is the difference of two integrable
inverse-time Gamma terms. -/
theorem heatKernelSecond_inverseTime_decomposition {s : ℝ} (hs : 0 < s)
    (i j : Fin 3) (z : Space) :
    heatKernelSecond s i j z =
      (4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
        (z i * z j / 4 * (s ^ (-((5 / 2 : ℝ) + 1)) *
          Real.exp (-(‖z‖ ^ 2 / 4) / s)) -
        (if i = j then 1 else 0) / 2 * (s ^ (-((3 / 2 : ℝ) + 1)) *
          Real.exp (-(‖z‖ ^ 2 / 4) / s))) := by
  simpa only [heatKernelSecond, neg_div, neg_mul, sub_eq_add_neg] using
    heatKernel_invTime_decomposition hs z (z i * z j) (-(if i = j then 1 else 0))

theorem heatKernelSecondTimeEnvelope_eq {s : ℝ} (hs : 0 < s) (z : Space) :
    heatKernelSecondTimeEnvelope ‖z‖ s =
      (‖z‖ ^ 2 / (4 * s ^ 2) + 1 / (2 * s)) * heatKernel s z :=
  (heatKernel_invTime_decomposition hs z (‖z‖ ^ 2) 1).symm

theorem norm_heatKernelSecond_le_timeEnvelope {s : ℝ} (hs : 0 < s)
    (i j : Fin 3) (z : Space) :
    ‖heatKernelSecond s i j z‖ ≤ heatKernelSecondTimeEnvelope ‖z‖ s := by
  rw [heatKernelSecondTimeEnvelope_eq hs z]
  exact norm_heatKernelSecond_le hs i j z

/-- Away from the spatial origin, every Hessian component is integrable in
positive time. -/
theorem heatKernelSecond_integrable_time (i j : Fin 3) {z : Space} (hz : z ≠ 0) :
    IntegrableOn (fun s : ℝ => heatKernelSecond s i j z) (Ioi 0) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have ha : 0 < ‖z‖ ^ 2 / 4 := by positivity
  have hfive := integrableOn_inverseTimeGamma ha (by norm_num : (0 : ℝ) < 5 / 2)
  have hthree := integrableOn_inverseTimeGamma ha (by norm_num : (0 : ℝ) < 3 / 2)
  have h := ((hfive.const_mul (z i * z j / 4)).sub
    (hthree.const_mul ((if i = j then (1 : ℝ) else 0) / 2))).const_mul
      ((4 * Real.pi) ^ (-(3 / 2 : ℝ)))
  refine h.congr ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  exact (heatKernelSecond_inverseTime_decomposition hs i j z).symm

/-- The positive-time integral of the absolute Hessian kernel has the
inverse-cube decay needed for the pressure commutator. -/
theorem heatKernelSecond_integral_norm_le (i j : Fin 3) {z : Space} (hz : z ≠ 0) :
    (∫ s : ℝ in Ioi 0, ‖heatKernelSecond s i j z‖) ≤
      heatKernelTimeConstant * ‖z‖ ^ (-3 : ℝ) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  calc
    (∫ s : ℝ in Ioi 0, ‖heatKernelSecond s i j z‖) ≤
        ∫ s : ℝ in Ioi 0, heatKernelSecondTimeEnvelope ‖z‖ s := by
      refine integral_mono_ae (heatKernelSecond_integrable_time i j hz).norm
        (heatKernelSecondTimeEnvelope_integrable hr) ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      exact norm_heatKernelSecond_le_timeEnvelope hs i j z
    _ = _ := integral_heatKernelSecondTimeEnvelope hr

theorem heatKernelSecond_integral_abs_le (i j : Fin 3) {z : Space} (hz : z ≠ 0) :
    (∫ s : ℝ in Ioi 0, |heatKernelSecond s i j z|) ≤
      heatKernelTimeConstant * ‖z‖ ^ (-3 : ℝ) := by
  simpa only [Real.norm_eq_abs] using heatKernelSecond_integral_norm_le i j hz

end NavierStokesR3.Comparison

/-! Merged from `NavierStokes.R3.HeatKernelCancellation` (in a section, so its `open`s cannot leak). -/
section
/-!
# Cancellation in the heat-kernel commutator

The multiplier is the square of a cutoff valued in `[0, 1]`.  Its difference
is bounded by its Lipschitz variation near the diagonal and by `1` everywhere.
The resulting minimum is the cancellation factor used before interchanging
the heat-time and spatial integrals.
-/


noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- The cancellation factor for the multiplier `φ²`. -/
def cutoffSquareDifference (φ : Space → ℝ) (x y : Space) : ℝ :=
  φ y ^ 2 - φ x ^ 2

theorem abs_sq_sub_sq_le_two_mul_abs_sub {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    |a ^ 2 - b ^ 2| ≤ 2 * |a - b| := by
  have hab : |a + b| ≤ 2 := by
    rw [abs_of_nonneg (add_nonneg ha.1 hb.1)]
    linarith [ha.2, hb.2]
  calc
    |a ^ 2 - b ^ 2| = |a - b| * |a + b| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ |a - b| * 2 := mul_le_mul_of_nonneg_left hab (abs_nonneg _)
    _ = 2 * |a - b| := mul_comm _ _

theorem abs_sq_sub_sq_le_one {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    |a ^ 2 - b ^ 2| ≤ 1 := by
  rw [abs_le]
  have ha2 : a * a ≤ 1 * 1 := mul_le_mul ha.2 ha.2 ha.1 (by norm_num)
  have hb2 : b * b ≤ 1 * 1 := mul_le_mul hb.2 hb.2 hb.1 (by norm_num)
  constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]

theorem cutoffSquareDifference_abs_le_one {φ : Space → ℝ}
    (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1) (x y : Space) :
    |cutoffSquareDifference φ x y| ≤ 1 :=
  abs_sq_sub_sq_le_one (hφ y) (hφ x)



/-- A form with a real scale parameter, convenient for scaled bump functions. -/
theorem cutoffSquareDifference_abs_le_scaled_min {φ : Space → ℝ}
    {L R : ℝ} (hR : 0 < R)
    (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (x y : Space) :
    |cutoffSquareDifference φ x y| ≤
      max (2 * L) 1 * min (‖x - y‖ / R) 1 := by
  have hsmall : |cutoffSquareDifference φ x y| ≤ 2 * L * (‖x - y‖ / R) := by
    have hxy := hLip y x
    rw [norm_sub_rev] at hxy
    calc
      |cutoffSquareDifference φ x y| ≤ 2 * |φ y - φ x| :=
        abs_sq_sub_sq_le_two_mul_abs_sub (hφ y) (hφ x)
      _ ≤ 2 * ((L / R) * ‖x - y‖) := mul_le_mul_of_nonneg_left hxy (by norm_num)
      _ = 2 * L * (‖x - y‖ / R) := by ring
  have hlarge := cutoffSquareDifference_abs_le_one hφ x y
  have hnonneg : 0 ≤ ‖x - y‖ / R := div_nonneg (norm_nonneg _) hR.le
  by_cases hx : ‖x - y‖ / R ≤ 1
  · rw [min_eq_left hx]
    exact hsmall.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hnonneg)
  · rw [min_eq_right (le_of_lt (lt_of_not_ge hx)), mul_one]
    exact hlarge.trans (le_max_right _ _)

@[simp] theorem cutoffSquareDifference_self (φ : Space → ℝ) (x : Space) :
    cutoffSquareDifference φ x x = 0 := sub_self _


/-- The time-integrated kernel with cancellation already inserted. -/
def cancelledTimeKernel (K : ℝ → Space → ℝ) (φ : Space → ℝ)
    (x y : Space) : ℝ :=
  ∫ s in Ioi (0 : ℝ), K s (x - y) * cutoffSquareDifference φ x y

/-- The absolute time integral is used to justify the subsequent Fubini step. -/
def absoluteCancelledTimeKernel (K : ℝ → Space → ℝ) (φ : Space → ℝ)
    (x y : Space) : ℝ :=
  ∫ s in Ioi (0 : ℝ), |K s (x - y) * cutoffSquareDifference φ x y|

theorem cancelledTimeKernel_abs_le (K : ℝ → Space → ℝ) (φ : Space → ℝ)
    (x y : Space) :
    |cancelledTimeKernel K φ x y| ≤ absoluteCancelledTimeKernel K φ x y :=
  abs_integral_le_integral_abs

theorem absoluteCancelledTimeKernel_nonneg (K : ℝ → Space → ℝ) (φ : Space → ℝ)
    (x y : Space) : 0 ≤ absoluteCancelledTimeKernel K φ x y :=
  integral_nonneg fun _ => abs_nonneg _

theorem cancelledTimeKernel_integrable_time {K : ℝ → Space → ℝ}
    (hK : ∀ z ≠ 0, IntegrableOn (fun s => K s z) (Ioi (0 : ℝ)) volume)
    (φ : Space → ℝ) (x y : Space) :
    IntegrableOn (fun s => K s (x - y) * cutoffSquareDifference φ x y)
      (Ioi (0 : ℝ)) volume := by
  by_cases hxy : x = y
  · simp only [hxy, cutoffSquareDifference_self, mul_zero]
    exact integrable_zero _ _ _
  · exact (hK (x - y) (sub_ne_zero.mpr hxy)).mul_const _

theorem absoluteCancelledTimeKernel_le {K : ℝ → Space → ℝ}
    {φ : Space → ℝ} {C L R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hK : ∀ z ≠ 0, (∫ s in Ioi (0 : ℝ), |K s z|) ≤ C * ‖z‖ ^ (-3 : ℝ))
    (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (x y : Space) :
    absoluteCancelledTimeKernel K φ x y ≤
      (C * max (2 * L) 1) * (‖x - y‖ ^ (-3 : ℝ) * min (‖x - y‖ / R) 1) := by
  by_cases hxy : x = y
  · simp [absoluteCancelledTimeKernel, hxy, cutoffSquareDifference_self]
  have hc : 0 ≤ C * ‖x - y‖ ^ (-3 : ℝ) := by positivity
  calc
    absoluteCancelledTimeKernel K φ x y =
        (∫ s in Ioi (0 : ℝ), |K s (x - y)|) * |cutoffSquareDifference φ x y| := by
      simp only [absoluteCancelledTimeKernel, abs_mul, integral_mul_const]
    _ ≤ (C * ‖x - y‖ ^ (-3 : ℝ)) * |cutoffSquareDifference φ x y| :=
      mul_le_mul_of_nonneg_right (hK _ (sub_ne_zero.mpr hxy)) (abs_nonneg _)
    _ ≤ (C * ‖x - y‖ ^ (-3 : ℝ)) *
        (max (2 * L) 1 * min (‖x - y‖ / R) 1) :=
      mul_le_mul_of_nonneg_left
        (cutoffSquareDifference_abs_le_scaled_min hR hφ hLip x y) hc
    _ = _ := by ring

theorem cancelledTimeKernel_le {K : ℝ → Space → ℝ}
    {φ : Space → ℝ} {C L R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hK : ∀ z ≠ 0, (∫ s in Ioi (0 : ℝ), |K s z|) ≤ C * ‖z‖ ^ (-3 : ℝ))
    (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (x y : Space) :
    |cancelledTimeKernel K φ x y| ≤
      (C * max (2 * L) 1) * (‖x - y‖ ^ (-3 : ℝ) * min (‖x - y‖ / R) 1) :=
  (cancelledTimeKernel_abs_le K φ x y).trans
    (absoluteCancelledTimeKernel_le hC hR hK hφ hLip x y)

theorem cancelledTimeIntegrand_measurable {K : ℝ → Space → ℝ}
    {φ : Space → ℝ} (hK : Measurable (Function.uncurry K))
    (hφ : Measurable φ) :
    Measurable (fun p : (Space × Space) × ℝ =>
      K p.2 (p.1.1 - p.1.2) * cutoffSquareDifference φ p.1.1 p.1.2) := by
  have hmap : Measurable (fun p : (Space × Space) × ℝ =>
      (p.2, p.1.1 - p.1.2)) := by fun_prop
  have hdiff : Measurable (fun p : (Space × Space) × ℝ =>
      cutoffSquareDifference φ p.1.1 p.1.2) := by
    unfold cutoffSquareDifference
    fun_prop
  exact (hK.comp hmap).mul hdiff

theorem cancelledTimeKernel_measurable {K : ℝ → Space → ℝ}
    {φ : Space → ℝ} (hK : Measurable (Function.uncurry K))
    (hφ : Measurable φ) :
    Measurable (Function.uncurry (cancelledTimeKernel K φ)) := by
  exact (cancelledTimeIntegrand_measurable hK hφ).stronglyMeasurable.integral_prod_right'.measurable

theorem absoluteCancelledTimeKernel_measurable {K : ℝ → Space → ℝ}
    {φ : Space → ℝ} (hK : Measurable (Function.uncurry K))
    (hφ : Measurable φ) :
    Measurable (Function.uncurry (absoluteCancelledTimeKernel K φ)) := by
  change Measurable (fun z : Space × Space => ∫ s in Ioi (0 : ℝ), |K s (z.1 - z.2) * cutoffSquareDifference φ z.1 z.2|)
  simpa only [Real.norm_eq_abs] using
    ((cancelledTimeIntegrand_measurable hK hφ).norm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioi (0 : ℝ)))).measurable

/-- The algebraic cancellation is inserted before either variable is integrated. -/
theorem cutoffSquareDifference_smul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (k : ℝ) (φ : Space → ℝ) (r : E) (x y : Space) :
    k • (φ y ^ 2 • r) - φ x ^ 2 • (k • r) =
      (k * cutoffSquareDifference φ x y) • r := by
  simp only [cutoffSquareDifference, mul_sub, sub_smul, smul_smul]
  rw [mul_comm (φ x ^ 2) k]

end NavierStokesR3.Comparison
end

/-! Merged from `NavierStokes.R3.HeatKernelPairedBound` (in a section, so its `open`s cannot leak). -/
section
/-!
# The paired estimate for the heat commutator kernel

The time-integrated heat Hessian, after cutoff cancellation, is dominated by
the radial `L^(4/3)` kernel. Its exact scaling and the sectionwise Hölder bound
give the factor `R^(-3/4)` in the paired commutator estimate.
-/


noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- The actual time-integrated heat Hessian with cutoff cancellation already
inserted into the time integrand. -/
def heatCommutatorKernel (i j : Fin 3) (φ : Space → ℝ) (x y : Space) : ℝ :=
  cancelledTimeKernel (fun s z => heatKernelSecond s i j z) φ x y

/-- A universal positive constant for the paired commutator estimate. -/
def rieszCommutatorConstant : ℝ :=
  heatKernelTimeConstant * (comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) + 1)

theorem rieszCommutatorConstant_pos : 0 < rieszCommutatorConstant := by
  exact mul_pos heatKernelTimeConstant_pos
    (add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg zero_lt_one)

/-- The explicit heat Hessian is jointly measurable in time and space,
including the totalized formula at time zero. -/
theorem heatKernelSecond_joint_measurable (i j : Fin 3) :
    Measurable (Function.uncurry (fun s z => heatKernelSecond s i j z)) := by
  have hcoord (a : Fin 3) : Measurable (fun p : ℝ × Space => p.2 a) := by
    have hc : Continuous (fun z : Space => z a) := by
      convert! (innerSL ℝ (NavierStokes.ProblemStatement.coordinateVector a)).continuous using 1
      ext z
      simp [NavierStokes.ProblemStatement.coordinateVector, EuclideanSpace.inner_single_left]
    exact hc.measurable.comp measurable_snd
  have hs : Measurable (fun p : ℝ × Space => p.1) := measurable_fst
  have hz : Measurable (fun p : ℝ × Space => p.2) := measurable_snd
  have hs2 : Measurable (fun p : ℝ × Space => p.1 ^ 2) := by
    simpa only [pow_two] using! hs.mul hs
  have hz2 : Measurable (fun p : ℝ × Space => ‖p.2‖ ^ 2) := by
    simpa only [pow_two] using! hz.norm.mul hz.norm
  have hcoeff : Measurable (fun p : ℝ × Space =>
      p.2 i * p.2 j / (4 * p.1 ^ 2) - (if i = j then 1 else 0) / (2 * p.1)) :=
    (((hcoord i).mul (hcoord j)).div (measurable_const.mul hs2)).sub
      (measurable_const.div (measurable_const.mul hs))
  have hbase : Measurable (fun p : ℝ × Space =>
      (4 * Real.pi * p.1) ^ (-(3 / 2 : ℝ))) :=
    (measurable_const.mul hs).pow_const _
  have hexp : Measurable (fun p : ℝ × Space =>
      Real.exp (-(‖p.2‖ ^ 2) / (4 * p.1))) :=
    Real.continuous_exp.measurable.comp (hz2.neg.div (measurable_const.mul hs))
  simpa only [Function.uncurry, heatKernelSecond, heatKernel] using!
    hcoeff.mul (hbase.mul hexp)

/-- The integrated, cancelled heat kernel is jointly measurable in its two
spatial variables. -/
theorem heatCommutatorKernel_measurable (i j : Fin 3) {φ : Space → ℝ}
    (hφ : Measurable φ) :
    Measurable (Function.uncurry (heatCommutatorKernel i j φ)) :=
  cancelledTimeKernel_measurable (heatKernelSecond_joint_measurable i j) hφ

/-- Pointwise domination by the radial commutator kernel. -/
theorem heatCommutatorKernel_bound (i j : Fin 3) {φ : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖) (x y : Space) :
    ‖heatCommutatorKernel i j φ x y‖ ≤
      (heatKernelTimeConstant * max (2 * L) 1) * radialCommutatorKernel R (x - y) := by
  simpa only [heatCommutatorKernel, Real.norm_eq_abs, radialCommutatorKernel] using
    cancelledTimeKernel_le heatKernelTimeConstant_pos.le hR
      (fun z hz => heatKernelSecond_integral_abs_le i j hz) hφ hLip x y

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




/-- The actual heat commutator satisfies the required paired estimate, with
the precise `R^(-3/4)` decay and a universal positive constant. -/
theorem heatKernel_paired_commutator_bound (i j : Fin 3)
    {φ g : Space → ℝ} {r : Space → E} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (hg : Integrable g volume) (hr : MemLp r 4 volume) :
    ‖∫ x, g x • ∫ y, heatCommutatorKernel i j φ x y • r y‖ ≤
      (rieszCommutatorConstant * max (2 * L) 1) * R ^ (-(3 / 4) : ℝ) *
        comparisonLpNorm 1 g * comparisonLpNorm 4 r := by
  have hmax : 0 ≤ max (2 * L) 1 := le_trans zero_le_one (le_max_right _ _)
  have hcoeff : 0 ≤ heatKernelTimeConstant * max (2 * L) 1 :=
    mul_nonneg heatKernelTimeConstant_pos.le hmax
  calc
    ‖∫ x, g x • ∫ y, heatCommutatorKernel i j φ x y • r y‖ ≤
        (heatKernelTimeConstant * max (2 * L) 1) * comparisonLpNorm 1 g *
          comparisonLpNorm (4 / 3) (radialCommutatorKernel R) * comparisonLpNorm 4 r :=
      PairedKernelBound.norm_paired_kernel_le_scaled
        (heatCommutatorKernel_measurable i j hφm) (radialCommutatorKernel_memLp hR)
        hr hg hcoeff (heatCommutatorKernel_bound i j hR hφ hLip)
    _ = (heatKernelTimeConstant * comparisonLpNorm (4 / 3) (radialCommutatorKernel 1)) *
        max (2 * L) 1 * R ^ (-(3 / 4) : ℝ) * comparisonLpNorm 1 g * comparisonLpNorm 4 r := by
      rw [radialCommutatorKernel_lpNorm_scale hR]
      ring
    _ ≤ (rieszCommutatorConstant * max (2 * L) 1) * R ^ (-(3 / 4) : ℝ) *
        comparisonLpNorm 1 g * comparisonLpNorm 4 r := by
      unfold rieszCommutatorConstant
      apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
      apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hR.le _)
      apply mul_le_mul_of_nonneg_right _ hmax
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one)
        heatKernelTimeConstant_pos.le

end NavierStokesR3.Comparison
end

/-! Merged from `NavierStokes.R3.HeatKernelFubini`. -/
/-!
# Fubini after insertion of the cutoff difference

The time kernel is multiplied by the cutoff difference before estimating its
absolute integral. The resulting radial majorant belongs to `L^(4/3)`, so
Hölder with the `L^4` test function proves integrability on space times time.
-/


noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- The complex pairing integrand, with cancellation already inserted. -/
def cancelledComplexTimeIntegrand (K : ℝ → Space → ℝ) (φ : Space → ℝ)
    (r : Space → ℂ) (x : Space) (ys : Space × ℝ) : ℂ :=
  (K ys.2 (x - ys.1) * cutoffSquareDifference φ x ys.1) • r ys.1

theorem cancelledComplexTimeIntegrand_measurable {K : ℝ → Space → ℝ}
    {φ : Space → ℝ} {r : Space → ℂ}
    (hK : Measurable (Function.uncurry K)) (hφ : Measurable φ)
    (hr : Measurable r) (x : Space) :
    Measurable (cancelledComplexTimeIntegrand K φ r x) := by
  have hmap : Measurable (fun p : Space × ℝ => ((x, p.1), p.2)) := by fun_prop
  exact ((cancelledTimeIntegrand_measurable hK hφ).comp hmap).smul
    (hr.comp measurable_fst)

private theorem cancelledComplexTimeIntegrand_norm_timeIntegral
    (K : ℝ → Space → ℝ) (φ : Space → ℝ) (r : Space → ℂ) (x y : Space) :
    (∫ s in Ioi (0 : ℝ), ‖cancelledComplexTimeIntegrand K φ r x (y, s)‖) =
      absoluteCancelledTimeKernel K φ x y * ‖r y‖ := by
  simp only [cancelledComplexTimeIntegrand, norm_smul, Real.norm_eq_abs,
    absoluteCancelledTimeKernel, integral_mul_const]

/-- The cancelled integrand is absolutely integrable on the product space.
The time-section hypothesis is needed only away from the origin; cancellation
makes the diagonal section identically zero. -/
theorem cancelledTimeKernel_product_integrable {K : ℝ → Space → ℝ}
    {φ : Space → ℝ} {r : Space → ℂ} {C L R : ℝ}
    (hKmeas : Measurable (Function.uncurry K)) (hφmeas : Measurable φ)
    (hrmeas : Measurable r)
    (hKint : ∀ z ≠ 0, IntegrableOn (fun s => K s z) (Ioi (0 : ℝ)) volume)
    (hC : 0 ≤ C) (hR : 0 < R)
    (hKbound : ∀ z ≠ 0, (∫ s in Ioi (0 : ℝ), |K s z|) ≤ C * ‖z‖ ^ (-3 : ℝ))
    (hφrange : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (hr : MemLp r 4 volume) (x : Space) :
    Integrable (cancelledComplexTimeIntegrand K φ r x)
      ((volume : Measure Space).prod ((volume : Measure ℝ).restrict (Ioi 0))) := by
  have hD : 0 ≤ C * max (2 * L) 1 :=
    mul_nonneg hC (zero_le_one.trans (le_max_right _ _))
  have hm : AEStronglyMeasurable
      (fun y : Space => absoluteCancelledTimeKernel K φ x y) volume :=
    ((absoluteCancelledTimeKernel_measurable hKmeas hφmeas).comp
      measurable_prodMk_left).aestronglyMeasurable
  have hb : ∀ᵐ y ∂volume, ‖absoluteCancelledTimeKernel K φ x y‖ ≤
      (C * max (2 * L) 1) * radialCommutatorKernel R (x - y) := by
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (absoluteCancelledTimeKernel_nonneg K φ x y)]
    exact absoluteCancelledTimeKernel_le hC hR hKbound hφrange hLip x y
  have hmarginal :=
    PairedKernelBound.dominated_section_integrable_and_integral_norm_le_scaled
      x hm (radialCommutatorKernel_memLp hR) hr.norm hD hb
  have hmeas : AEStronglyMeasurable (cancelledComplexTimeIntegrand K φ r x)
      ((volume : Measure Space).prod ((volume : Measure ℝ).restrict (Ioi 0))) :=
    (cancelledComplexTimeIntegrand_measurable hKmeas hφmeas hrmeas x).aestronglyMeasurable
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · refine Filter.Eventually.of_forall fun y => ?_
    exact (cancelledTimeKernel_integrable_time hKint φ x y).smul_const (r y)
  · simpa only [cancelledComplexTimeIntegrand_norm_timeIntegral, smul_eq_mul] using
      hmarginal.1

/-- Cancellation justifies exchanging the heat-time and spatial integrals. -/
theorem cancelledTimeKernel_integral_swap {K : ℝ → Space → ℝ}
    {φ : Space → ℝ} {r : Space → ℂ} {C L R : ℝ}
    (hKmeas : Measurable (Function.uncurry K)) (hφmeas : Measurable φ)
    (hrmeas : Measurable r)
    (hKint : ∀ z ≠ 0, IntegrableOn (fun s => K s z) (Ioi (0 : ℝ)) volume)
    (hC : 0 ≤ C) (hR : 0 < R)
    (hKbound : ∀ z ≠ 0, (∫ s in Ioi (0 : ℝ), |K s z|) ≤ C * ‖z‖ ^ (-3 : ℝ))
    (hφrange : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (hr : MemLp r 4 volume) (x : Space) :
    (∫ s in Ioi (0 : ℝ), ∫ y : Space,
      (K s (x - y) * cutoffSquareDifference φ x y) • r y) =
      ∫ y : Space, cancelledTimeKernel K φ x y • r y := by
  have hprod := cancelledTimeKernel_product_integrable hKmeas hφmeas hrmeas
    hKint hC hR hKbound hφrange hLip hr x
  calc
    (∫ s in Ioi (0 : ℝ), ∫ y : Space,
        (K s (x - y) * cutoffSquareDifference φ x y) • r y) =
        ∫ y : Space, ∫ s in Ioi (0 : ℝ),
          (K s (x - y) * cutoffSquareDifference φ x y) • r y := by
      exact (integral_integral_swap
        (f := fun (y : Space) (s : ℝ) =>
          (K s (x - y) * cutoffSquareDifference φ x y) • r y) hprod).symm
    _ = _ := by simp only [cancelledTimeKernel, integral_smul_const]

end NavierStokesR3.Comparison


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
    a • z = (a : ℂ) * z :=
  Complex.real_smul

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

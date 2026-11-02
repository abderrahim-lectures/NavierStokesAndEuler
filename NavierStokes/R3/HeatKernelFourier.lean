import NavierStokes.R3.HeatKernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import NavierStokes.R3.RieszTestOperators
import NavierStokes.R3.ComparisonFourierSetup
import NavierStokes.R3.RieszSymbolRegularity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Fourier.Inversion

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

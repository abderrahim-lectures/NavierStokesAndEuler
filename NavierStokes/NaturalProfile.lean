import NavierStokes.NaturalAxisCoefficients
import NavierStokes.NaturalAxisBridge
import NavierStokes.AxisSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Actual natural profiles in the original radial variable

This module reconstructs the unscaled natural profiles from the actual smooth
solutions of the coefficient-space problem. Derivative identities refer to
ordinary derivatives of the reconstructed real functions.
-/
/-! Merged from `NavierStokes.AxisReference` (in a section, so its `open`s cannot leak). -/
section
/-!
# Identification and positivity of the actual natural-axis reference

The reference is the image of the unit datum under the constructed Banach-space
resolvent. Its coefficient recurrence identifies its evaluation with the entire
leading series. Uniform estimates for the actual nonlinear profiles then preserve
positivity and a strict logarithmic-slope margin at one common parameter scale.
-/

noncomputable section

namespace NavierStokes.AxisReference

open Set AxisCoefficientSpace AxisWeightEstimates NaturalAxisBridge
open scoped BigOperators Topology ContDiff


theorem coefficient_naturalOperator_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ A : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    coefficient I (weight ε) (AxisResolvent.naturalOperator I hε χ A) 0 η = 0 := by
  simp only [AxisResolvent.naturalOperator, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, coefficient, Submodule.coe_smul, jet_smul]
  have hz := AxisOperators.jet_regularInverse_zero I hε 2 (by norm_num)
    (AxisOperators.product I hε χ A) 0 hη
  dsimp only [AxisOperators.inputJet] at hz
  rw [hz, mul_zero]

theorem coefficient_naturalOperator_succ (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ A : AxisSpace I ε) (hχ : RadiallyConstant I ε χ)
    (n : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    coefficient I (weight ε) (AxisResolvent.naturalOperator I hε χ A) (n + 1) η =
      (1 / 2 : ℝ) * (coefficient I (weight ε) χ 0 η *
        coefficient I (weight ε) A n η / radialDivisor 2 n) := by
  simp only [AxisResolvent.naturalOperator, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, coefficient, Submodule.coe_smul, jet_smul]
  have hs := AxisOperators.jet_regularInverse_succ I hε 2 (by norm_num)
    (AxisOperators.product I hε χ A) n 0 hη
  dsimp only [AxisOperators.inputJet] at hs
  rw [hs]
  change (1 / 2 : ℝ) *
      (coefficient I (weight ε) (AxisOperators.product I hε χ A) n η /
        radialDivisor 2 n) = _
  rw [coefficient_product_constant I hε χ A hχ n hη]
  rfl

/-- The unit datum is preserved at the axis by the actual resolvent. -/
theorem reference_coefficient_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ e : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval)
    (he : coefficient I (weight ε) e 0 η = 1) :
    coefficient I (weight ε) (AxisResolvent.naturalResolvent I hε χ e) 0 η = 1 := by
  have heq := congrArg (fun A : AxisSpace I ε => coefficient I (weight ε) A 0 η)
    (AxisResolvent.naturalResolvent_equation I hε χ e)
  simp only [coefficient, Submodule.coe_add, jet_add] at heq
  change coefficient I (weight ε) (AxisResolvent.naturalResolvent I hε χ e) 0 η +
      coefficient I (weight ε)
        (AxisResolvent.naturalOperator I hε χ
          (AxisResolvent.naturalResolvent I hε χ e)) 0 η =
      coefficient I (weight ε) e 0 η at heq
  rw [coefficient_naturalOperator_zero I hε χ _ hη, add_zero, he] at heq
  exact heq

/-- Every higher coefficient is forced by the resolvent equation; the
recurrence is derived from the bounded operators, rather than postulated. -/
theorem reference_coefficient_succ (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ e : AxisSpace I ε) (hχ : RadiallyConstant I ε χ)
    (he : RadiallyConstant I ε e) (n : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    coefficient I (weight ε) (AxisResolvent.naturalResolvent I hε χ e) (n + 1) η =
      (-coefficient I (weight ε) χ 0 η / 2) *
        coefficient I (weight ε) (AxisResolvent.naturalResolvent I hε χ e) n η /
          radialDivisor 2 n := by
  have heq := congrArg
    (fun A : AxisSpace I ε => coefficient I (weight ε) A (n + 1) η)
    (AxisResolvent.naturalResolvent_equation I hε χ e)
  simp only [coefficient, Submodule.coe_add, jet_add] at heq
  change coefficient I (weight ε) (AxisResolvent.naturalResolvent I hε χ e) (n + 1) η +
      coefficient I (weight ε)
        (AxisResolvent.naturalOperator I hε χ
          (AxisResolvent.naturalResolvent I hε χ e)) (n + 1) η =
      coefficient I (weight ε) e (n + 1) η at heq
  rw [coefficient_naturalOperator_succ I hε χ _ hχ n hη,
    he (n + 1) (by omega) η hη] at heq
  linear_combination heq

/-- The constructed resolvent has the factorial coefficients of the
regular Bessel-type reference. -/
theorem reference_coefficient (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ e : AxisSpace I ε) (hχ : RadiallyConstant I ε χ)
    (he : RadiallyConstant I ε e) {η : ℝ} (hη : η ∈ I.interval)
    (he0 : coefficient I (weight ε) e 0 η = 1) (n : ℕ) :
    coefficient I (weight ε) (AxisResolvent.naturalResolvent I hε χ e) n η =
      (-coefficient I (weight ε) χ 0 η / 2) ^ n /
        ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)) := by
  induction n with
  | zero => simpa using reference_coefficient_zero I hε χ e hη he0
  | succ n ih =>
      rw [reference_coefficient_succ I hε χ e hχ he n hη, ih]
      have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        radialDivisor, Nat.cast_ofNat, pow_succ]
      field_simp ; ring

/-- Evaluation of the actual coefficient-space reference equals the
entire leading series at every real radius. -/
theorem reference_profile_eq_series (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ e : AxisSpace I ε) (hχ : RadiallyConstant I ε χ)
    (he : RadiallyConstant I ε e) {η : ℝ} (hη : η ∈ I.interval)
    (he0 : coefficient I (weight ε) e 0 η = 1) (Y : ℝ) :
    AxisEvaluation.profile I ε (AxisResolvent.naturalResolvent I hε χ e) (Y, η) =
      AxisSeries.profile (coefficient I (weight ε) χ 0 η) Y := by
  rw [AxisEvaluation.profile, AxisSeries.profile_eq_tsum]
  apply tsum_congr
  intro n
  rw [reference_coefficient I hε χ e hχ he hη he0 n]
  rw [← mul_div_assoc, ← mul_pow]
  congr 2
  ring

/-- In particular, the leading pair used by the nonlinear existence theorem
has exactly this angular series. -/
theorem referenceCoefficients_profile_eq_series (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) {η : ℝ} (hη : η ∈ I.interval) (Y : ℝ) :
    AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1 (Y, η) =
      AxisSeries.profile (inputValue I ε χ η) Y := by
  exact reference_profile_eq_series I hε χ d.one hd.chi_radial hd.one_radial
    hη (hd.one_value η hη) Y

theorem referenceCoefficients_deriv_Y_eq (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) {η : ℝ} (hη : η ∈ I.interval) (Y : ℝ) :
    deriv (fun y => AxisEvaluation.profile I ε
      (referenceCoefficients I hε χ d).1 (y, η)) Y =
        deriv (AxisSeries.profile (inputValue I ε χ η)) Y := by
  congr 2
  funext y
  exact referenceCoefficients_profile_eq_series I hε χ d hd hη y

/-- The lower bound concerns the reference constructed by the resolvent,
not a separately declared comparison function. -/
theorem referenceCoefficients_gt_quarter (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) {η Y : ℝ} (hη : η ∈ I.interval)
    (hχ0 : 0 ≤ inputValue I ε χ η) (hχ1 : inputValue I ε χ η ≤ 1)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 41 / 10) :
    1 / 4 < AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1 (Y, η) := by
  rw [referenceCoefficients_profile_eq_series I hε χ d hd hη]
  exact AxisSeries.profile_gt_quarter _ Y hχ0 hχ1 hY0 hY1

theorem referenceCoefficients_log_slope_at_four (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) {η : ℝ} (hη : η ∈ I.interval)
    (hχ99 : 99 / 100 ≤ inputValue I ε χ η) (hχ1 : inputValue I ε χ η ≤ 1) :
    236 / 100 <
      -8 * deriv (fun y => AxisEvaluation.profile I ε
        (referenceCoefficients I hε χ d).1 (y, η)) 4 /
          AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1 (4, η) := by
  rw [referenceCoefficients_deriv_Y_eq I hε χ d hd hη,
    referenceCoefficients_profile_eq_series I hε χ d hd hη]
  exact AxisSeries.profile_log_slope_at_four _ hχ99 hχ1

/-- Quantitative stability of the strict slope margin under simultaneous
value and first-derivative errors of at most `1/1000`. -/
theorem log_slope_stability {v₀ v d₀ d : ℝ}
    (hv₀ : 1 / 4 < v₀) (hvalue : |v - v₀| ≤ 1 / 1000)
    (hderiv : |d - d₀| ≤ 1 / 1000) (hslope : 236 / 100 < -8 * d₀ / v₀) :
    1 / 8 < v ∧ 23 / 10 < -8 * d / v := by
  have hv : 1 / 8 < v := by
    have := (abs_le.mp hvalue).1
    linarith
  refine ⟨hv, ?_⟩
  have hvpos : 0 < v := by linarith
  have hv₀pos : 0 < v₀ := by linarith
  rw [lt_div_iff₀ hvpos]
  rw [lt_div_iff₀ hv₀pos] at hslope
  have he0 := (abs_le.mp hvalue).2
  have he1 := (abs_le.mp hderiv).2
  nlinarith

/-- A single lower bound on the scale makes both evaluation constants
small enough for positivity and logarithmic-slope stability. -/
theorem scaled_error_le {C C₀ C₁ K Λ : ℝ}
    (hCsum : C ≤ C₀ + C₁) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hK : 0 ≤ K) (hΛ : 1 + 500 * (C₀ + C₁) * K ≤ Λ) :
    C * (K / (2 * Λ)) ≤ 1 / 1000 := by
  have hsum : 0 ≤ C₀ + C₁ := add_nonneg hC₀ hC₁
  have hΛpos : 0 < Λ := by nlinarith [mul_nonneg hsum hK]
  rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 2 * Λ)]
  nlinarith [mul_le_mul_of_nonneg_right hCsum hK]

/-- This explicit threshold controls both values and first radial derivatives
on `|Y|≤5`, uniformly over the parameter interval. -/
def stabilityScale (ε K : ℝ) : ℝ :=
  1 + 500 * (AxisEvaluation.jetBound ε 5 0 0 + AxisEvaluation.jetBound ε 5 1 0) * K


theorem value_error_le (I : Window) {ε K Λ : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hΛ : stabilityScale ε K ≤ Λ) {Φ u Φ₀ u₀ : ℝ × ℝ → ℝ}
    (herr : UniformMixedError I ε (K / (2 * Λ)) Φ u Φ₀ u₀)
    {p : ℝ × ℝ} (hY : |p.1| ≤ 5) (hη : p.2 ∈ Ioo I.left I.right) :
    |Φ p - Φ₀ p| ≤ 1 / 1000 := by
  have hC₀ := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 0 0
  have hC₁ := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 1 0
  have hb : AxisEvaluation.jetBound ε 5 0 0 * (K / (2 * Λ)) ≤ 1 / 1000 :=
    scaled_error_le (le_add_of_nonneg_right hC₁) hC₀ hC₁ hK hΛ
  have he := (herr 5 (by norm_num) (by norm_num) 0 0 p hY hη).1
  exact le_trans (by simpa only [mixedDerivative, iteratedDeriv_zero] using he) hb

theorem radial_deriv_error_le (I : Window) {ε K Λ : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hΛ : stabilityScale ε K ≤ Λ) {Φ u Φ₀ u₀ : ℝ × ℝ → ℝ}
    (herr : UniformMixedError I ε (K / (2 * Λ)) Φ u Φ₀ u₀)
    {p : ℝ × ℝ} (hY : |p.1| ≤ 5) (hη : p.2 ∈ Ioo I.left I.right) :
    |partialY Φ p - partialY Φ₀ p| ≤ 1 / 1000 := by
  have hC₀ := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 0 0
  have hC₁ := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 1 0
  have hb : AxisEvaluation.jetBound ε 5 1 0 * (K / (2 * Λ)) ≤ 1 / 1000 :=
    scaled_error_le (le_add_of_nonneg_left hC₀) hC₀ hC₁ hK hΛ
  have he := (herr 5 (by norm_num) (by norm_num) 1 0 p hY hη).1
  exact le_trans
    (by simpa only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one, partialY] using he) hb

/-- Uniform closeness to the actual reference preserves a positive margin
on the full closed radial interval. -/
theorem positive_of_uniformMixedError (I : Window) {ε K Λ : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) (hK : 0 ≤ K) (hΛ : stabilityScale ε K ≤ Λ)
    {Φ u u₀ : ℝ × ℝ → ℝ}
    (herr : UniformMixedError I ε (K / (2 * Λ)) Φ u
      (AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1) u₀)
    {Y η : ℝ} (hY0 : 0 ≤ Y) (hY1 : Y ≤ 41 / 10)
    (hη : η ∈ Ioo I.left I.right)
    (hχ0 : 0 ≤ inputValue I ε χ η) (hχ1 : inputValue I ε χ η ≤ 1) :
    1 / 8 < Φ (Y, η) := by
  have href := referenceCoefficients_gt_quarter I hε χ d hd
    (show η ∈ I.interval from ⟨hη.1.le, hη.2.le⟩) hχ0 hχ1 hY0 hY1
  have he := value_error_le I hε hK hΛ herr
    (p := (Y, η)) (by simpa only [abs_of_nonneg hY0] using (show Y ≤ 5 by linarith)) hη
  have he' := (abs_le.mp he).1
  linarith

/-- The same scale preserves a strict slope greater than `2.3` wherever
the parameter coefficient is at least `0.99`. -/
theorem log_slope_of_uniformMixedError (I : Window) {ε K Λ : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) (hK : 0 ≤ K) (hΛ : stabilityScale ε K ≤ Λ)
    {Φ u u₀ : ℝ × ℝ → ℝ}
    (herr : UniformMixedError I ε (K / (2 * Λ)) Φ u
      (AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1) u₀)
    {η : ℝ} (hη : η ∈ Ioo I.left I.right)
    (hχ99 : 99 / 100 ≤ inputValue I ε χ η) (hχ1 : inputValue I ε χ η ≤ 1) :
    23 / 10 < -8 * partialY Φ (4, η) / Φ (4, η) := by
  have hη' : η ∈ I.interval := ⟨hη.1.le, hη.2.le⟩
  have href := referenceCoefficients_gt_quarter I hε χ d hd hη'
    (by linarith : 0 ≤ inputValue I ε χ η) hχ1
    (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (4 : ℝ) ≤ 41 / 10)
  have hslope := referenceCoefficients_log_slope_at_four I hε χ d hd hη' hχ99 hχ1
  exact (log_slope_stability href
    (value_error_le I hε hK hΛ herr (p := (4, η)) (by norm_num) hη)
    (radial_deriv_error_le I hε hK hΛ herr (p := (4, η)) (by norm_num) hη)
    hslope).2

/-- One sufficiently large scale gives the actual smooth nonlinear
profiles, all mixed-derivative estimates, uniform positivity, and the strict
angular slope bound, simultaneously for the full amplitude norm ball. -/
theorem exists_positive_scaled_profiles (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d)
    (hχ : ∀ η ∈ I.interval, 0 ≤ inputValue I ε χ η ∧ inputValue I ε χ η ≤ 1)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
      ∀ a : AxisSpace I ε, ‖a‖ ≤ M → RadiallyConstant I ε a →
      ∃ Φ u B P : ℝ × ℝ → ℝ,
        IsScaledSolution I (parameters I ε χ d) (1 / Λ) (inputValue I ε a) Φ u B P ∧
        UniformMixedError I ε (errorConstant I hε χ d M hM / (2 * Λ))
          Φ u (AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1)
          (AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).2) ∧
        (∀ Y ∈ Icc (0 : ℝ) (41 / 10), ∀ η ∈ Ioo I.left I.right, 1 / 8 < Φ (Y, η)) ∧
        (∀ η ∈ Ioo I.left I.right, 99 / 100 ≤ inputValue I ε χ η →
          23 / 10 < -8 * partialY Φ (4, η) / Φ (4, η)) := by
  obtain ⟨Λ₀, hΛ₀, hexists⟩ := exists_scaled_profiles I hε χ d hd M hM
  refine ⟨max Λ₀ (stabilityScale ε (errorConstant I hε χ d M hM)),
    hΛ₀.trans_le (le_max_left _ _), ?_⟩
  intro Λ hΛ a ha harad
  obtain ⟨Φ, u, B, P, hsol, herr⟩ := hexists Λ ((le_max_left _ _).trans hΛ) a ha harad
  have hscale : stabilityScale ε (errorConstant I hε χ d M hM) ≤ Λ :=
    (le_max_right _ _).trans hΛ
  have hK := errorConstant_nonneg I hε χ d M hM
  refine ⟨Φ, u, B, P, hsol, herr, ?_, ?_⟩
  · intro Y hY η hη
    have hχη := hχ η ⟨hη.1.le, hη.2.le⟩
    exact positive_of_uniformMixedError I hε χ d hd hK hscale herr
      hY.1 hY.2 hη hχη.1 hχη.2
  · intro η hη hχ99
    exact log_slope_of_uniformMixedError I hε χ d hd hK hscale herr hη hχ99
      (hχ η ⟨hη.1.le, hη.2.le⟩).2

end NavierStokes.AxisReference

end
end


noncomputable section

namespace NavierStokes.NaturalProfile

open Set Filter NaturalAxisBridge NaturalAxisCoefficients
open scoped Topology ContDiff


def rescalePoint (Λ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (Λ * p.1, p.2)

def domain (Λ : ℝ) : Set (ℝ × ℝ) :=
  rescalePoint Λ ⁻¹' AxisEvaluation.strip window 20

def pullback (Λ : ℝ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := F (rescalePoint Λ p)

def affineProfile (b : ℝ → ℝ) (c Λ : ℝ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  b p.2 + c * pullback Λ F p

def angularProfile (a : ℝ → ℝ) (Λ : ℝ) (Φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  a p.2 * pullback Λ Φ p

theorem contDiff_rescalePoint (Λ : ℝ) : ContDiff ℝ ∞ (rescalePoint Λ) := by
  exact (contDiff_const.mul contDiff_fst).prodMk contDiff_snd

theorem domain_isOpen (Λ : ℝ) : IsOpen (domain Λ) :=
  (AxisEvaluation.strip_isOpen window 20).preimage (contDiff_rescalePoint Λ).continuous

theorem pullback_smooth {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20)) (Λ : ℝ) :
    ContDiffOn ℝ ∞ (pullback Λ F) (domain Λ) :=
  hF.comp (contDiff_rescalePoint Λ).contDiffOn (fun _ hp => hp)

theorem affineProfile_smooth {b : ℝ → ℝ}
    (hb : ContDiffOn ℝ ∞ b (Ioo window.left window.right))
    {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (c Λ : ℝ) : ContDiffOn ℝ ∞ (affineProfile b c Λ F) (domain Λ) := by
  exact (hb.comp (s := domain Λ) (t := Ioo window.left window.right)
    contDiff_snd.contDiffOn (fun _ hp => hp.2)).add
    (contDiffOn_const.mul (pullback_smooth hF Λ))

theorem angularProfile_smooth {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a (Ioo window.left window.right))
    {Φ : ℝ × ℝ → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip window 20))
    (Λ : ℝ) : ContDiffOn ℝ ∞ (angularProfile a Λ Φ) (domain Λ) := by
  exact (ha.comp (s := domain Λ) (t := Ioo window.left window.right)
    contDiff_snd.contDiffOn (fun _ hp => hp.2)).mul (pullback_smooth hΦ Λ)

theorem sliceY_smooth {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip window 20) :
    ContDiffAt ℝ ∞ (fun Y : ℝ => F (Y, p.2)) p.1 := by
  exact (hF.contDiffAt ((AxisEvaluation.strip_isOpen window 20).mem_nhds hp)).comp p.1
    (contDiffAt_id.prodMk contDiffAt_const)

theorem sliceEta_smooth {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip window 20) :
    ContDiffAt ℝ ∞ (fun η : ℝ => F (p.1, η)) p.2 := by
  exact (hF.contDiffAt ((AxisEvaluation.strip_isOpen window 20).mem_nhds hp)).comp p.2
    (contDiffAt_const.prodMk contDiffAt_id)

theorem pullback_hasDerivAt_Y {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    HasDerivAt (fun X : ℝ => pullback Λ F (X, p.2))
      (Λ * partialY F (rescalePoint Λ p)) p.1 := by
  have hf := (sliceY_smooth hF hp).differentiableAt (by norm_num)
  have hd := hf.hasDerivAt.comp p.1 ((hasDerivAt_id p.1).const_mul Λ)
  simp only [Function.comp_def, mul_one] at hd
  convert! hd using 1 ; simp only [rescalePoint, partialY, mul_comm]



theorem pullback_second_Y {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    iteratedDeriv 2 (fun X : ℝ => pullback Λ F (X, p.2)) p.1 =
      Λ ^ 2 * iteratedDeriv 2 (fun Y : ℝ => F (Y, p.2)) (Λ * p.1) := by
  have hs := sliceY_smooth hF hp
  have hs' : ContDiffAt ℝ 1 (deriv (fun Y : ℝ => F (Y, p.2))) (Λ * p.1) := by
    exact (hs.fderiv_right (m := 1)
        (by simp)).clm_apply
        contDiffAt_const
  have hd := ((hs'.differentiableAt (by norm_num)).hasDerivAt.comp p.1
    ((hasDerivAt_id p.1).const_mul Λ)).const_mul Λ
  have heq : deriv (fun X : ℝ => pullback Λ F (X, p.2)) =ᶠ[𝓝 p.1]
      (fun X : ℝ => Λ * deriv (fun Y : ℝ => F (Y, p.2)) (Λ * X)) := by
    have hc : Continuous (fun X : ℝ => (Λ * X, p.2)) :=
      (continuous_const.mul continuous_id).prodMk continuous_const
    filter_upwards [hc.continuousAt.eventually
      ((AxisEvaluation.strip_isOpen window 20).mem_nhds hp)] with X hX
    exact (pullback_hasDerivAt_Y hF Λ (p := (X, p.2)) hX).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq]
  convert! hd.deriv using 1
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  ring


theorem affineProfile_partialY {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (b : ℝ → ℝ) (c Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    partialY (affineProfile b c Λ F) p = c * Λ * partialY F (rescalePoint Λ p) := by
  simpa only [affineProfile, partialY, mul_assoc] using
    ((pullback_hasDerivAt_Y hF Λ hp).const_mul c).const_add (b p.2) |>.deriv

theorem affineProfile_partialEta {b : ℝ → ℝ} {b' : ℝ}
    {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (c Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) (hb : HasDerivAt b b' p.2) :
    partialEta (affineProfile b c Λ F) p = b' + c * partialEta F (rescalePoint Λ p) := by
  have hf := (sliceEta_smooth hF hp).differentiableAt (by norm_num)
  exact (hb.add (hf.hasDerivAt.const_mul c)).deriv

theorem affineProfile_radialDifferential {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (b : ℝ → ℝ) (c Λ : ℝ) (r : ℕ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    radialDifferential r (affineProfile b c Λ F) p =
      c * Λ * radialDifferential r F (rescalePoint Λ p) := by
  have hs : ContDiffAt ℝ 2 (fun X : ℝ => pullback Λ F (X, p.2)) p.1 := by
    exact ((sliceY_smooth hF hp).comp p.1 (contDiffAt_const.mul contDiffAt_id)).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  unfold radialDifferential
  rw [affineProfile_partialY hF b c Λ hp]
  change p.1 * iteratedDeriv 2 (fun X => b p.2 + c * pullback Λ F (X, p.2)) p.1 + _ = _
  rw [iteratedDeriv_const_add (by norm_num : 0 < (2 : ℕ)),
    iteratedDeriv_const_mul c hs, pullback_second_Y hF Λ hp]
  dsimp [rescalePoint]
  ring

theorem angularProfile_partialY {Φ : ℝ × ℝ → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip window 20))
    (a : ℝ → ℝ) (Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    partialY (angularProfile a Λ Φ) p = a p.2 * Λ * partialY Φ (rescalePoint Λ p) := by
  simpa only [angularProfile, partialY, mul_assoc] using
    ((pullback_hasDerivAt_Y hΦ Λ hp).const_mul (a p.2)).deriv

theorem angularProfile_partialEta {a : ℝ → ℝ} {a' : ℝ}
    {Φ : ℝ × ℝ → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip window 20))
    (Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) (ha : HasDerivAt a a' p.2) :
    partialEta (angularProfile a Λ Φ) p =
      a' * Φ (rescalePoint Λ p) + a p.2 * partialEta Φ (rescalePoint Λ p) := by
  have hf := (sliceEta_smooth hΦ hp).differentiableAt (by norm_num)
  exact (ha.mul hf.hasDerivAt).deriv

theorem angularProfile_radialDifferential {Φ : ℝ × ℝ → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip window 20))
    (a : ℝ → ℝ) (Λ : ℝ) (r : ℕ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    radialDifferential r (angularProfile a Λ Φ) p =
      a p.2 * Λ * radialDifferential r Φ (rescalePoint Λ p) := by
  have hs : ContDiffAt ℝ 2 (fun X : ℝ => pullback Λ Φ (X, p.2)) p.1 := by
    exact ((sliceY_smooth hΦ hp).comp p.1 (contDiffAt_const.mul contDiffAt_id)).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  unfold radialDifferential
  rw [angularProfile_partialY hΦ a Λ hp]
  change p.1 * iteratedDeriv 2 (fun X => a p.2 * pullback Λ Φ (X, p.2)) p.1 + _ = _
  rw [iteratedDeriv_const_mul (a p.2) hs, pullback_second_Y hΦ Λ hp]
  dsimp [rescalePoint]
  ring

/-- The fixed polynomial and pressure fields, interpreted as real functions. -/
def actualData (h j σ : ℝ) (P0 : ℝ → ℝ) : ParameterData where
  A := NaturalAxisData.A h
  D := NaturalAxisData.D h
  h := h
  chi := NaturalAxisData.chi h j σ
  d := NaturalAxisData.d
  inverseL := fun η => (NaturalAxisData.L h η)⁻¹
  uStar := NaturalAxisData.U j
  uStarEta := fun _ => 4
  wStar := NaturalAxisData.W h j
  hStar := NaturalAxisData.H h j
  kappa := realGradient h j σ
  zStar := NaturalAxisData.Z h j P0

/-- Replace all coefficient evaluations by their proved concrete values. -/
theorem materialize_scaled {h j σ t : ℝ} {P0 a₀ : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (a : AxisCoefficientSpace.AxisSpace window v.epsilon)
    (ha : ∀ η ∈ window.interval, inputValue window v.epsilon a η = a₀ η)
    {Φ u B P : ℝ × ℝ → ℝ}
    (hs : IsScaledSolution window
      (parameters window v.epsilon (v.elements .chi) v.axisData) t
      (inputValue window v.epsilon a) Φ u B P) :
    IsScaledSolution window (actualData h j σ P0) t a₀ Φ u B P := by
  refine {
    phi_smooth := hs.phi_smooth
    u_smooth := hs.u_smooth
    average_smooth := hs.average_smooth
    pressure_smooth := hs.pressure_smooth
    phi_axis := hs.phi_axis
    u_axis := hs.u_axis
    average_axis := hs.average_axis
    pressure_axis := hs.pressure_axis
    average_equation := hs.average_equation
    average_integral := hs.average_integral
    pressure_equation := ?_
    pressure_integral := ?_
    angular_equation := ?_
    axial_equation := ?_
  }
  · intro p hp
    rw [hs.pressure_equation p hp, ha p.2 ⟨hp.2.1.le, hp.2.2.le⟩]
  · intro p hp
    rw [hs.pressure_integral p hp, ha p.2 ⟨hp.2.1.le, hp.2.2.le⟩]
  · intro p hp
    have hv : ∀ k, inputValue window v.epsilon (v.elements k) p.2 =
        realField h j σ P0 k p.2 := fun k => v.value k ⟨hp.2.1.le, hp.2.2.le⟩
    simpa only [angularRemainder, reconstructedW, reconstructedU, reconstructedH,
      actualData, parameters, CoefficientFamily.axisData, hv, realField] using
      hs.angular_equation p hp
  · intro p hp
    have hv : ∀ k, inputValue window v.epsilon (v.elements k) p.2 =
        realField h j σ P0 k p.2 := fun k => v.value k ⟨hp.2.1.le, hp.2.2.le⟩
    simpa only [axialRemainder, reconstructedW, actualData, parameters,
      CoefficientFamily.axisData, hv, realField] using hs.axial_equation p hp

theorem amplitude_smooth {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (Λ C : ℝ) :
    ContDiffOn ℝ ∞ (realAmplitude h j σ Λ C) (Ioo window.left window.right) := by
  intro η hη
  have hc : ContDiffAt ℂ ∞ (axisPhase h j σ) (η : ℂ) :=
    (d.phase_analytic (η : ℂ) (d.real_mem_compact ⟨hη.1.le, hη.2.le⟩)).contDiffAt
  have hr : ContDiffAt ℝ ∞ (realPhase h j σ) η := by
    simpa only [axisPhase_ofReal, Complex.ofReal_re] using hc.real_of_complex
  exact (((contDiffAt_const.mul hr).exp).mul contDiffAt_const).contDiffWithinAt

theorem uStar_hasDerivAt (j η : ℝ) : HasDerivAt (NaturalAxisData.U j) 4 η := by
  change HasDerivAt (fun x : ℝ => 4 * x + j) 4 η
  simpa only [mul_one, id_eq] using ((hasDerivAt_id η).const_mul 4).add_const j

theorem uStar_smooth (j : ℝ) : ContDiff ℝ ∞ (NaturalAxisData.U j) := by
  exact (contDiff_const.mul contDiff_id).add contDiff_const

/-- The natural transport coefficient recovered from the true radial average. -/
def transportW (h : ℝ) (V : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  1 - 2 * NaturalAxisData.D h * p.2 * V p - NaturalAxisData.d p.2 * partialEta V p

def transportH (h : ℝ) (U : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  NaturalAxisData.D h * p.2 + NaturalAxisData.d p.2 * U p

theorem transportW_reconstruct {h j σ Λ : ℝ} (P0 : ℝ → ℝ) {B : ℝ × ℝ → ℝ}
    (hB : ContDiffOn ℝ ∞ B (AxisEvaluation.strip window 20))
    {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    transportW h (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ B) p =
      reconstructedW (actualData h j σ P0) (1 / Λ) B (rescalePoint Λ p) := by
  unfold transportW
  rw [affineProfile_partialEta hB (1 / Λ) Λ hp (uStar_hasDerivAt j p.2)]
  simp only [affineProfile, pullback, reconstructedW, actualData, rescalePoint,
    NaturalAxisData.W]
  ring

theorem transportH_reconstruct (h j σ Λ : ℝ) (P0 : ℝ → ℝ) (u : ℝ × ℝ → ℝ)
    (p : ℝ × ℝ) :
    transportH h (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u) p =
      reconstructedH (actualData h j σ P0) (1 / Λ) u (rescalePoint Λ p) := by
  simp only [transportH, affineProfile, pullback, reconstructedH, actualData,
    rescalePoint, NaturalAxisData.H]
  ring

theorem gradient_identity (h j σ η : ℝ) :
    NaturalAxisData.H h j η * realGradient h j σ η =
      -NaturalAxisData.L h η * NaturalAxisData.chi h j σ η := by
  unfold realGradient NaturalAxisData.chi
  ring

/-- The actual unscaled system, with all derivatives taken on real functions. -/
structure IsNaturalSolution (h j Λ : ℝ) (P0 a₀ : ℝ → ℝ)
    (f U V Pr : ℝ × ℝ → ℝ) : Prop where
  f_smooth : ContDiffOn ℝ ∞ f (domain Λ)
  U_smooth : ContDiffOn ℝ ∞ U (domain Λ)
  average_smooth : ContDiffOn ℝ ∞ V (domain Λ)
  pressure_smooth : ContDiffOn ℝ ∞ Pr (domain Λ)
  f_axis : ∀ η ∈ Ioo window.left window.right, f (0, η) = a₀ η
  U_axis : ∀ η ∈ Ioo window.left window.right, U (0, η) = NaturalAxisData.U j η
  average_axis : ∀ η ∈ Ioo window.left window.right, V (0, η) = NaturalAxisData.U j η
  pressure_axis : ∀ η ∈ Ioo window.left window.right, Pr (0, η) = P0 η
  average_equation : ∀ p ∈ domain Λ, V p + p.1 * partialY V p = U p
  pressure_equation : ∀ p ∈ domain Λ, partialY Pr p = (f p) ^ 2
  average_integral : ∀ p ∈ domain Λ,
    p.1 * V p = ∫ X in (0 : ℝ)..p.1, U (X, p.2)
  pressure_integral : ∀ p ∈ domain Λ,
    Pr p - P0 p.2 = ∫ X in (0 : ℝ)..p.1, (f (X, p.2)) ^ 2
  angular_equation : ∀ p ∈ domain Λ,
    2 * NaturalAxisData.L h p.2 * radialDifferential 2 f p =
      transportW h V p * (p.1 * partialY f p + f p) +
      h * (1 - 2 * p.2 * U p) * f p + transportH h U p * partialEta f p
  axial_equation : ∀ p ∈ domain Λ,
    2 * NaturalAxisData.L h p.2 * radialDifferential 1 U p =
      transportW h V p * (p.1 * partialY U p) +
      NaturalAxisData.A h * (1 - 2 * p.2 * U p) * U p +
      transportH h U p * partialEta U p + NaturalAxisData.d p.2 * partialEta Pr p -
      4 * NaturalAxisData.A h * p.2 * Pr p - 2 * p.2 * p.1 * partialY Pr p

private theorem angular_rescale_identity
    {Λ L X η h d u U W H Hs κ χ a φ φY φEta R : ℝ}
    (hΛ : Λ ≠ 0) (hL : L ≠ 0) (hχ : Hs * κ = -L * χ)
    (hH : H = Hs + (1 / Λ) * d * u)
    (heq : 2 * R = -χ * φ + (1 / Λ) * L⁻¹ *
      ((W + h * (1 - 2 * η * U) + d * u * κ) * φ +
        W * (Λ * X * φY) + H * φEta)) :
    2 * L * (a * Λ * R) = W * (X * (a * Λ * φY) + a * φ) +
      h * (1 - 2 * η * U) * (a * φ) + H * ((Λ * κ) * a * φ + a * φEta) := by
  calc
    _ = a * Λ * L * (2 * R) := by ring
    _ = a * Λ * L * (-χ * φ + (1 / Λ) * L⁻¹ *
        ((W + h * (1 - 2 * η * U) + d * u * κ) * φ +
          W * (Λ * X * φY) + H * φEta)) := by rw [heq]
    _ = a * (Λ * (Hs * κ) * φ +
        ((W + h * (1 - 2 * η * U) + d * u * κ) * φ +
          W * (Λ * X * φY) + H * φEta)) := by
      rw [hχ]
      field_simp
    _ = _ := by
      rw [hH]
      field_simp ; ring

private theorem axial_rescale_identity
    {Λ L X η A d Us UsEta Hs W u uY uEta P0 P0Eta P PY PEta R : ℝ}
    (hΛ : Λ ≠ 0) (hL : L ≠ 0)
    (heq : 2 * R = -L⁻¹ *
      (-A * (1 - 2 * η * Us) * Us - Hs * UsEta - d * P0Eta + 4 * A * η * P0) +
      (1 / Λ) * L⁻¹ *
        (A * (1 - 4 * η * Us) * u - 2 * A * η * (1 / Λ) * u ^ 2 +
          W * (Λ * X * uY) + Hs * uEta + d * UsEta * u +
          (1 / Λ) * d * u * uEta - 4 * A * η * P + d * PEta - 2 * η * (Λ * X * PY))) :
    2 * L * R = W * (X * uY) +
      A * (1 - 2 * η * (Us + (1 / Λ) * u)) * (Us + (1 / Λ) * u) +
      (Hs + (1 / Λ) * d * u) * (UsEta + (1 / Λ) * uEta) +
      d * (P0Eta + (1 / Λ) * PEta) - 4 * A * η * (P0 + (1 / Λ) * P) -
      2 * η * X * PY := by
  calc
    _ = L * (2 * R) := by ring
    _ = L * (-L⁻¹ *
        (-A * (1 - 2 * η * Us) * Us - Hs * UsEta - d * P0Eta + 4 * A * η * P0) +
        (1 / Λ) * L⁻¹ *
          (A * (1 - 4 * η * Us) * u - 2 * A * η * (1 / Λ) * u ^ 2 +
            W * (Λ * X * uY) + Hs * uEta + d * UsEta * u +
            (1 / Λ) * d * u * uEta - 4 * A * η * P + d * PEta -
            2 * η * (Λ * X * PY))) := by rw [heq]
    _ = _ := by
      field_simp ; ring

theorem angular_equation_reconstruct {h j σ Λ : ℝ} {P0 a₀ : ℝ → ℝ}
    (hsmall : NaturalAxisRange.Parameters h j) (hΛ : Λ ≠ 0)
    {Φ u B P : ℝ × ℝ → ℝ}
    (hs : IsScaledSolution window (actualData h j σ P0) (1 / Λ) a₀ Φ u B P)
    {p : ℝ × ℝ} (hp : p ∈ domain Λ)
    (ha : HasDerivAt a₀ ((Λ * realGradient h j σ p.2) * a₀ p.2) p.2) :
    2 * NaturalAxisData.L h p.2 * radialDifferential 2 (angularProfile a₀ Λ Φ) p =
      transportW h (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ B) p *
        (p.1 * partialY (angularProfile a₀ Λ Φ) p + angularProfile a₀ Λ Φ p) +
      h * (1 - 2 * p.2 * affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u p) *
        angularProfile a₀ Λ Φ p +
      transportH h (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u) p *
        partialEta (angularProfile a₀ Λ Φ) p := by
  rw [angularProfile_radialDifferential hs.phi_smooth a₀ Λ 2 hp,
    angularProfile_partialY hs.phi_smooth a₀ Λ hp,
    angularProfile_partialEta hs.phi_smooth Λ hp ha,
    transportW_reconstruct P0 hs.average_smooth hp,
    transportH_reconstruct h j σ Λ P0 u p]
  have hL : NaturalAxisData.L h p.2 ≠ 0 :=
    (L_pos_on_window hsmall ⟨hp.2.1.le, hp.2.2.le⟩).ne'
  apply angular_rescale_identity hΛ hL (gradient_identity h j σ p.2)
    (H := reconstructedH (actualData h j σ P0) (1 / Λ) u (rescalePoint Λ p))
    (Hs := NaturalAxisData.H h j p.2)
  · rfl
  · simpa only [angularRemainder, actualData, reconstructedU, rescalePoint,
      affineProfile, pullback, mul_assoc] using hs.angular_equation (rescalePoint Λ p) hp

theorem axial_equation_reconstruct {h j σ Λ : ℝ} {P0 a₀ : ℝ → ℝ}
    (hsmall : NaturalAxisRange.Parameters h j) (hΛ : Λ ≠ 0)
    (hP0 : ContDiff ℝ ∞ P0) {Φ u B P : ℝ × ℝ → ℝ}
    (hs : IsScaledSolution window (actualData h j σ P0) (1 / Λ) a₀ Φ u B P)
    {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    2 * NaturalAxisData.L h p.2 *
        radialDifferential 1 (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u) p =
      transportW h (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ B) p *
        (p.1 * partialY (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u) p) +
      NaturalAxisData.A h *
        (1 - 2 * p.2 * affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u p) *
        affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u p +
      transportH h (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u) p *
        partialEta (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u) p +
      NaturalAxisData.d p.2 * partialEta (affineProfile P0 (1 / Λ) Λ P) p -
      4 * NaturalAxisData.A h * p.2 * affineProfile P0 (1 / Λ) Λ P p -
      2 * p.2 * p.1 * partialY (affineProfile P0 (1 / Λ) Λ P) p := by
  rw [affineProfile_radialDifferential hs.u_smooth (NaturalAxisData.U j) (1 / Λ) Λ 1 hp,
    affineProfile_partialY hs.u_smooth (NaturalAxisData.U j) (1 / Λ) Λ hp,
    affineProfile_partialY hs.pressure_smooth P0 (1 / Λ) Λ hp,
    affineProfile_partialEta hs.u_smooth (1 / Λ) Λ hp (uStar_hasDerivAt j p.2),
    affineProfile_partialEta hs.pressure_smooth (1 / Λ) Λ hp
      ((hP0.differentiable (by norm_num)).differentiableAt.hasDerivAt),
    transportW_reconstruct P0 hs.average_smooth hp,
    transportH_reconstruct h j σ Λ P0 u p]
  simp only [one_div_mul_cancel hΛ, one_mul]
  have hL : NaturalAxisData.L h p.2 ≠ 0 :=
    (L_pos_on_window hsmall ⟨hp.2.1.le, hp.2.2.le⟩).ne'
  apply axial_rescale_identity hΛ hL
  simpa only [axialRemainder, actualData, NaturalAxisData.Z, reconstructedH,
    rescalePoint, affineProfile, pullback, mul_assoc] using
      hs.axial_equation (rescalePoint Λ p) hp

theorem domain_segment {Λ : ℝ} (hΛ : 0 < Λ) {p : ℝ × ℝ} (hp : p ∈ domain Λ)
    {X : ℝ} (hX : X ∈ uIcc (0 : ℝ) p.1) : (X, p.2) ∈ domain Λ := by
  change (-20 < Λ * X ∧ Λ * X < 20) ∧ p.2 ∈ Ioo window.left window.right
  change (-20 < Λ * p.1 ∧ Λ * p.1 < 20) ∧ _ at hp
  refine ⟨?_, hp.2⟩
  rcases le_total 0 p.1 with hpos | hneg
  · rw [uIcc_of_le hpos] at hX
    constructor
    · have := mul_nonneg hΛ.le hX.1
      linarith
    · exact (mul_le_mul_of_nonneg_left hX.2 hΛ.le).trans_lt hp.1.2
  · rw [uIcc_of_ge hneg] at hX
    constructor
    · exact hp.1.1.trans_le (mul_le_mul_of_nonneg_left hX.1 hΛ.le)
    · have := mul_nonpos_of_nonneg_of_nonpos hΛ.le hX.2
      linarith

theorem average_integral_reconstruct {Λ : ℝ} (hΛ : 0 < Λ)
    (b : ℝ → ℝ) (c : ℝ) {u B : ℝ × ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (AxisEvaluation.strip window 20))
    (havg : ∀ q ∈ AxisEvaluation.strip window 20,
      q.1 * B q = ∫ Y in (0 : ℝ)..q.1, u (Y, q.2))
    {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    p.1 * affineProfile b c Λ B p =
      ∫ X in (0 : ℝ)..p.1, affineProfile b c Λ u (X, p.2) := by
  have hi : IntervalIntegrable (fun X : ℝ => pullback Λ u (X, p.2))
      MeasureTheory.volume 0 p.1 := by
    apply ContinuousOn.intervalIntegrable
    exact (pullback_smooth hu Λ).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hx => domain_segment hΛ hp hx)
  have hchange := intervalIntegral.integral_comp_mul_left
    (fun Y : ℝ => u (Y, p.2)) hΛ.ne' (a := 0) (b := p.1)
  change p.1 * (b p.2 + c * B (rescalePoint Λ p)) =
    ∫ X in (0 : ℝ)..p.1, b p.2 + c * pullback Λ u (X, p.2)
  rw [intervalIntegral.integral_add intervalIntegrable_const (hi.const_mul c),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
  change _ = (p.1 - 0) * b p.2 + c * ∫ X in (0 : ℝ)..p.1, u (Λ * X, p.2)
  rw [hchange]
  simp only [mul_zero, smul_eq_mul, sub_zero]
  have hav := havg (rescalePoint Λ p) hp
  dsimp only [rescalePoint] at hav
  rw [← hav]
  dsimp [rescalePoint]
  field_simp

/-- Reconstruction preserves the full differential and integral system. -/
theorem reconstruct_solution {h j σ Λ : ℝ} {P0 a₀ : ℝ → ℝ}
    (hsmall : NaturalAxisRange.Parameters h j) (hΛ : 0 < Λ)
    (hP0 : ContDiff ℝ ∞ P0)
    (haSmooth : ContDiffOn ℝ ∞ a₀ (Ioo window.left window.right))
    (ha : ∀ η ∈ Ioo window.left window.right,
      HasDerivAt a₀ ((Λ * realGradient h j σ η) * a₀ η) η)
    {Φ u B P : ℝ × ℝ → ℝ}
    (hs : IsScaledSolution window (actualData h j σ P0) (1 / Λ) a₀ Φ u B P) :
    IsNaturalSolution h j Λ P0 a₀ (angularProfile a₀ Λ Φ)
      (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u)
      (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ B)
      (affineProfile P0 (1 / Λ) Λ P) := by
  refine {
    f_smooth := angularProfile_smooth haSmooth hs.phi_smooth Λ
    U_smooth := affineProfile_smooth (uStar_smooth j).contDiffOn hs.u_smooth (1 / Λ) Λ
    average_smooth := affineProfile_smooth (uStar_smooth j).contDiffOn hs.average_smooth (1 / Λ) Λ
    pressure_smooth := affineProfile_smooth hP0.contDiffOn hs.pressure_smooth (1 / Λ) Λ
    f_axis := ?_
    U_axis := ?_
    average_axis := ?_
    pressure_axis := ?_
    average_equation := ?_
    pressure_equation := ?_
    average_integral := fun p hp => average_integral_reconstruct hΛ (NaturalAxisData.U j)
      (1 / Λ) hs.u_smooth hs.average_integral hp
    pressure_integral := ?_
    angular_equation := fun p hp => angular_equation_reconstruct hsmall hΛ.ne' hs hp (ha p.2 hp.2)
    axial_equation := fun p hp => axial_equation_reconstruct hsmall hΛ.ne' hP0 hs hp
  }
  · intro η hη
    simp only [angularProfile, pullback, rescalePoint, mul_zero, hs.phi_axis η hη, mul_one]
  · intro η hη
    simp only [affineProfile, pullback, rescalePoint, mul_zero, hs.u_axis η hη, add_zero]
  · intro η hη
    simp only [affineProfile, pullback, rescalePoint, mul_zero, hs.average_axis η hη,
      hs.u_axis η hη, add_zero]
  · intro η hη
    simp only [affineProfile, pullback, rescalePoint, mul_zero, hs.pressure_axis η hη, add_zero]
  · intro p hp
    rw [affineProfile_partialY hs.average_smooth (NaturalAxisData.U j) (1 / Λ) Λ hp,
      one_div_mul_cancel hΛ.ne', one_mul]
    change NaturalAxisData.U j p.2 + (1 / Λ) * B (rescalePoint Λ p) +
      p.1 * partialY B (rescalePoint Λ p) =
        NaturalAxisData.U j p.2 + (1 / Λ) * u (rescalePoint Λ p)
    have he := hs.average_equation (rescalePoint Λ p) hp
    dsimp [rescalePoint] at he ⊢
    apply (mul_left_cancel₀ hΛ.ne')
    field_simp
    linear_combination he
  · intro p hp
    rw [affineProfile_partialY hs.pressure_smooth P0 (1 / Λ) Λ hp,
      one_div_mul_cancel hΛ.ne', one_mul, hs.pressure_equation (rescalePoint Λ p) hp]
    simp only [angularProfile, pullback, rescalePoint, mul_pow]
  · intro p hp
    change P0 p.2 + (1 / Λ) * P (rescalePoint Λ p) - P0 p.2 = _
    rw [add_sub_cancel_left, hs.pressure_integral (rescalePoint Λ p) hp]
    have he := intervalIntegral.integral_comp_mul_left
      (fun Y : ℝ => (a₀ p.2) ^ 2 * (Φ (Y, p.2)) ^ 2) hΛ.ne' (a := 0) (b := p.1)
    simpa only [angularProfile, pullback, rescalePoint, mul_zero, smul_eq_mul, mul_pow,
      one_div] using he.symm

theorem angularProfile_log_slope_at_four {Λ : ℝ} (hΛ : 0 < Λ)
    {a : ℝ → ℝ} {Φ : ℝ × ℝ → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip window 20))
    {η : ℝ} (hη : η ∈ Ioo window.left window.right)
    (ha : 0 < a η) (hval : 0 < Φ (4, η)) :
    -2 * (4 / Λ) * partialY (angularProfile a Λ Φ) (4 / Λ, η) /
        angularProfile a Λ Φ (4 / Λ, η) =
      -8 * partialY Φ (4, η) / Φ (4, η) := by
  have hrad : Λ * (4 / Λ) = 4 := by field_simp
  have hp : (4 / Λ, η) ∈ domain Λ := by
    change (Λ * (4 / Λ), η) ∈ AxisEvaluation.strip window 20
    rw [hrad]
    exact ⟨by norm_num, hη⟩
  rw [angularProfile_partialY hΦ a Λ hp]
  simp only [angularProfile, pullback, rescalePoint, hrad]
  field_simp ; ring

def profileErrorConstant {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) : ℝ :=
  errorConstant window d.coefficients.epsilon_pos (d.coefficients.elements .chi)
    d.coefficients.axisData d.amplitudeBound d.amplitudeBound_nonneg

/-- The functions and estimates obtained from one actual coefficient-space
fixed point. All unscaled functions are explicit expressions in these fields. -/
structure ProfileFamily {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (Λ C : ℝ) where
  phi : ℝ × ℝ → ℝ
  u : ℝ × ℝ → ℝ
  average : ℝ × ℝ → ℝ
  pressure : ℝ × ℝ → ℝ
  natural : IsNaturalSolution h j Λ P0 (realAmplitude h j σ Λ C)
    (angularProfile (realAmplitude h j σ Λ C) Λ phi)
    (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u)
    (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ average)
    (affineProfile P0 (1 / Λ) Λ pressure)
  mixed_error : UniformMixedError window d.coefficients.epsilon
    (profileErrorConstant d / (2 * Λ)) phi u
    (AxisEvaluation.profile window d.coefficients.epsilon
      (referenceCoefficients window d.coefficients.epsilon_pos
        (d.coefficients.elements .chi) d.coefficients.axisData).1)
    (AxisEvaluation.profile window d.coefficients.epsilon
      (referenceCoefficients window d.coefficients.epsilon_pos
        (d.coefficients.elements .chi) d.coefficients.axisData).2)
  positive : ∀ p ∈ domain Λ, 0 ≤ Λ * p.1 → Λ * p.1 ≤ 41 / 10 →
    0 < angularProfile (realAmplitude h j σ Λ C) Λ phi p
  slope : ∀ η ∈ Ioo window.left window.right, 99 / 100 ≤ NaturalAxisData.chi h j σ η →
    23 / 10 <
      -2 * (4 / Λ) * partialY (angularProfile (realAmplitude h j σ Λ C) Λ phi) (4 / Λ, η) /
        angularProfile (realAmplitude h j σ Λ C) Λ phi (4 / Λ, η)

def ProfileFamily.f {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : ProfileFamily d Λ C) : ℝ × ℝ → ℝ :=
  angularProfile (realAmplitude h j σ Λ C) Λ F.phi

def ProfileFamily.U {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : ProfileFamily d Λ C) : ℝ × ℝ → ℝ :=
  affineProfile (NaturalAxisData.U j) (1 / Λ) Λ F.u

def ProfileFamily.Ubar {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : ProfileFamily d Λ C) : ℝ × ℝ → ℝ :=
  affineProfile (NaturalAxisData.U j) (1 / Λ) Λ F.average

def ProfileFamily.Pi {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : ProfileFamily d Λ C) : ℝ × ℝ → ℝ :=
  affineProfile P0 (1 / Λ) Λ F.pressure

/-- The scale threshold is uniform over every normalization above the actual
compact-domain exponential threshold. -/
theorem exists_profileFamily {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hsmall : NaturalAxisRange.Parameters h j)
    (hσ : 0 < σ) (hP0 : ContDiff ℝ ∞ P0) :
    ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
      ∀ C : ℝ, d.normalizationThreshold Λ ≤ C → Nonempty (ProfileFamily d Λ C) := by
  have hchi : ∀ η ∈ window.interval,
      0 ≤ inputValue window d.coefficients.epsilon (d.coefficients.elements .chi) η ∧
        inputValue window d.coefficients.epsilon (d.coefficients.elements .chi) η ≤ 1 := by
    intro η hη
    rw [d.coefficients.value .chi hη]
    exact ⟨(NaturalAxisData.chi_bounds h j hσ η).1, (NaturalAxisData.chi_bounds h j hσ η).2.le⟩
  obtain ⟨Λ₀, hΛ₀, hexists⟩ := AxisReference.exists_positive_scaled_profiles window
    d.coefficients.epsilon_pos (d.coefficients.elements .chi) d.coefficients.axisData
    d.coefficients.compatible hchi d.amplitudeBound d.amplitudeBound_nonneg
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ C hC
  have hΛpos : 0 < Λ := hΛ₀.trans_le hΛ
  have hCpos : 0 < C := (Real.exp_pos _).trans_le hC
  obtain ⟨a, ha, harad, havalue⟩ := d.uniformAmplitude Λ hΛpos.le C hC
  obtain ⟨Φ, u, B, P, hs, herr, hpositive, hslope⟩ := hexists Λ hΛ a ha harad
  have hs' := materialize_scaled d.coefficients a havalue hs
  refine ⟨{
    phi := Φ
    u := u
    average := B
    pressure := P
    natural := reconstruct_solution hsmall hΛpos hP0 (amplitude_smooth d Λ C)
      (fun η hη => d.realAmplitude_hasDerivAt Λ C ⟨hη.1.le, hη.2.le⟩) hs'
    mixed_error := herr
    positive := ?_
    slope := ?_
  }⟩
  · intro p hp hY0 hY1
    exact mul_pos (realAmplitude_pos h j σ Λ hCpos p.2)
      (lt_trans (by norm_num) (hpositive (Λ * p.1) ⟨hY0, hY1⟩ p.2 hp.2))
  · intro η hη hchiη
    rw [angularProfile_log_slope_at_four hΛpos hs.phi_smooth hη
      (realAmplitude_pos h j σ Λ hCpos η)
      (lt_trans (by norm_num) (hpositive 4 (by norm_num) η hη))]
    apply hslope η hη
    rw [d.coefficients.value .chi ⟨hη.1.le, hη.2.le⟩]
    exact hchiη

/-- The pressure integral and ideal prefix yield actual unscaled natural
profiles after selecting the cutoff and common analytic coefficient radius. -/
theorem ideal_prefix_profileFamily {h j : ℝ}
    (hsmall : NaturalAxisRange.Parameters h j)
    {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ δ σ : ℝ, 0 < δ ∧ 0 < σ ∧
      (∀ η ∈ Icc (-1 : ℝ) 1,
        |NaturalAxisData.Z h j (PressureDatum.pressure g a) η| ≤ δ →
          99 / 100 < NaturalAxisData.chi h j σ η) ∧
      ∃ d : AnalyticInputs h j σ (PressureDatum.pressure g a),
        ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
          ∀ C : ℝ, d.normalizationThreshold Λ ≤ C → Nonempty (ProfileFamily d Λ C) := by
  obtain ⟨δ, σ, hδ, hσ, hcut, ⟨d⟩⟩ :=
    ideal_prefix_analytic_inputs hsmall hp hB hg ha
  refine ⟨δ, σ, hδ, hσ, hcut, d, ?_⟩
  exact exists_profileFamily d hsmall hσ (PressureDatum.pressure_contDiff hp)

/-- A direct existence theorem for the unscaled real functions. The cutoff,
analytic input family, large scale, and normalization are all constructed
from the stated pressure assumptions. -/
theorem exists_natural_profiles {h j : ℝ}
    (hsmall : NaturalAxisRange.Parameters h j)
    {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ δ σ Λ C : ℝ, 0 < δ ∧ 0 < σ ∧ 0 < Λ ∧ 0 < C ∧
      ∃ f U V Pr : ℝ × ℝ → ℝ,
        IsNaturalSolution h j Λ (PressureDatum.pressure g a)
          (realAmplitude h j σ Λ C) f U V Pr ∧
        (∀ p ∈ domain Λ, 0 ≤ Λ * p.1 → Λ * p.1 ≤ 41 / 10 → 0 < f p) ∧
        (∀ η ∈ Icc (-1 : ℝ) 1,
          |NaturalAxisData.Z h j (PressureDatum.pressure g a) η| ≤ δ →
            23 / 10 < -2 * (4 / Λ) * partialY f (4 / Λ, η) / f (4 / Λ, η)) := by
  obtain ⟨δ, σ, hδ, hσ, hcut, d, Λ, hΛ, hexists⟩ :=
    ideal_prefix_profileFamily hsmall hp hB hg ha
  let C := d.normalizationThreshold Λ
  obtain ⟨F⟩ := hexists Λ le_rfl C le_rfl
  refine ⟨δ, σ, Λ, C, hδ, hσ, hΛ, Real.exp_pos _,
    F.f, F.U, F.Ubar, F.Pi, F.natural, F.positive, ?_⟩
  intro η hη hZ
  exact F.slope η (original_interval_interior hη) (hcut η hη hZ).le

end NavierStokes.NaturalProfile

end

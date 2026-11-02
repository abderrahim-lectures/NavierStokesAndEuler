import NavierStokes.AxisContraction
import NavierStokes.AxisEvaluation
import NavierStokes.AxisOperators
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

/-!
# From the coefficient fixed point to actual natural-axis profiles

This bridge uses ordinary real derivatives of the evaluated functions. The
fixed input data must still be supplied as members of the coefficient space;
their construction from the outgoing schedule is a separate obligation.
-/
/-! Merged from `NavierStokes.AxisEvaluationAlgebra` (in a section, so its `open`s cannot leak). -/
section
/-!
# Actual profile equations for the coefficient operators

The identities here combine the convergent, smooth evaluation of `AxisSpace`
with the exact compatible coefficient operators of `AxisOperators`.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff BigOperators
open NavierStokes.AxisCoefficientSpace NavierStokes.AxisWeightEstimates
open NavierStokes.AxisEvaluation NavierStokes.AxisOperators

namespace NavierStokes.AxisEvaluationAlgebra

theorem powerSeries_mul {f g : ℕ → ℝ} {Y : ℝ}
    (hf : Summable (fun n => ‖Y ^ n * f n‖))
    (hg : Summable (fun n => ‖Y ^ n * g n‖)) :
    (∑' n : ℕ, Y ^ n * f n) * (∑' n : ℕ, Y ^ n * g n) =
      ∑' n : ℕ, Y ^ n * ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2 := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
  apply tsum_congr
  intro n
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [← Finset.mem_antidiagonal.mp hij, pow_add]
  ring

theorem profile_series_norm_summable (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) :
    Summable (fun n => ‖Y ^ n * coefficient I (weight ε) A n η‖) := by
  simpa only [Real.norm_eq_abs] using (profile_hasSum I hε A (p := (Y, η)) hY).summable.abs

/-- Multiplication in the coefficient space evaluates to pointwise multiplication. -/
theorem profile_product (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A B : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) (hη : η ∈ I.interval) :
    profile I ε (product I hε A B) (Y, η) =
      profile I ε A (Y, η) * profile I ε B (Y, η) := by
  rw [profile, profile, profile, powerSeries_mul
    (profile_series_norm_summable I hε A hY) (profile_series_norm_summable I hε B hY)]
  apply tsum_congr
  intro n
  rw [coefficient_product I hε A B n hη]

theorem profile_axis (I : Window) (ε : ℝ) (A : AxisSpace I ε) (η : ℝ) :
    profile I ε A (0, η) = coefficient I (weight ε) A 0 η := by
  unfold profile
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]


theorem profile_deriv_eta (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    deriv (fun x => profile I ε A (Y, x)) η = mixedSeries I ε A 0 1 (Y, η) := by
  have hd := mixedSeries_hasDerivAt_eta I hε A 0 0 hY hη
  rw [mixedSeries_zero] at hd
  exact hd.deriv


def radialValue (I : Window) (ε : ℝ) (r : ℕ) (A : AxisSpace I ε) (p : ℝ × ℝ) : ℝ :=
  p.1 * mixedSeries I ε A 2 0 p + (r : ℝ) * mixedSeries I ε A 1 0 p


theorem polynomialJet_radial (r n : ℕ) (Y : ℝ) :
    Y * polynomialJet (n + 1) 2 Y + (r : ℝ) * polynomialJet (n + 1) 1 Y =
      radialDivisor r n * Y ^ n := by
  cases n with
  | zero => simp [polynomialJet, radialDivisor, Nat.descFactorial_succ]
  | succ n =>
      have he : n + 1 + 1 - 2 = n := by omega
      simp only [polynomialJet, Nat.descFactorial_succ, Nat.descFactorial_zero,
        Nat.sub_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      simp only [Nat.add_sub_cancel, he]
      unfold radialDivisor
      push_cast
      rw [pow_succ]
      ring

/-- Coefficient formula for the actual regular radial differential operator. -/
theorem radialValue_series (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) :
    radialValue I ε r A (Y, η) =
      ∑' n : ℕ, radialDivisor r n * Y ^ n * coefficient I (weight ε) A (n + 1) η := by
  have h₂ := mixedSeries_summable I hε A 2 0 (p := (Y, η)) hY
  have h₁ := mixedSeries_summable I hε A 1 0 (p := (Y, η)) hY
  have hs := (h₂.mul_left Y).add (h₁.mul_left (r : ℝ))
  calc
    _ = ∑' n : ℕ, (Y * term I ε A 2 0 n (Y, η) +
        (r : ℝ) * term I ε A 1 0 n (Y, η)) := by
      rw [Summable.tsum_add (h₂.mul_left Y) (h₁.mul_left (r : ℝ)), tsum_mul_left, tsum_mul_left]
      rfl
    _ = ∑' n : ℕ, (Y * term I ε A 2 0 (n + 1) (Y, η) +
        (r : ℝ) * term I ε A 1 0 (n + 1) (Y, η)) := by
      rw [hs.tsum_eq_zero_add]
      simp [term, polynomialJet]
    _ = _ := by
      apply tsum_congr
      intro n
      calc
        _ = (Y * polynomialJet (n + 1) 2 Y + (r : ℝ) * polynomialJet (n + 1) 1 Y) *
            coefficient I (weight ε) A (n + 1) η := by unfold term coefficient; ring
        _ = _ := by rw [polynomialJet_radial]

/-- The regular inverse is a genuine right inverse on evaluated profiles. -/
theorem regularInverse_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A : AxisSpace I ε) {Y η : ℝ}
    (hY : |Y| < 20) (hη : η ∈ I.interval) :
    radialValue I ε r (regularInverse I hε r hr A) (Y, η) = profile I ε A (Y, η) := by
  rw [radialValue_series I hε r _ hY]
  unfold profile
  apply tsum_congr
  intro n
  change radialDivisor r n * Y ^ n * inputJet I ε (regularInverse I hε r hr A) (n + 1) 0 η = _
  rw [jet_regularInverse_succ I hε r hr A n 0 hη]
  change radialDivisor r n * Y ^ n * (coefficient I (weight ε) A n η / radialDivisor r n) = _
  field_simp [(radialDivisor_pos hr n).ne']

theorem regularInverse_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (regularInverse I hε r hr A) (0, η) = 0 := by
  rw [profile_axis]
  exact jet_regularInverse_zero I hε r hr A 0 hη

theorem derivativeSeries (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) :
    mixedSeries I ε A 1 0 (Y, η) =
      ∑' n : ℕ, ((n : ℝ) + 1) * Y ^ n * coefficient I (weight ε) A (n + 1) η := by
  have hs := mixedSeries_summable I hε A 1 0 (p := (Y, η)) hY
  unfold mixedSeries
  rw [hs.tsum_eq_zero_add]
  simp only [term, polynomialJet, Nat.zero_descFactorial_succ, Nat.cast_zero,
    zero_mul, zero_add]
  apply tsum_congr
  intro n
  simp [coefficient]

theorem jet_average_eval (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    inputJet I ε (average I hε A) n m η = inputJet I ε A n m η / ((n : ℝ) + 1) := by
  change inputJet I ε (linearLift I hε (averageData I hε) A) n m η = _
  rw [jet_linearLift I hε (averageData I hε) A n m hη]
  change (1 / ((n : ℝ) + 1)) * inputJet I ε A n (0 + m) η = _
  rw [Nat.zero_add]
  ring

theorem jet_primitive_eval (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    inputJet I ε (primitive I hε A) n m η = primitiveScale n * inputJet I ε A n.pred m η := by
  change inputJet I ε (linearLift I hε (primitiveData I hε) A) n m η = _
  rw [jet_linearLift I hε (primitiveData I hε) A n m hη]
  change primitiveScale n * inputJet I ε A n.pred (0 + m) η = _
  rw [Nat.zero_add]

theorem jet_parameterPrimitive_eval (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    inputJet I ε (parameterPrimitive I hε A) n m η =
      primitiveScale n * inputJet I ε A n.pred (1 + m) η := by
  change inputJet I ε (linearLift I hε (parameterPrimitiveData I hε) A) n m η = _
  exact jet_linearLift I hε (parameterPrimitiveData I hε) A n m hη

theorem jet_mulY_eval (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    inputJet I ε (mulY I hε A) n m η = multiplyYScale n * inputJet I ε A n.pred m η := by
  change inputJet I ε (linearLift I hε (multiplyYData I hε) A) n m η = _
  rw [jet_linearLift I hε (multiplyYData I hε) A n m hη]
  change multiplyYScale n * inputJet I ε A n.pred (0 + m) η = _
  rw [Nat.zero_add]

theorem primitive_Y_value (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) (hη : η ∈ I.interval) :
    mixedSeries I ε (primitive I hε A) 1 0 (Y, η) = profile I ε A (Y, η) := by
  rw [derivativeSeries I hε _ hY]
  unfold profile
  apply tsum_congr
  intro n
  change ((n : ℝ) + 1) * Y ^ n * inputJet I ε (primitive I hε A) (n + 1) 0 η = _
  rw [jet_primitive_eval I hε A (n + 1) 0 hη]
  simp only [primitiveScale, Nat.pred_succ]
  change ((n : ℝ) + 1) * Y ^ n * (1 / ((n : ℝ) + 1) * coefficient I (weight ε) A n η) = _
  field_simp

theorem primitive_hasDerivAt (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    HasDerivAt (fun y => profile I ε (primitive I hε A) (y, η)) (profile I ε A (Y, η)) Y := by
  have hd := mixedSeries_hasDerivAt_Y I hε (primitive I hε A) 0 0 hY hη
  rw [mixedSeries_zero, primitive_Y_value I hε A (abs_lt.mpr hY) ⟨hη.1.le, hη.2.le⟩] at hd
  exact hd

theorem primitive_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (primitive I hε A) (0, η) = 0 := by
  rw [profile_axis]
  change inputJet I ε (primitive I hε A) 0 0 η = _
  rw [jet_primitive_eval I hε A 0 0 hη]
  simp [primitiveScale]

theorem profile_mulY (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) (hη : η ∈ I.interval) :
    profile I ε (mulY I hε A) (Y, η) = Y * profile I ε A (Y, η) := by
  have hs := (profile_hasSum I hε (mulY I hε A) (p := (Y, η)) hY).summable
  unfold profile
  rw [hs.tsum_eq_zero_add]
  have hzero : coefficient I (weight ε) (mulY I hε A) 0 η = 0 := by
    change inputJet I ε (mulY I hε A) 0 0 η = _
    rw [jet_mulY_eval I hε A 0 0 hη]
    simp [multiplyYScale]
  rw [hzero, mul_zero, zero_add, ← tsum_mul_left]
  apply tsum_congr
  intro n
  change Y ^ (n + 1) * inputJet I ε (mulY I hε A) (n + 1) 0 η = _
  rw [jet_mulY_eval I hε A (n + 1) 0 hη]
  simp only [multiplyYScale, Nat.pred_succ, one_mul, pow_succ]
  change Y ^ n * Y * coefficient I (weight ε) A n η = _
  ring

theorem primitive_eq_mulY_average (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) : primitive I hε A = mulY I hε (average I hε A) := by
  apply coefficient_ext I (weight ε) (fun n m => (weight_pos hε n m).ne')
  intro n η hη
  change inputJet I ε (primitive I hε A) n 0 η = inputJet I ε (mulY I hε (average I hε A)) n 0 η
  rw [jet_primitive_eval I hε A n 0 hη, jet_mulY_eval I hε (average I hε A) n 0 hη,
    jet_average_eval I hε A n.pred 0 hη]
  cases n <;> simp [primitiveScale, multiplyYScale, div_eq_mul_inv, mul_comm]

theorem average_times_Y (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) (hη : η ∈ I.interval) :
    Y * profile I ε (average I hε A) (Y, η) = profile I ε (primitive I hε A) (Y, η) := by
  rw [primitive_eq_mulY_average, profile_mulY I hε _ hY hη]

theorem parameterSeries (I : Window) (ε : ℝ) (A : AxisSpace I ε)
    (m : ℕ) (Y η : ℝ) :
    mixedSeries I ε A 0 m (Y, η) = ∑' n : ℕ, Y ^ n * inputJet I ε A n m η := by
  simp only [mixedSeries, term, polynomialJet, Nat.descFactorial_zero, Nat.cast_one,
    Nat.sub_zero, one_mul, inputJet]

theorem parameterSeries_norm_summable (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (m : ℕ) {Y η : ℝ} (hY : |Y| < 20) :
    Summable (fun n : ℕ => ‖Y ^ n * inputJet I ε A n m η‖) := by
  simpa only [term, polynomialJet, Nat.descFactorial_zero, Nat.cast_one, Nat.sub_zero,
    one_mul, Prod.fst, Prod.snd, inputJet, Real.norm_eq_abs] using
    (mixedSeries_summable I hε A 0 m (p := (Y, η)) hY).abs

theorem polynomialJet_dot (n : ℕ) (Y : ℝ) :
    Y * polynomialJet n 1 Y = (n : ℝ) * Y ^ n := by
  cases n with
  | zero => simp [polynomialJet]
  | succ n =>
      simp only [polynomialJet, Nat.descFactorial_one, Nat.add_sub_cancel,
        Nat.cast_add, Nat.cast_one, pow_succ]
      ring

theorem dotSeries (I : Window) (ε : ℝ) (A : AxisSpace I ε) (Y η : ℝ) :
    Y * mixedSeries I ε A 1 0 (Y, η) =
      ∑' n : ℕ, Y ^ n * ((n : ℝ) * inputJet I ε A n 0 η) := by
  rw [mixedSeries, ← tsum_mul_left]
  apply tsum_congr
  intro n
  change Y * (polynomialJet n 1 Y * inputJet I ε A n 0 η) = _
  rw [← mul_assoc, polynomialJet_dot]
  ring

theorem dotSeries_norm_summable (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) :
    Summable (fun n : ℕ => ‖Y ^ n * ((n : ℝ) * inputJet I ε A n 0 η)‖) := by
  have hs := ((mixedSeries_summable I hε A 1 0 (p := (Y, η)) hY).mul_left Y).abs
  convert! hs using 1
  funext n
  change |Y ^ n * ((n : ℝ) * inputJet I ε A n 0 η)| =
    |Y * (polynomialJet n 1 Y * inputJet I ε A n 0 η)|
  have he : Y * (polynomialJet n 1 Y * inputJet I ε A n 0 η) =
      Y ^ n * ((n : ℝ) * inputJet I ε A n 0 η) := by
    rw [← mul_assoc, polynomialJet_dot]
    ring
  rw [he]

theorem radialValue_of_convolution (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (C : AxisSpace I ε) (f g : ℕ → ℝ) {Y η : ℝ} (hY : |Y| < 20)
    (hf : Summable (fun n => ‖Y ^ n * f n‖))
    (hg : Summable (fun n => ‖Y ^ n * g n‖))
    (hC : ∀ n, radialDivisor r n * inputJet I ε C (n + 1) 0 η =
      ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2) :
    radialValue I ε r C (Y, η) = (∑' n, Y ^ n * f n) * (∑' n, Y ^ n * g n) := by
  rw [radialValue_series I hε r C hY, powerSeries_mul hf hg]
  apply tsum_congr
  intro n
  change radialDivisor r n * Y ^ n * inputJet I ε C (n + 1) 0 η = _
  calc
    _ = Y ^ n * (radialDivisor r n * inputJet I ε C (n + 1) 0 η) := by ring
    _ = _ := by rw [hC n]

theorem differentialFamily_cancel (I : Window) (ε : ℝ) (r p : ℕ) (hr : 1 ≤ r)
    (d : ℕ → ℝ) (A B : AxisSpace I ε) (n : ℕ) (η : ℝ) :
    radialDivisor r n * differentialFamily I ε r p d A B (n + 1) 0 η =
      ∑ ij ∈ Finset.antidiagonal n, inputJet I ε A ij.1 p η *
        (d ij.2 * inputJet I ε B ij.2 0 η) := by
  simp only [differentialFamily, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
    Nat.choose_zero_right, Nat.cast_one, mul_one,
    Nat.add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  field_simp [(radialDivisor_pos hr n).ne']

/-- The parameter derivative is on the first factor and the radial dot is
on the second factor, as required by the manuscript's mixed estimate. -/
theorem inverseMixed_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {Y η : ℝ}
    (hY : |Y| < 20) (hη : η ∈ I.interval) :
    radialValue I ε r (inverseMixed I hε r hr A B) (Y, η) =
      mixedSeries I ε A 0 1 (Y, η) * (Y * mixedSeries I ε B 1 0 (Y, η)) := by
  rw [parameterSeries, dotSeries]
  apply radialValue_of_convolution I hε r _ _ _ hY
    (parameterSeries_norm_summable I hε A 1 hY) (dotSeries_norm_summable I hε B hY)
  intro n
  rw [jet_inverseMixed I hε r hr A B (n + 1) 0 hη]
  exact differentialFamily_cancel I ε r 1 hr (fun j => (j : ℝ)) A B n η

theorem inverseParamProduct_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {Y η : ℝ}
    (hY : |Y| < 20) (hη : η ∈ I.interval) :
    radialValue I ε r (inverseParamProduct I hε r hr A B) (Y, η) =
      mixedSeries I ε A 0 1 (Y, η) * profile I ε B (Y, η) := by
  rw [parameterSeries]
  change radialValue I ε r (inverseParamProduct I hε r hr A B) (Y, η) =
    (∑' n, Y ^ n * inputJet I ε A n 1 η) * (∑' n, Y ^ n * inputJet I ε B n 0 η)
  apply radialValue_of_convolution I hε r _ _ _ hY
    (parameterSeries_norm_summable I hε A 1 hY) (parameterSeries_norm_summable I hε B 0 hY)
  intro n
  rw [jet_inverseParamProduct I hε r hr A B (n + 1) 0 hη]
  simpa only [one_mul] using differentialFamily_cancel I ε r 1 hr (fun _ => 1) A B n η

theorem inverseDotProduct_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {Y η : ℝ}
    (hY : |Y| < 20) (hη : η ∈ I.interval) :
    radialValue I ε r (inverseDotProduct I hε r hr A B) (Y, η) =
      profile I ε A (Y, η) * (Y * mixedSeries I ε B 1 0 (Y, η)) := by
  rw [dotSeries]
  change radialValue I ε r (inverseDotProduct I hε r hr A B) (Y, η) =
    (∑' n : ℕ, Y ^ n * inputJet I ε A n 0 η) *
      (∑' n : ℕ, Y ^ n * ((n : ℝ) * inputJet I ε B n 0 η))
  apply radialValue_of_convolution I hε r _ _ _ hY
    (parameterSeries_norm_summable I hε A 0 hY) (dotSeries_norm_summable I hε B hY)
  intro n
  rw [jet_inverseDotProduct I hε r hr A B (n + 1) 0 hη]
  exact differentialFamily_cancel I ε r 0 hr (fun j => (j : ℝ)) A B n η

theorem inverseMixed_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (inverseMixed I hε r hr A B) (0, η) = 0 := by
  rw [profile_axis]
  exact jet_inverseMixed I hε r hr A B 0 0 hη

theorem inverseParamProduct_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (inverseParamProduct I hε r hr A B) (0, η) = 0 := by
  rw [profile_axis]
  exact jet_inverseParamProduct I hε r hr A B 0 0 hη

theorem inverseDotProduct_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (inverseDotProduct I hε r hr A B) (0, η) = 0 := by
  rw [profile_axis]
  exact jet_inverseDotProduct I hε r hr A B 0 0 hη

theorem parameterPrimitive_eta_value (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (Y : ℝ) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (parameterPrimitive I hε A) (Y, η) =
      mixedSeries I ε (primitive I hε A) 0 1 (Y, η) := by
  rw [parameterSeries]
  unfold profile
  apply tsum_congr
  intro n
  change Y ^ n * inputJet I ε (parameterPrimitive I hε A) n 0 η = _
  rw [jet_parameterPrimitive_eval I hε A n 0 hη, jet_primitive_eval I hε A n 1 hη]

/-- The pressure parameter primitive is the actual parameter derivative
of the radial primitive. -/
theorem parameterPrimitive_eq_deriv_eta (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    profile I ε (parameterPrimitive I hε A) (Y, η) =
      deriv (fun x => profile I ε (primitive I hε A) (Y, x)) η := by
  rw [profile_deriv_eta I hε _ hY hη]
  exact parameterPrimitive_eta_value I hε A Y ⟨hη.1.le, hη.2.le⟩




theorem radial_segment_mem {Y y : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hy : y ∈ uIcc (0 : ℝ) Y) : y ∈ Ioo (-20 : ℝ) 20 := by
  rcases le_total (0 : ℝ) Y with h | h
  · rw [uIcc_of_le h] at hy
    exact ⟨lt_of_lt_of_le (by norm_num) hy.1, hy.2.trans_lt hY.2⟩
  · rw [uIcc_of_ge h] at hy
    exact ⟨hY.1.trans_le hy.1, lt_of_le_of_lt hy.2 (by norm_num)⟩

/-- The coefficient primitive equals the ordinary oriented integral. -/
theorem primitive_integral (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    profile I ε (primitive I hε A) (Y, η) =
      ∫ y in (0 : ℝ)..Y, profile I ε A (y, η) := by
  have hcont : ContinuousOn (fun y => profile I ε A (y, η)) (uIcc (0 : ℝ) Y) := by
    intro y hy
    have hd := mixedSeries_hasDerivAt_Y I hε A 0 0 (radial_segment_mem hY hy) hη
    rw [mixedSeries_zero] at hd
    exact hd.continuousAt.continuousWithinAt
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => primitive_hasDerivAt I hε A (radial_segment_mem hY hy) hη)
    hcont.intervalIntegrable
  rw [primitive_axis_zero I hε A ⟨hη.1.le, hη.2.le⟩, sub_zero] at hi
  exact hi.symm

theorem average_integral (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    Y * profile I ε (average I hε A) (Y, η) =
      ∫ y in (0 : ℝ)..Y, profile I ε A (y, η) := by
  rw [average_times_Y I hε A (abs_lt.mpr hY) ⟨hη.1.le, hη.2.le⟩]
  exact primitive_integral I hε A hY hη



theorem average_axis (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (average I hε A) (0, η) = profile I ε A (0, η) := by
  rw [profile_axis, profile_axis]
  change inputJet I ε (average I hε A) 0 0 η = inputJet I ε A 0 0 η
  rw [jet_average_eval I hε A 0 0 hη]
  norm_num

theorem average_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) (hη : η ∈ I.interval) :
    profile I ε (average I hε A) (Y, η) +
      Y * mixedSeries I ε (average I hε A) 1 0 (Y, η) = profile I ε A (Y, η) := by
  have hs := (parameterSeries_norm_summable I hε (average I hε A) 0 (η := η) hY).of_norm
  have hd := (dotSeries_norm_summable I hε (average I hε A) (η := η) hY).of_norm
  change (∑' n : ℕ, Y ^ n * inputJet I ε (average I hε A) n 0 η) +
    Y * mixedSeries I ε (average I hε A) 1 0 (Y, η) =
    ∑' n : ℕ, Y ^ n * inputJet I ε A n 0 η
  rw [dotSeries, ← hs.tsum_add hd]
  apply tsum_congr
  intro n
  rw [jet_average_eval I hε A n 0 hη]
  field_simp ; ring

end NavierStokes.AxisEvaluationAlgebra
end


noncomputable section

namespace NavierStokes.NaturalAxisBridge

private local instance (I : AxisCoefficientSpace.Window) (ε : ℝ) :
    NormedAddCommGroup (AxisCoefficientSpace.AxisSpace I ε) := inferInstance
private local instance (I : AxisCoefficientSpace.Window) (ε : ℝ) :
    NormedSpace ℝ (AxisCoefficientSpace.AxisSpace I ε) := inferInstance

open Set Filter
open scoped Topology ContDiff
open AxisCoefficientSpace AxisWeightEstimates

/-- Ordinary radial partial derivative of an actual function. -/
def partialY (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun Y => F (Y, p.2)) p.1

/-- Ordinary parameter partial derivative of an actual function. -/
def partialEta (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun η => F (p.1, η)) p.2

/-- Actual mixed derivative, with the order used by the manuscript's jet bounds. -/
def mixedDerivative (k m : ℕ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  iteratedDeriv m (fun η => iteratedDeriv k (fun Y => F (Y, η)) p.1) p.2

/-- The singular radial differential expression, evaluated without division by `Y`. -/
def radialDifferential (r : ℕ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * iteratedDeriv 2 (fun Y => F (Y, p.2)) p.1 + (r : ℝ) * partialY F p

/-- The same expression in terms of the rigorously differentiated sums. -/
def radialEvaluation (I : Window) (ε : ℝ) (r : ℕ) (A : AxisSpace I ε) (p : ℝ × ℝ) : ℝ :=
  p.1 * AxisEvaluation.mixedSeries I ε A 2 0 p +
    (r : ℝ) * AxisEvaluation.mixedSeries I ε A 1 0 p

theorem partialY_profile (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    partialY (AxisEvaluation.profile I ε A) p = AxisEvaluation.mixedSeries I ε A 1 0 p := by
  simpa only [partialY, AxisEvaluation.mixedSeries_zero] using
    (AxisEvaluation.mixedSeries_hasDerivAt_Y I hε A 0 0 hp.1 hp.2).deriv

theorem partialEta_profile (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    partialEta (AxisEvaluation.profile I ε A) p = AxisEvaluation.mixedSeries I ε A 0 1 p := by
  simpa only [partialEta, AxisEvaluation.mixedSeries_zero] using
    (AxisEvaluation.mixedSeries_hasDerivAt_eta I hε A 0 0 hp.1 hp.2).deriv


theorem radialEvaluation_eq (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (A : AxisSpace I ε) {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε r A p = radialDifferential r (AxisEvaluation.profile I ε A) p := by
  have h2 := AxisEvaluation.iteratedDeriv_Y I hε A 0 0 2 hp.1 hp.2
  simp only [AxisEvaluation.mixedSeries_zero, Nat.zero_add] at h2
  rw [radialEvaluation, radialDifferential, partialY_profile I hε A hp, h2]

theorem profile_add (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A B : AxisSpace I ε) {p : ℝ × ℝ} (hp : |p.1| < 20) :
    AxisEvaluation.profile I ε (A + B) p =
      AxisEvaluation.profile I ε A p + AxisEvaluation.profile I ε B p := by
  simpa only [AxisEvaluation.mixedSeries_zero] using
    AxisEvaluation.mixedSeries_add I hε A B 0 0 hp

theorem profile_smul (I : Window) (ε c : ℝ) (A : AxisSpace I ε) (p : ℝ × ℝ) :
    AxisEvaluation.profile I ε (c • A) p = c * AxisEvaluation.profile I ε A p := by
  simpa only [AxisEvaluation.mixedSeries_zero] using
    AxisEvaluation.mixedSeries_smul I ε c A 0 0 p

theorem profile_sub (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A B : AxisSpace I ε) {p : ℝ × ℝ} (hp : |p.1| < 20) :
    AxisEvaluation.profile I ε (A - B) p =
      AxisEvaluation.profile I ε A p - AxisEvaluation.profile I ε B p := by
  simpa only [AxisEvaluation.mixedSeries_zero] using
    AxisEvaluation.mixedSeries_sub I hε A B 0 0 hp

theorem profile_zero (I : Window) (ε : ℝ) (p : ℝ × ℝ) :
    AxisEvaluation.profile I ε (0 : AxisSpace I ε) p = 0 := by
  simp [AxisEvaluation.profile, coefficient]

theorem radialEvaluation_add (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (A B : AxisSpace I ε) {p : ℝ × ℝ} (hp : |p.1| < 20) :
    radialEvaluation I ε r (A + B) p =
      radialEvaluation I ε r A p + radialEvaluation I ε r B p := by
  simp only [radialEvaluation, AxisEvaluation.mixedSeries_add I hε A B _ _ hp]
  ring

theorem radialEvaluation_sub (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (A B : AxisSpace I ε) {p : ℝ × ℝ} (hp : |p.1| < 20) :
    radialEvaluation I ε r (A - B) p =
      radialEvaluation I ε r A p - radialEvaluation I ε r B p := by
  simp only [radialEvaluation, AxisEvaluation.mixedSeries_sub I hε A B _ _ hp]
  ring

theorem radialEvaluation_smul (I : Window) (ε c : ℝ)
    (r : ℕ) (A : AxisSpace I ε) (p : ℝ × ℝ) :
    radialEvaluation I ε r (c • A) p = c * radialEvaluation I ε r A p := by
  simp only [radialEvaluation, AxisEvaluation.mixedSeries_smul]
  ring

/-- Fixed axis data have radial degree zero; parameter dependence remains unrestricted. -/
def RadiallyConstant (I : Window) (ε : ℝ) (A : AxisSpace I ε) : Prop :=
  ∀ n : ℕ, n ≠ 0 → ∀ η : ℝ, η ∈ I.interval → coefficient I (weight ε) A n η = 0

theorem profile_radiallyConstant (I : Window) (ε : ℝ) (A : AxisSpace I ε)
    (hA : RadiallyConstant I ε A) (Y : ℝ) {η : ℝ} (hη : η ∈ I.interval) :
    AxisEvaluation.profile I ε A (Y, η) = coefficient I (weight ε) A 0 η := by
  unfold AxisEvaluation.profile
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp only [hA n hn η hη, mul_zero]

theorem radialEvaluation_constant (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (A : AxisSpace I ε) (hA : RadiallyConstant I ε A)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε r A p = 0 := by
  rw [radialEvaluation_eq I hε r A hp]
  have hfun : (fun Y => AxisEvaluation.profile I ε A (Y, p.2)) =
      fun _ : ℝ => coefficient I (weight ε) A 0 p.2 := by
    funext Y
    exact profile_radiallyConstant I ε A hA Y ⟨hp.2.1.le, hp.2.2.le⟩
  simp only [radialDifferential, partialY, hfun]
  norm_num [iteratedDeriv_succ, iteratedDeriv_zero]

theorem coefficient_product_constant (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A B : AxisSpace I ε) (hA : RadiallyConstant I ε A)
    (n : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    coefficient I (weight ε) (AxisOperators.product I hε A B) n η =
      coefficient I (weight ε) A 0 η * coefficient I (weight ε) B n η := by
  classical
  rw [AxisOperators.coefficient_product I hε A B n hη]
  apply Finset.sum_eq_single (0, n)
  · intro ij hij hne
    have hi : ij.1 ≠ 0 := by
      intro hi
      have hs := Finset.mem_antidiagonal.mp hij
      apply hne
      apply Prod.ext
      · exact hi
      · simpa only [hi, zero_add] using hs
    simp only [hA ij.1 hi η hη, zero_mul]
  · simp

/-- A fixed parameter multiplier commutes with the radial differential expression. -/
theorem radialEvaluation_product_constant (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (A B : AxisSpace I ε) (hA : RadiallyConstant I ε A)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε r (AxisOperators.product I hε A B) p =
      AxisEvaluation.profile I ε A p * radialEvaluation I ε r B p := by
  have hη : p.2 ∈ I.interval := ⟨hp.2.1.le, hp.2.2.le⟩
  have hY : |p.1| < 20 := abs_lt.mpr hp.1
  change AxisEvaluationAlgebra.radialValue I ε r (AxisOperators.product I hε A B) p =
    AxisEvaluation.profile I ε A p * AxisEvaluationAlgebra.radialValue I ε r B p
  rw [AxisEvaluationAlgebra.radialValue_series I hε r _ hY,
    AxisEvaluationAlgebra.radialValue_series I hε r _ hY,
    profile_radiallyConstant I ε A hA p.1 hη, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [coefficient_product_constant I hε A B hA (n + 1) hη]
  ring

theorem profile_neg (I : Window) (ε : ℝ) (A : AxisSpace I ε) (p : ℝ × ℝ) :
    AxisEvaluation.profile I ε (-A) p = -AxisEvaluation.profile I ε A p := by
  simpa only [neg_one_smul, neg_one_mul] using profile_smul I ε (-1) A p

theorem radialEvaluation_regularInverse (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A : AxisSpace I ε)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε r (AxisOperators.regularInverse I hε r hr A) p =
      AxisEvaluation.profile I ε A p :=
  AxisEvaluationAlgebra.regularInverse_equation I hε r hr A
    (abs_lt.mpr hp.1) ⟨hp.2.1.le, hp.2.2.le⟩

theorem radialEvaluation_param (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε r (AxisOperators.inverseParamProduct I hε r hr A B) p =
      partialEta (AxisEvaluation.profile I ε A) p * AxisEvaluation.profile I ε B p := by
  rw [partialEta_profile I hε A hp]
  exact AxisEvaluationAlgebra.inverseParamProduct_equation I hε r hr A B
    (abs_lt.mpr hp.1) ⟨hp.2.1.le, hp.2.2.le⟩

theorem radialEvaluation_dot (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε r (AxisOperators.inverseDotProduct I hε r hr A B) p =
      AxisEvaluation.profile I ε A p * (p.1 * partialY (AxisEvaluation.profile I ε B) p) := by
  rw [partialY_profile I hε B hp]
  exact AxisEvaluationAlgebra.inverseDotProduct_equation I hε r hr A B
    (abs_lt.mpr hp.1) ⟨hp.2.1.le, hp.2.2.le⟩

theorem radialEvaluation_mixed (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε r (AxisOperators.inverseMixed I hε r hr A B) p =
      partialEta (AxisEvaluation.profile I ε A) p *
        (p.1 * partialY (AxisEvaluation.profile I ε B) p) := by
  rw [partialEta_profile I hε A hp, partialY_profile I hε B hp]
  exact AxisEvaluationAlgebra.inverseMixed_equation I hε r hr A B
    (abs_lt.mpr hp.1) ⟨hp.2.1.le, hp.2.2.le⟩

/-- Fixed parameter functions appearing in the scaled natural equations. -/
structure ParameterData where
  A : ℝ
  D : ℝ
  h : ℝ
  chi : ℝ → ℝ
  d : ℝ → ℝ
  inverseL : ℝ → ℝ
  uStar : ℝ → ℝ
  uStarEta : ℝ → ℝ
  wStar : ℝ → ℝ
  hStar : ℝ → ℝ
  kappa : ℝ → ℝ
  zStar : ℝ → ℝ

/-- The actual parameter function represented by the zeroth radial coefficient. -/
def inputValue (I : Window) (ε : ℝ) (A : AxisSpace I ε) : ℝ → ℝ :=
  coefficient I (weight ε) A 0

/-- The fixed fields of the integrated system, interpreted as actual functions. -/
def parameters (I : Window) (ε : ℝ) (χ : AxisSpace I ε)
    (d : AxisContraction.AxisData (AxisSpace I ε)) : ParameterData where
  A := d.A
  D := d.D
  h := d.h
  chi := inputValue I ε χ
  d := inputValue I ε d.d
  inverseL := inputValue I ε d.inverseL
  uStar := inputValue I ε d.uStar
  uStarEta := inputValue I ε d.uStarEta
  wStar := inputValue I ε d.wStar
  hStar := inputValue I ε d.hStar
  kappa := inputValue I ε d.normalizedGradient
  zStar := inputValue I ε d.zStar

/-- Fixed analytic input data are independent of the radial coordinate.
These hypotheses concern only the given inputs, never the unknown profiles. -/
structure CompatibleData (I : Window) (ε : ℝ) (χ : AxisSpace I ε)
    (d : AxisContraction.AxisData (AxisSpace I ε)) : Prop where
  chi_radial : RadiallyConstant I ε χ
  one_radial : RadiallyConstant I ε d.one
  eta_radial : RadiallyConstant I ε d.eta
  d_radial : RadiallyConstant I ε d.d
  inverseL_radial : RadiallyConstant I ε d.inverseL
  uStar_radial : RadiallyConstant I ε d.uStar
  uStarEta_radial : RadiallyConstant I ε d.uStarEta
  wStar_radial : RadiallyConstant I ε d.wStar
  hStar_radial : RadiallyConstant I ε d.hStar
  gradient_radial : RadiallyConstant I ε d.normalizedGradient
  zStar_radial : RadiallyConstant I ε d.zStar
  one_value : ∀ η ∈ I.interval, inputValue I ε d.one η = 1
  eta_value : ∀ η ∈ I.interval, inputValue I ε d.eta η = η
  uStarEta_value : ∀ η ∈ Ioo I.left I.right,
    inputValue I ε d.uStarEta η = deriv (inputValue I ε d.uStar) η

/-- The pressure source in the complete coefficient space. -/
def pressureSource (I : Window) {ε : ℝ} (hε : 0 < ε)
    (a Φ : AxisSpace I ε) : AxisSpace I ε :=
  AxisOperators.product I hε (AxisOperators.product I hε a a)
    (AxisOperators.product I hε Φ Φ)

def pressureCoefficient (I : Window) {ε : ℝ} (hε : 0 < ε)
    (a Φ : AxisSpace I ε) : AxisSpace I ε :=
  AxisOperators.primitive I hε (pressureSource I hε a Φ)

/-- The reconstructed axial profile `U=U*+Λ⁻¹u`. -/
def reconstructedU (d : ParameterData) (t : ℝ) (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  d.uStar p.2 + t * u p

/-- The actual transport coefficient using the regular radial average. -/
def reconstructedW (d : ParameterData) (t : ℝ) (B : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  d.wStar p.2 - t * ((2 * d.D * p.2) * B p + d.d p.2 * partialEta B p)

def reconstructedH (d : ParameterData) (t : ℝ) (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  d.hStar p.2 + t * d.d p.2 * u p

/-- The first remainder in equation (17), using ordinary derivatives of
actual functions and `κ=ξ₀/Λ`. -/
def angularRemainder (d : ParameterData) (t : ℝ)
    (Φ u B : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  d.inverseL p.2 *
    ((reconstructedW d t B p + d.h * (1 - 2 * p.2 * reconstructedU d t u p) +
        d.d p.2 * u p * d.kappa p.2) * Φ p +
      reconstructedW d t B p * (p.1 * partialY Φ p) +
      reconstructedH d t u p * partialEta Φ p)

/-- The expanded second remainder in equation (17), including all pressure
terms and the actual parameter derivative of the pressure correction. -/
def axialRemainder (d : ParameterData) (t : ℝ)
    (u B P : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  d.inverseL p.2 *
    (d.A * (1 - 4 * p.2 * d.uStar p.2) * u p -
      2 * d.A * p.2 * t * (u p) ^ 2 +
      reconstructedW d t B p * (p.1 * partialY u p) +
      d.hStar p.2 * partialEta u p + d.d p.2 * d.uStarEta p.2 * u p +
      t * d.d p.2 * u p * partialEta u p -
      4 * d.A * p.2 * P p + d.d p.2 * partialEta P p -
      2 * p.2 * (p.1 * partialY P p))

/-- The target is an equation for actual smooth profiles, together with the
regular-average and pressure identities that determine its auxiliary fields. -/
structure IsScaledSolution (I : Window) (d : ParameterData) (t : ℝ) (a : ℝ → ℝ)
    (Φ u B P : ℝ × ℝ → ℝ) : Prop where
  phi_smooth : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip I 20)
  u_smooth : ContDiffOn ℝ ∞ u (AxisEvaluation.strip I 20)
  average_smooth : ContDiffOn ℝ ∞ B (AxisEvaluation.strip I 20)
  pressure_smooth : ContDiffOn ℝ ∞ P (AxisEvaluation.strip I 20)
  phi_axis : ∀ η ∈ Ioo I.left I.right, Φ (0, η) = 1
  u_axis : ∀ η ∈ Ioo I.left I.right, u (0, η) = 0
  average_axis : ∀ η ∈ Ioo I.left I.right, B (0, η) = u (0, η)
  pressure_axis : ∀ η ∈ Ioo I.left I.right, P (0, η) = 0
  average_equation : ∀ p ∈ AxisEvaluation.strip I 20,
    B p + p.1 * partialY B p = u p
  pressure_equation : ∀ p ∈ AxisEvaluation.strip I 20,
    partialY P p = (a p.2) ^ 2 * (Φ p) ^ 2
  average_integral : ∀ p ∈ AxisEvaluation.strip I 20,
    p.1 * B p = ∫ y in (0 : ℝ)..p.1, u (y, p.2)
  pressure_integral : ∀ p ∈ AxisEvaluation.strip I 20,
    P p = ∫ y in (0 : ℝ)..p.1, (a p.2) ^ 2 * (Φ (y, p.2)) ^ 2
  angular_equation : ∀ p ∈ AxisEvaluation.strip I 20,
    2 * radialDifferential 2 Φ p = -d.chi p.2 * Φ p + t * angularRemainder d t Φ u B p
  axial_equation : ∀ p ∈ AxisEvaluation.strip I 20,
    2 * radialDifferential 1 u p = -d.inverseL p.2 * d.zStar p.2 + t * axialRemainder d t u B P p

theorem profile_inputValue (I : Window) (ε : ℝ) (A : AxisSpace I ε)
    (hA : RadiallyConstant I ε A) {p : ℝ × ℝ} (hη : p.2 ∈ I.interval) :
    AxisEvaluation.profile I ε A p = inputValue I ε A p.2 :=
  profile_radiallyConstant I ε A hA p.1 hη

/-- Differentiating the actual first integrated remainder gives precisely
the first scaled differential remainder, including the mixed term. -/
theorem angular_remainder_evaluation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) (t : ℝ) (a : AxisSpace I ε)
    (x : AxisSpace I ε × AxisSpace I ε) {p : ℝ × ℝ}
    (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε 2
        (AxisContraction.naturalRemainder (AxisContraction.coefficientOperators I hε)
          d (ContinuousLinearMap.id ℝ _) t a x).1 p =
      angularRemainder (parameters I ε χ d) t
        (AxisEvaluation.profile I ε x.1) (AxisEvaluation.profile I ε x.2)
        (AxisEvaluation.profile I ε (AxisOperators.average I hε x.2)) p := by
  have hY : |p.1| < 20 := abs_lt.mpr hp.1
  have hη : p.2 ∈ I.interval := ⟨hp.2.1.le, hp.2.2.le⟩
  have radd := fun A B => radialEvaluation_add I hε 2 A B hY
  have rsub := fun A B => radialEvaluation_sub I hε 2 A B hY
  have rsmul := fun c A => radialEvaluation_smul I ε c 2 A p
  have rj := fun A => radialEvaluation_regularInverse I hε 2 (by norm_num) A hp
  have rp := fun A B => radialEvaluation_param I hε 2 (by norm_num) A B hp
  have rd := fun A B => radialEvaluation_dot I hε 2 (by norm_num) A B hp
  have rm := fun A B => radialEvaluation_mixed I hε 2 (by norm_num) A B hp
  have rfactor := fun A => radialEvaluation_product_constant I hε 2 d.d A hd.d_radial hp
  have rinv := fun A => radialEvaluation_product_constant I hε 2 d.inverseL A hd.inverseL_radial hp
  have pmul := fun A B => AxisEvaluationAlgebra.profile_product I hε A B hY hη
  have padd := fun A B => profile_add I hε A B hY
  have psub := fun A B => profile_sub I hε A B hY
  have psmul := fun c A => profile_smul I ε c A p
  have pbase := fun A hA => profile_inputValue I ε A hA hη
  dsimp only [AxisContraction.naturalRemainder, AxisContraction.coefficientOperators,
    ContinuousLinearMap.id_apply]
  simp only [rinv, radd, rsub, rsmul, rj, rp, rd, rm, rfactor]
  simp only [AxisContraction.angularLinearCoefficient,
    AxisContraction.angularQuadraticCoefficient, AxisContraction.averageCoefficient,
    AxisContraction.angularSlowCoefficient,
    pmul, padd, psub, psmul]
  simp only [pbase d.one hd.one_radial, pbase d.eta hd.eta_radial,
    pbase d.d hd.d_radial, pbase d.inverseL hd.inverseL_radial,
    pbase d.uStar hd.uStar_radial, pbase d.wStar hd.wStar_radial,
    pbase d.hStar hd.hStar_radial, pbase d.normalizedGradient hd.gradient_radial,
    hd.one_value p.2 hη, hd.eta_value p.2 hη]
  simp only [angularRemainder, reconstructedW, reconstructedU, reconstructedH, parameters]
  ring

/-- Differentiating the second integrated remainder gives the complete
axial differential remainder, with the actual pressure derivatives. -/
theorem axial_remainder_evaluation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) (t : ℝ) (a : AxisSpace I ε)
    (x : AxisSpace I ε × AxisSpace I ε) {p : ℝ × ℝ}
    (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε 1
        (AxisContraction.naturalRemainder (AxisContraction.coefficientOperators I hε)
          d (ContinuousLinearMap.id ℝ _) t a x).2 p =
      axialRemainder (parameters I ε χ d) t
        (AxisEvaluation.profile I ε x.2)
        (AxisEvaluation.profile I ε (AxisOperators.average I hε x.2))
        (AxisEvaluation.profile I ε (pressureCoefficient I hε a x.1)) p := by
  have hY : |p.1| < 20 := abs_lt.mpr hp.1
  have hη : p.2 ∈ I.interval := ⟨hp.2.1.le, hp.2.2.le⟩
  have radd := fun A B => radialEvaluation_add I hε 1 A B hY
  have rsub := fun A B => radialEvaluation_sub I hε 1 A B hY
  have rsmul := fun c A => radialEvaluation_smul I ε c 1 A p
  have rj := fun A => radialEvaluation_regularInverse I hε 1 (by norm_num) A hp
  have rp := fun A B => radialEvaluation_param I hε 1 (by norm_num) A B hp
  have rd := fun A B => radialEvaluation_dot I hε 1 (by norm_num) A B hp
  have rm := fun A B => radialEvaluation_mixed I hε 1 (by norm_num) A B hp
  have rfactor := fun A => radialEvaluation_product_constant I hε 1 d.d A hd.d_radial hp
  have rinv := fun A => radialEvaluation_product_constant I hε 1 d.inverseL A hd.inverseL_radial hp
  have pmul := fun A B => AxisEvaluationAlgebra.profile_product I hε A B hY hη
  have padd := fun A B => profile_add I hε A B hY
  have psub := fun A B => profile_sub I hε A B hY
  have psmul := fun c A => profile_smul I ε c A p
  have pneg := fun A => profile_neg I ε A p
  have pbase := fun A hA => profile_inputValue I ε A hA hη
  have pparam := fun A => AxisEvaluationAlgebra.parameterPrimitive_eq_deriv_eta
    I hε A hp.1 hp.2
  have pmy (A : AxisSpace I ε) :
      AxisEvaluation.profile I ε (AxisOperators.mulY I hε A) p =
        p.1 * partialY (AxisEvaluation.profile I ε (AxisOperators.primitive I hε A)) p := by
    rw [AxisEvaluationAlgebra.profile_mulY I hε A hY hη,
      partialY_profile I hε _ hp, AxisEvaluationAlgebra.primitive_Y_value I hε A hY hη]
  dsimp only [AxisContraction.naturalRemainder, AxisContraction.coefficientOperators]
  simp only [rinv, radd, rsub, rsmul, rj, rp, rd, rm, rfactor]
  simp only [AxisContraction.axialLinearCoefficient, AxisContraction.axialQuadraticCoefficient,
    AxisContraction.averageCoefficient,
    pmul, padd, psub, psmul, pneg, pparam, pmy]
  simp only [pbase d.one hd.one_radial, pbase d.eta hd.eta_radial,
    pbase d.d hd.d_radial, pbase d.inverseL hd.inverseL_radial,
    pbase d.uStar hd.uStar_radial, pbase d.uStarEta hd.uStarEta_radial,
    pbase d.wStar hd.wStar_radial, pbase d.hStar hd.hStar_radial,
    hd.one_value p.2 hη, hd.eta_value p.2 hη]
  simp only [axialRemainder, reconstructedW, parameters, pressureCoefficient, pressureSource,
    partialEta]
  ring

/-- Both integrated remainders have exactly zero axis value. -/
theorem remainder_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (d : AxisContraction.AxisData (AxisSpace I ε)) (t : ℝ) (a : AxisSpace I ε)
    (x : AxisSpace I ε × AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    AxisEvaluation.profile I ε
        (AxisContraction.naturalRemainder (AxisContraction.coefficientOperators I hε)
          d (ContinuousLinearMap.id ℝ _) t a x).1 (0, η) = 0 ∧
      AxisEvaluation.profile I ε
        (AxisContraction.naturalRemainder (AxisContraction.coefficientOperators I hε)
          d (ContinuousLinearMap.id ℝ _) t a x).2 (0, η) = 0 := by
  have hY : |(0 : ℝ)| < 20 := by norm_num
  have padd := fun A B => profile_add I hε A B (p := (0, η)) hY
  have psub := fun A B => profile_sub I hε A B (p := (0, η)) hY
  have psmul := fun c A => profile_smul I ε c A (0, η)
  have pmul := fun A B => AxisEvaluationAlgebra.profile_product I hε A B hY hη
  have pj := fun r hr A => AxisEvaluationAlgebra.regularInverse_axis_zero I hε r hr A hη
  have pp := fun r hr A B => AxisEvaluationAlgebra.inverseParamProduct_axis_zero I hε r hr A B hη
  have pd := fun r hr A B => AxisEvaluationAlgebra.inverseDotProduct_axis_zero I hε r hr A B hη
  have pm := fun r hr A B => AxisEvaluationAlgebra.inverseMixed_axis_zero I hε r hr A B hη
  constructor <;>
    dsimp only [AxisContraction.naturalRemainder, AxisContraction.coefficientOperators,
      ContinuousLinearMap.id_apply] <;>
    simp only [padd, psub, psmul, pmul, pj, pp, pd, pm, mul_zero,
      add_zero, sub_zero]

theorem naturalOperator_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ A : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    AxisEvaluation.profile I ε (AxisResolvent.naturalOperator I hε χ A) (0, η) = 0 := by
  simp only [AxisResolvent.naturalOperator, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, profile_smul,
    AxisEvaluationAlgebra.regularInverse_axis_zero I hε _ _ _ hη, mul_zero]

theorem radialEvaluation_naturalOperator (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ A : AxisSpace I ε) (hχ : RadiallyConstant I ε χ)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε 2 (AxisResolvent.naturalOperator I hε χ A) p =
      (1 / 2 : ℝ) * inputValue I ε χ p.2 * AxisEvaluation.profile I ε A p := by
  simp only [AxisResolvent.naturalOperator, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, radialEvaluation_smul]
  rw [radialEvaluation_regularInverse I hε 2 (by norm_num) _ hp,
    AxisEvaluationAlgebra.profile_product I hε χ A (abs_lt.mpr hp.1) ⟨hp.2.1.le, hp.2.2.le⟩,
    profile_inputValue I ε χ hχ ⟨hp.2.1.le, hp.2.2.le⟩]
  ring

theorem pressure_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (a Φ : AxisSpace I ε) (ha : RadiallyConstant I ε a)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    partialY (AxisEvaluation.profile I ε (pressureCoefficient I hε a Φ)) p =
      (inputValue I ε a p.2) ^ 2 * (AxisEvaluation.profile I ε Φ p) ^ 2 := by
  have hY : |p.1| < 20 := abs_lt.mpr hp.1
  have hη : p.2 ∈ I.interval := ⟨hp.2.1.le, hp.2.2.le⟩
  rw [pressureCoefficient, partialY_profile I hε _ hp,
    AxisEvaluationAlgebra.primitive_Y_value I hε _ hY hη]
  simp only [pressureSource, AxisEvaluationAlgebra.profile_product I hε _ _ hY hη,
    profile_inputValue I ε a ha hη]
  ring

/-- The pressure field is the ordinary integral from the axis, rather
than merely a formal coefficient primitive. -/
theorem pressure_integral (I : Window) {ε : ℝ} (hε : 0 < ε)
    (a Φ : AxisSpace I ε) (ha : RadiallyConstant I ε a)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    AxisEvaluation.profile I ε (pressureCoefficient I hε a Φ) p =
      ∫ y in (0 : ℝ)..p.1,
        (inputValue I ε a p.2) ^ 2 * (AxisEvaluation.profile I ε Φ (y, p.2)) ^ 2 := by
  rw [pressureCoefficient, AxisEvaluationAlgebra.primitive_integral I hε _ hp.1 hp.2]
  apply intervalIntegral.integral_congr
  intro y hy
  have hY : |y| < 20 := abs_lt.mpr (AxisEvaluationAlgebra.radial_segment_mem hp.1 hy)
  have hη : p.2 ∈ I.interval := ⟨hp.2.1.le, hp.2.2.le⟩
  simp only [pressureSource, AxisEvaluationAlgebra.profile_product I hε _ _ hY hη,
    profile_inputValue I ε a ha (p := (y, p.2)) hη]
  ring

/-- The integrated coefficient equations give the literal scaled equations
for actual smooth functions on the open real strip. -/
theorem integrated_solution (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) (t s : ℝ) (hst : 2 * s = t)
    (a : AxisSpace I ε) (ha : RadiallyConstant I ε a)
    (x : AxisSpace I ε × AxisSpace I ε)
    (hφ : x.1 + AxisResolvent.naturalOperator I hε χ x.1 =
      d.one + s • (AxisContraction.naturalRemainder
        (AxisContraction.coefficientOperators I hε) d (ContinuousLinearMap.id ℝ _) t a x).1)
    (hu : x.2 = -(1 / 2 : ℝ) • AxisOperators.regularInverse I hε 1 (by norm_num)
        (AxisOperators.product I hε d.inverseL d.zStar) +
      s • (AxisContraction.naturalRemainder
        (AxisContraction.coefficientOperators I hε) d (ContinuousLinearMap.id ℝ _) t a x).2) :
    IsScaledSolution I (parameters I ε χ d) t (inputValue I ε a)
      (AxisEvaluation.profile I ε x.1) (AxisEvaluation.profile I ε x.2)
      (AxisEvaluation.profile I ε (AxisOperators.average I hε x.2))
      (AxisEvaluation.profile I ε (pressureCoefficient I hε a x.1)) := by
  refine {
    phi_smooth := AxisEvaluation.profile_smooth I hε x.1
    u_smooth := AxisEvaluation.profile_smooth I hε x.2
    average_smooth := AxisEvaluation.profile_smooth I hε _
    pressure_smooth := AxisEvaluation.profile_smooth I hε _
    phi_axis := ?_
    u_axis := ?_
    average_axis := ?_
    pressure_axis := ?_
    average_equation := ?_
    pressure_equation := fun p hp => pressure_equation I hε a x.1 ha hp
    average_integral := ?_
    pressure_integral := fun p hp => pressure_integral I hε a x.1 ha hp
    angular_equation := ?_
    axial_equation := ?_ }
  · intro η hη
    have hηc : η ∈ I.interval := ⟨hη.1.le, hη.2.le⟩
    have h0 : |(0 : ℝ)| < 20 := by norm_num
    have he := congrArg (fun A => AxisEvaluation.profile I ε A (0, η)) hφ
    simp only [profile_add I hε _ _ (p := (0, η)) h0,
      naturalOperator_axis_zero I hε χ x.1 hηc,
      profile_smul, (remainder_axis_zero I hε d t a x hηc).1,
      profile_inputValue I ε d.one hd.one_radial (p := (0, η)) hηc,
      hd.one_value η hηc] at he
    simpa only [add_zero, mul_zero] using he
  · intro η hη
    have hηc : η ∈ I.interval := ⟨hη.1.le, hη.2.le⟩
    have h0 : |(0 : ℝ)| < 20 := by norm_num
    have he := congrArg (fun A => AxisEvaluation.profile I ε A (0, η)) hu
    simp only [profile_add I hε _ _ (p := (0, η)) h0, profile_smul,
      AxisEvaluationAlgebra.regularInverse_axis_zero I hε 1 (by norm_num) _ hηc,
      (remainder_axis_zero I hε d t a x hηc).2] at he
    simpa only [mul_zero, add_zero] using he
  · intro η hη
    exact AxisEvaluationAlgebra.average_axis I hε x.2 ⟨hη.1.le, hη.2.le⟩
  · intro η hη
    exact AxisEvaluationAlgebra.primitive_axis_zero I hε _ ⟨hη.1.le, hη.2.le⟩
  · intro p hp
    rw [partialY_profile I hε _ hp]
    exact AxisEvaluationAlgebra.average_equation I hε x.2 (abs_lt.mpr hp.1)
      ⟨hp.2.1.le, hp.2.2.le⟩
  · intro p hp
    exact AxisEvaluationAlgebra.average_integral I hε x.2 hp.1 hp.2
  · intro p hp
    have hY : |p.1| < 20 := abs_lt.mpr hp.1
    have he := congrArg (fun A => radialEvaluation I ε 2 A p) hφ
    simp only [radialEvaluation_add I hε 2 _ _ hY,
      radialEvaluation_naturalOperator I hε χ x.1 hd.chi_radial hp,
      radialEvaluation_constant I hε 2 d.one hd.one_radial hp,
      radialEvaluation_smul, angular_remainder_evaluation I hε χ d hd t a x hp,
      radialEvaluation_eq I hε 2 x.1 hp] at he
    change 2 * radialDifferential 2 (AxisEvaluation.profile I ε x.1) p =
      -inputValue I ε χ p.2 * AxisEvaluation.profile I ε x.1 p + _
    calc
      _ = -inputValue I ε χ p.2 * AxisEvaluation.profile I ε x.1 p +
          (2 * s) * angularRemainder (parameters I ε χ d) t
            (AxisEvaluation.profile I ε x.1) (AxisEvaluation.profile I ε x.2)
            (AxisEvaluation.profile I ε (AxisOperators.average I hε x.2)) p := by
        nlinarith only [he]
      _ = _ := by rw [hst]
  · intro p hp
    have hY : |p.1| < 20 := abs_lt.mpr hp.1
    have hη : p.2 ∈ I.interval := ⟨hp.2.1.le, hp.2.2.le⟩
    have he := congrArg (fun A => radialEvaluation I ε 1 A p) hu
    simp only [radialEvaluation_add I hε 1 _ _ hY,
      radialEvaluation_smul,
      radialEvaluation_regularInverse I hε 1 (by norm_num) _ hp,
      axial_remainder_evaluation I hε χ d hd t a x hp,
      AxisEvaluationAlgebra.profile_product I hε d.inverseL d.zStar hY hη,
      profile_inputValue I ε d.inverseL hd.inverseL_radial hη,
      profile_inputValue I ε d.zStar hd.zStar_radial hη,
      radialEvaluation_eq I hε 1 x.2 hp] at he
    change 2 * radialDifferential 1 (AxisEvaluation.profile I ε x.2) p =
      -inputValue I ε d.inverseL p.2 * inputValue I ε d.zStar p.2 + _
    calc
      _ = -inputValue I ε d.inverseL p.2 * inputValue I ε d.zStar p.2 +
          (2 * s) * axialRemainder (parameters I ε χ d) t
            (AxisEvaluation.profile I ε x.2)
            (AxisEvaluation.profile I ε (AxisOperators.average I hε x.2))
            (AxisEvaluation.profile I ε (pressureCoefficient I hε a x.1)) p := by
        nlinarith only [he]
      _ = _ := by rw [hst]

/-- The leading pair defined using the proved angular resolvent. -/
def referenceCoefficients (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε)) :
    AxisSpace I ε × AxisSpace I ε :=
  AxisContraction.referencePair (AxisContraction.coefficientOperators I hε) d
    (AxisResolvent.naturalResolvent I hε χ)

/-- The limiting system is stated directly for actual functions. -/
structure IsLeadingSolution (I : Window) (d : ParameterData)
    (Φ u : ℝ × ℝ → ℝ) : Prop where
  phi_smooth : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip I 20)
  u_smooth : ContDiffOn ℝ ∞ u (AxisEvaluation.strip I 20)
  phi_axis : ∀ η ∈ Ioo I.left I.right, Φ (0, η) = 1
  u_axis : ∀ η ∈ Ioo I.left I.right, u (0, η) = 0
  angular_equation : ∀ p ∈ AxisEvaluation.strip I 20,
    2 * radialDifferential 2 Φ p = -d.chi p.2 * Φ p
  axial_equation : ∀ p ∈ AxisEvaluation.strip I 20,
    2 * radialDifferential 1 u p = -d.inverseL p.2 * d.zStar p.2


/-- A fixed finite constant computed from the input norms and the genuine
bounded operators. It is independent of `Λ` and of the amplitude in its norm ball. -/
def errorConstant (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (M : ℝ) (hM : 0 ≤ M) : ℝ :=
  AxisContraction.remainderBound (AxisContraction.coefficientOperators I hε) d
    (AxisResolvent.naturalResolvent I hε χ)
    (‖referenceCoefficients I hε χ d‖ + 1) M (by positivity) hM

theorem errorConstant_nonneg (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (M : ℝ) (hM : 0 ≤ M) : 0 ≤ errorConstant I hε χ d M hM :=
  AxisContraction.remainderBound_nonneg _ _ _ _ _ _ _

/-- Simultaneous estimates for every ordinary mixed derivative, uniform on
each smaller radial interval and on the whole open parameter interval. -/
def UniformMixedError (I : Window) (ε K : ℝ)
    (Φ u Φ₀ u₀ : ℝ × ℝ → ℝ) : Prop :=
  ∀ R : ℝ, 1 ≤ R → R < 20 → ∀ k m : ℕ, ∀ p : ℝ × ℝ,
    |p.1| ≤ R → p.2 ∈ Ioo I.left I.right →
      |mixedDerivative k m Φ p - mixedDerivative k m Φ₀ p| ≤
          AxisEvaluation.jetBound ε R k m * K ∧
        |mixedDerivative k m u p - mixedDerivative k m u₀ p| ≤
          AxisEvaluation.jetBound ε R k m * K

theorem uniformMixedError_of_norm (I : Window) {ε : ℝ} (hε : 0 < ε)
    (x x₀ : AxisSpace I ε × AxisSpace I ε) (K : ℝ) (hK : ‖x - x₀‖ ≤ K) :
    UniformMixedError I ε K
      (AxisEvaluation.profile I ε x.1) (AxisEvaluation.profile I ε x.2)
      (AxisEvaluation.profile I ε x₀.1) (AxisEvaluation.profile I ε x₀.2) := by
  intro R hR hR20 k m p hY hη
  constructor
  · simpa only [mixedDerivative, Real.norm_eq_abs] using
      AxisContraction.evaluated_mixed_error I hε hR hR20 x.1 x₀.1 K
        ((norm_fst_le (x - x₀)).trans hK) k m hY hη
  · simpa only [mixedDerivative, Real.norm_eq_abs] using
      AxisContraction.evaluated_mixed_error I hε hR hR20 x.2 x₀.2 K
        ((norm_snd_le (x - x₀)).trans hK) k m hY hη

/-- Actual smooth natural-axis profiles exist for every sufficiently large
`Λ`, uniformly over all radially constant angular amplitudes in a fixed norm
ball. The conclusion is a differential/integral system for real functions,
and its error estimate concerns their ordinary derivatives of every order. -/
theorem exists_scaled_profiles (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) (M : ℝ) (hM : 0 ≤ M) :
    ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
      ∀ a : AxisSpace I ε, ‖a‖ ≤ M → RadiallyConstant I ε a →
      ∃ Φ u B P : ℝ × ℝ → ℝ,
        IsScaledSolution I (parameters I ε χ d) (1 / Λ) (inputValue I ε a) Φ u B P ∧
        UniformMixedError I ε (errorConstant I hε χ d M hM / (2 * Λ))
          Φ u (AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1)
          (AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).2) := by
  obtain ⟨Λ₀, hΛ₀, hexists⟩ := AxisContraction.natural_axis_profiles I hε χ d M hM
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ a ha harad
  obtain ⟨x, _, herr, hφ, hu, _, _⟩ := hexists Λ hΛ a ha
  have hscale : 2 * (1 / (2 * Λ)) = 1 / Λ := by
    field_simp [(hΛ₀.trans_le hΛ).ne']
  refine ⟨AxisEvaluation.profile I ε x.1, AxisEvaluation.profile I ε x.2,
    AxisEvaluation.profile I ε (AxisOperators.average I hε x.2),
    AxisEvaluation.profile I ε (pressureCoefficient I hε a x.1),
    integrated_solution I hε χ d hd (1 / Λ) (1 / (2 * Λ)) hscale a harad x hφ hu, ?_⟩
  exact uniformMixedError_of_norm I hε x (referenceCoefficients I hε χ d)
    (errorConstant I hε χ d M hM / (2 * Λ)) herr

end NavierStokes.NaturalAxisBridge

end

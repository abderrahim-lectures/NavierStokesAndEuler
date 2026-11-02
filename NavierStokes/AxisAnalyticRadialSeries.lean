import NavierStokes.AxisHolomorphic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import NavierStokes.CauchyRestriction

/-! # A convergent radial series in a Banach space of parameter-disk functions -/

/-! Merged from `NavierStokes.AxisAnalyticCoefficients`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Holomorphic radial coefficients with a common geometric bound -/

noncomputable section

open Set Metric Filter Complex
open scoped Topology
open NavierStokes.AxisCoefficientSpace NavierStokes.AxisWeightEstimates
open NavierStokes.AxisEvaluation NavierStokes.AxisHolomorphic

namespace NavierStokes.AxisJointAnalytic

def coefficientJet (I : Window) (ε : ℝ) (A : AxisSpace I ε) (n m : ℕ) (x : ℝ) : ℝ :=
  jet I (weight ε) A.1 n m x / (m.factorial : ℝ)

theorem coefficientJet_hasDerivAt (I : Window) {ε : ℝ} (_hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) {x : ℝ} (hx : x ∈ Ioo I.left I.right) :
    HasDerivAt (coefficientJet I ε A n m)
      (((m : ℝ) + 1) * coefficientJet I ε A n (m + 1) x) x := by
  have hd := (hasDerivAt_jet_interior I (weight ε) A n m hx).div_const (m.factorial : ℝ)
  convert! hd using 1
  unfold coefficientJet
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem coefficientJet_bound (I : Window) {ε s : ℝ} (hε : 0 < ε)
    (hs : (1 : ℝ) / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (n m : ℕ) (x : ℝ) :
    ‖coefficientJet I ε A n m x‖ ≤
      (‖A‖ / (1 - s) * (1 / 20 / s) ^ n) * ((ε * (1 - s))⁻¹) ^ m := by
  have hb := term_factorial_bound I hε (R := 1) (by rfl) hs hs1 A 0 m n
    (p := (1, x)) (by norm_num)
  simp only [term, polynomialJet, Nat.descFactorial_zero, Nat.cast_one, Nat.sub_zero,
    one_pow, one_mul, pow_zero, mul_one] at hb
  rw [coefficientJet, norm_div, Real.norm_natCast]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < m.factorial)).mpr
  calc
    _ ≤ _ := hb
    _ = _ := by ring

/-- The actual vertical Taylor extension of radial coefficient `n`. -/
def complexCoefficient (I : Window) (ε : ℝ) (A : AxisSpace I ε) (n : ℕ) : ℂ → ℂ :=
  verticalExtension (coefficientJet I ε A n)

theorem complexCoefficient_ofReal (I : Window) (ε : ℝ) (A : AxisSpace I ε)
    (n : ℕ) (x : ℝ) :
    complexCoefficient I ε A n (x : ℂ) = (coefficient I (weight ε) A n x : ℂ) := by
  rw [complexCoefficient, verticalExtension_ofReal]
  simp [coefficientJet, coefficient]

theorem complexCoefficient_analytic (I : Window) {ε s : ℝ} (hε : 0 < ε)
    (hs : (1 : ℝ) / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε) (n : ℕ) :
    AnalyticOnNhd ℂ (complexCoefficient I ε A n) (parameterStrip I (ε * (1 - s))) := by
  apply verticalExtension_analytic I (C := ‖A‖ / (1 - s) * (1 / 20 / s) ^ n)
    (mul_nonneg (div_nonneg (norm_nonneg A) (by linarith)) (by positivity))
    (mul_pos hε (by linarith))
  · intro m x hx
    exact coefficientJet_hasDerivAt I hε A n m hx
  · intro m x _
    exact coefficientJet_bound I hε hs hs1 A n m x

theorem complexCoefficient_bound (I : Window) {ε s : ℝ} (hε : 0 < ε)
    (hs : (1 : ℝ) / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε) (n : ℕ)
    {z : ℂ} (hz : z ∈ parameterStrip I (ε * (1 - s))) :
    ‖complexCoefficient I ε A n z‖ ≤ (2 * ‖A‖ / (1 - s)) * (1 / 20 / s) ^ n := by
  have hb := verticalExtension_bound
    (C := ‖A‖ / (1 - s) * (1 / 20 / s) ^ n)
    (mul_nonneg (div_nonneg (norm_nonneg A) (by linarith)) (by positivity))
    (mul_pos hε (by linarith)) hz.2.le
    (fun m => coefficientJet_bound I hε hs hs1 A n m z.re)
  change ‖verticalExtension (coefficientJet I ε A n) z‖ ≤ _
  convert! hb using 1
  ring

end NavierStokes.AxisJointAnalytic


end


noncomputable section

open Set Metric Filter Complex
open scoped Topology
open NavierStokes.AxisCoefficientSpace NavierStokes.AxisWeightEstimates
open NavierStokes.AxisEvaluation NavierStokes.AxisHolomorphic NavierStokes.CauchyRestriction

namespace NavierStokes.AxisJointAnalytic

section Geometric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Uniform geometric coefficient bounds yield a genuine Banach-valued
holomorphic radial sum throughout the indicated disk. -/
theorem geometricSeries_analytic {a : ℕ → E} {C ρ R : ℝ}
    (_hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hR : 0 < R) (hq : R * ρ < 1)
    (ha : ∀ n, ‖a n‖ ≤ C * ρ ^ n) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∑' n : ℕ, z ^ n • a n) (ball 0 R) := by
  have hg : Summable (fun n : ℕ => C * (R * ρ) ^ n) :=
    (summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hR.le hρ)]
      exact hq)).mul_left C
  apply (Complex.differentiableOn_tsum_of_summable_norm hg _ isOpen_ball _).analyticOnNhd isOpen_ball
  · intro n
    exact ((differentiable_id.pow n).smul_const (a n)).differentiableOn
  · intro n z hz
    have hzR : ‖z‖ ≤ R := (mem_ball_zero_iff.mp hz).le
    rw [norm_smul, norm_pow]
    calc
      _ ≤ R ^ n * (C * ρ ^ n) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hzR n)
        (ha n) (norm_nonneg _) (pow_nonneg hR.le n)
      _ = _ := by rw [mul_pow]; ring

theorem geometricSeries_summable {a : ℕ → E} {C ρ R : ℝ}
    (_hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hR : 0 < R) (hq : R * ρ < 1)
    (ha : ∀ n, ‖a n‖ ≤ C * ρ ^ n) {z : ℂ} (hz : ‖z‖ ≤ R) :
    Summable (fun n : ℕ => z ^ n • a n) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hR.le hρ)]
      exact hq)).mul_left C)
  intro n
  rw [norm_smul, norm_pow]
  calc
    _ ≤ R ^ n * (C * ρ ^ n) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz n)
      (ha n) (norm_nonneg _) (pow_nonneg hR.le n)
    _ = _ := by rw [mul_pow]; ring

end Geometric

/-- Each coefficient restricted to a closed disk inside the common strip. -/
def diskCoefficient (I : Window) {ε s : ℝ} (hε : 0 < ε)
    (hs : (1 : ℝ) / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s)))
    (n : ℕ) : C(Disk c σ, ℂ) where
  toFun z := complexCoefficient I ε A n z
  continuous_toFun := (complexCoefficient_analytic I hε hs hs1 A n).continuousOn.comp_continuous
    continuous_subtype_val (fun z => hK z.2)

theorem diskCoefficient_bound (I : Window) {ε s : ℝ} (hε : 0 < ε)
    (hs : (1 : ℝ) / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s))) (n : ℕ) :
    ‖diskCoefficient I hε hs hs1 A c σ hK n‖ ≤
      (2 * ‖A‖ / (1 - s)) * (1 / 20 / s) ^ n := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro z
  exact complexCoefficient_bound I hε hs hs1 A n (hK z.2)

/-- The same coefficient series, evaluated at a real radius and a complex
parameter. Its real slice is the original constructed profile. -/
def radialExtension (I : Window) (ε : ℝ) (A : AxisSpace I ε) (Y : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (Y : ℂ) ^ n * complexCoefficient I ε A n z

theorem radialExtension_ofReal (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y : ℝ} (hY : |Y| < 20) (x : ℝ) :
    radialExtension I ε A Y (x : ℂ) = (profile I ε A (Y, x) : ℂ) := by
  unfold radialExtension profile
  simp only [complexCoefficient_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  exact (Complex.ofRealCLM.map_tsum (profile_hasSum I hε A (p := (Y, x)) hY).summable).symm

end NavierStokes.AxisJointAnalytic

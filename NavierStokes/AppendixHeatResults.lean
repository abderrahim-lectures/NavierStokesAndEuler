import NavierStokes.HeatProfileExtension
import Mathlib.RingTheory.Polynomial.Pochhammer

/-! Exact endpoint jets and quantitative small-argument estimates for the
gamma integral in `heat:exterior`. -/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokes.AppendixHeatResults

open RadialHeatProfile

/-- The rising factorial used in the manuscript: Mathlib's `ascPochhammer` polynomial,
evaluated at the argument. -/
def rising (b : ℝ) (n : ℕ) : ℝ := (ascPochhammer ℝ n).eval b

theorem rising_zero (b : ℝ) : rising b 0 = 1 := by
  simp [rising, ascPochhammer_zero]

theorem rising_succ (b : ℝ) (n : ℕ) :
    rising b (n + 1) = rising b n * (b + n) := by
  simpa only [rising] using ascPochhammer_succ_eval (S := ℝ) n b

theorem rising_one (b : ℝ) : rising b 1 = b := by
  have h := ascPochhammer_succ_eval (S := ℝ) 0 b
  simpa [rising, ascPochhammer_zero] using h

theorem rising_two (b : ℝ) : rising b 2 = b * (b + 1) := by
  rw [rising_succ, rising_one]; ring

theorem rising_nonneg {b : ℝ} (hb : 0 ≤ b) (n : ℕ) : 0 ≤ rising b n := by
  induction n with
  | zero => simp [rising_zero]
  | succ n ih =>
    rw [rising_succ]
    exact mul_nonneg ih (by linarith)


theorem rising_mono {b c : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) (n : ℕ) :
    rising b n ≤ rising c n := by
  induction n with
  | zero => simp [rising_zero]
  | succ n ih =>
    rw [rising_succ, rising_succ]
    exact mul_le_mul ih (by linarith) (by linarith) (rising_nonneg (le_trans hb hbc) n)

theorem rising_succ_left (b : ℝ) (n : ℕ) :
    rising b (n + 1) = b * rising (1 + b) n := by
  induction n with
  | zero => simp [rising_succ, rising_zero]
  | succ n ih =>
    rw [rising_succ b (n + 1), ih, rising_succ (1 + b) n]
    push_cast
    ring

theorem derivativeCoeff_eq_rising (h : ℝ) (n : ℕ) :
    derivativeCoeff (1 + h) n = (-1 : ℝ) ^ n * rising h n := by
  induction n with
  | zero => simp [derivativeCoeff, rising_zero]
  | succ n ih => rw [derivativeCoeff, ih, rising_succ, pow_succ]; ring

theorem gamma_add_nat {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Real.Gamma (a + n) = Real.Gamma a * rising a n := by
  induction n with
  | zero => simp [rising_zero]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc,
      Real.Gamma_add_one (by positivity : a + (n : ℝ) ≠ 0), ih, rising_succ]
    ring

/-- The displayed endpoint formula holds for actual one-sided derivatives,
not merely a recursively specified formal series. -/
theorem endpoint_derivatives {h : ℝ} (hh : 0 < h) (n : ℕ) :
    iteratedDerivWithin n (profile (1 + h)) (Ici 0) 0 =
      (-1 : ℝ) ^ n * rising h n * rising (1 + h) n := by
  rw [iteratedDerivWithin_profile (by linarith : 1 < 1 + h) n le_rfl,
    profileJet, moment_zero (by linarith : 1 < 1 + h), derivativeCoeff_eq_rising,
    gamma_add_nat (by linarith : 0 < 1 + h)]
  have hg := (Real.Gamma_pos_of_pos (by linarith : 0 < 1 + h)).ne'
  field_simp

/-- Every derivative is bounded by the magnitude of its endpoint value. -/
theorem derivative_bound_rising {h z : ℝ} (hh : 0 < h) (hz : 0 ≤ z) (n : ℕ) :
    |iteratedDerivWithin n (profile (1 + h)) (Ici 0) z| ≤
      rising h n * rising (1 + h) n := by
  have hb := profile_derivative_bound (a := 1 + h) (by linarith) n hz
  have hg := Real.Gamma_pos_of_pos (by linarith : 0 < 1 + h)
  rw [derivativeCoeff_eq_rising, gamma_add_nat (by linarith : 0 < 1 + h),
    abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (rising_nonneg hh.le n), abs_of_pos (inv_pos.mpr hg)] at hb
  convert hb using 1
  field_simp


theorem first_endpoint_jet {h : ℝ} (hh : 0 < h) :
    profileJet (1 + h) 1 0 = -h * (1 + h) := by
  rw [← iteratedDerivWithin_profile (by linarith : 1 < 1 + h) 1 le_rfl,
    endpoint_derivatives hh]
  simp [rising_one]

/-- An explicit derivative bound on the entire nonnegative half-line. -/
theorem second_jet_bound {h z : ℝ} (hh : 0 < h) (hz : 0 ≤ z) :
    |profileJet (1 + h) 2 z| ≤ h * (1 + h) ^ 2 * (2 + h) := by
  have hb := profile_derivative_bound (a := 1 + h) (by linarith) 2 hz
  rw [iteratedDerivWithin_profile (by linarith : 1 < 1 + h) 2 hz] at hb
  have hg := Real.Gamma_pos_of_pos (by linarith : 0 < 1 + h)
  have he : |(Real.Gamma (1 + h))⁻¹ * derivativeCoeff (1 + h) 2| *
      Real.Gamma (1 + h + (2 : ℕ)) = h * (1 + h) ^ 2 * (2 + h) := by
    rw [gamma_add_nat (by linarith : 0 < 1 + h)]
    have hc : derivativeCoeff (1 + h) 2 = h * (1 + h) := by
      simp [derivativeCoeff]; ring
    rw [hc, abs_of_pos (by positivity)]
    simp only [rising_two]
    field_simp
    ring
  exact hb.trans_eq he

theorem first_jet_remainder {h z : ℝ} (hh : 0 < h) (hz : 0 ≤ z) :
    |profileJet (1 + h) 1 z + h * (1 + h)| ≤
      h * (1 + h) ^ 2 * (2 + h) * z := by
  have H := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := profileJet (1 + h) 1) (f' := profileJet (1 + h) 2)
    (a := 0) (b := z) (C := h * (1 + h) ^ 2 * (2 + h))
    (fun x hx => (profileJet_hasDerivWithinAt (by linarith : 1 < 1 + h) 1 hx.1).mono
      Icc_subset_Ici_self)
    (fun x hx => by simpa only [Real.norm_eq_abs] using second_jet_bound hh hx.1)
  simpa only [Real.norm_eq_abs, first_endpoint_jet hh, neg_mul, sub_neg_eq_add, sub_zero]
    using H z ⟨hz, le_rfl⟩



end NavierStokes.AppendixHeatResults

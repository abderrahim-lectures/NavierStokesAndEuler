import NavierStokes.R3.ComparisonCutoffs
import NavierStokes.R3.ComparisonFiniteEnergy
import NavierStokes.R3.ComparisonGronwall
import NavierStokes.R3.LocalizedDifferenceEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.OpenPos
import NavierStokes.R3.LocalizedFluxEstimates
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

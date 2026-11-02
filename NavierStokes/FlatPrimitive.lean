import NavierStokes.FlatCutoff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Actual primitives of exponential-flat edges

This file studies the integral of `exp (-c / u²) * u⁻ʲ * b u` from zero.
The integrand uses the smooth zero extension from `FlatCutoff`.

In particular, smoothness of the primitive is distinct from smoothness of its
quotient by an exponentially small factor. The statements below keep those
obligations separate.
-/

noncomputable section

open Filter Topology Set MeasureTheory Polynomial
open scoped ContDiff
open NavierStokes.FlatCutoff

namespace NavierStokes.FlatPrimitive

def integrand (c : ℝ) (j : ℕ) (b : ℝ → ℝ) (x : ℝ) : ℝ :=
  (edge c x / x ^ j) * b x

def primitive (c : ℝ) (j : ℕ) (b : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, integrand c j b u

/-- The expected factor `exp(-c/x²) x^(3-j)`, written without truncated
natural subtraction and defined smoothly at zero. -/
def scale (c : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  (edge c x / x ^ j) * x ^ 3

theorem integrand_contDiff {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : ℝ → ℝ} {n : ℕ∞} (hb : ContDiff ℝ n b) :
    ContDiff ℝ n (integrand c j b) :=
  (edge_div_pow_contDiff hc j).mul hb

theorem integrand_continuous {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : ℝ → ℝ} (hb : Continuous b) : Continuous (integrand c j b) :=
  ((edge_div_pow_contDiff hc j : ContDiff ℝ ∞ _).continuous).mul hb

theorem primitive_hasDerivAt {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : ℝ → ℝ} (hb : Continuous b) (x : ℝ) :
    HasDerivAt (primitive c j b) (integrand c j b x) x := by
  have hf := integrand_continuous hc j hb
  exact intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 x)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

theorem primitive_deriv {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : ℝ → ℝ} (hb : Continuous b) :
    deriv (primitive c j b) = integrand c j b := by
  funext x
  exact (primitive_hasDerivAt hc j hb x).deriv

theorem primitive_contDiff {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (primitive c j b) := by
  apply contDiff_infty_iff_deriv.mpr
  constructor
  · exact fun x => (primitive_hasDerivAt hc j hb.continuous x).differentiableAt
  · rw [primitive_deriv hc j hb.continuous]
    exact integrand_contDiff hc j hb

@[simp] theorem primitive_zero (c : ℝ) (j : ℕ) (b : ℝ → ℝ) :
    primitive c j b 0 = 0 := by simp [primitive]

theorem primitive_of_nonpos (c : ℝ) (j : ℕ) (b : ℝ → ℝ)
    {x : ℝ} (hx : x ≤ 0) : primitive c j b x = 0 := by
  unfold primitive
  calc
    (∫ u in (0 : ℝ)..x, integrand c j b u) = ∫ _u in (0 : ℝ)..x, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu0 : u ≤ 0 := (uIcc_of_ge hx ▸ hu).2
      simp [integrand, edge_of_nonpos c hu0]
    _ = 0 := intervalIntegral.integral_zero




theorem edge_hasDerivAt {c : ℝ} (hc : 0 < c) (x : ℝ) :
    HasDerivAt (edge c) (2 * c * edge c x / x ^ 3) x := by
  have h := polynomialEdge_hasDerivAt hc (1 : ℝ[X]) x
  rw [polynomialEdge_one] at h
  convert! h using 1
  simp [polynomialEdge, derivativePolynomial, div_eq_mul_inv, inv_pow]
  ring

theorem scale_contDiff {c : ℝ} (hc : 0 < c) (j : ℕ) {n : ℕ∞} :
    ContDiff ℝ n (scale c j) :=
  (edge_div_pow_contDiff hc j).mul (contDiff_id.pow 3)

@[simp] theorem scale_zero (c : ℝ) (j : ℕ) : scale c j 0 = 0 := by simp [scale]







/-- The natural primitive scale is strictly positive inside the active edge. -/
theorem scale_pos (c : ℝ) (j : ℕ) {x : ℝ} (hx : 0 < x) : 0 < scale c j x :=
  mul_pos (div_pos (edge_pos c hx) (pow_pos hx j)) (pow_pos hx 3)







end NavierStokes.FlatPrimitive

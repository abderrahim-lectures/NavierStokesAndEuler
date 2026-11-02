import NavierStokes.R3.ComparisonSetup
import NavierStokes.R3.CompactEnergy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import NavierStokes.R3.CompactSchwartz
import NavierStokes.R3.FourierTestDerivatives
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Compact tests used in pressure recovery

Real compact smooth tests are embedded in the actual complex Schwartz space.
The differential operators commute with this embedding. The pressure identities
below continue to pair the physical pressure only with compact spatial tests.
-/
/-! Merged from `NavierStokes.R3.ConservativeDifference` (in a section, so its `open`s cannot leak). -/
section
/-!
# Conservative difference equations tested on compactly supported functions

All integrals use Euclidean Lebesgue measure. Compact support is required only
of the test function; the velocities and pressures need no support or decay
assumptions for the identities in this module.
-/


noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace NavierStokesR3.ConservativeDifference

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness
open Comparison (tensorDiff)

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

private theorem infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)

/-- The ordinary scalar Laplacian, with the same coordinate directions as the
vector Laplacian in the Navier--Stokes residual. -/
def scalarLaplacian (f : Space → ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, spatialPartial i (spatialPartial i f) x

theorem scalarLaplacian_contDiff {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (scalarLaplacian f) :=
  ContDiff.sum fun i _ => spatial_partial_contDiff (spatial_partial_contDiff hf i) i

theorem compact_scalarLaplacian {f : Space → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (scalarLaplacian f) := by
  have hh (i : Fin 3) := CompactEnergy.compact_partial
    (CompactEnergy.compact_partial hf i) i
  change HasCompactSupport (fun x => ∑ i : Fin 3, spatialPartial i (spatialPartial i f) x)
  simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] using!
    (hh 0).add ((hh 1).add (hh 2))

theorem partial_mul {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (i : Fin 3) (x : Space) :
    spatialPartial i (fun y => f y * g y) x =
      f x * spatialPartial i g x + g x * spatialPartial i f x := by
  unfold spatialPartial
  rw [fderiv_fun_mul (hf.differentiable (by simp) x)
    (hg.differentiable (by simp) x)]
  rfl

theorem partial_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : Space → V} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : Fin 3) (x : Space) :
    spatialPartial i (fun y => f y - g y) x =
      spatialPartial i f x - spatialPartial i g x := by
  unfold spatialPartial
  rw [fderiv_fun_sub (hf.differentiable (by simp) x)
    (hg.differentiable (by simp) x)]
  rfl

theorem partial_component {f : Space → Space} (hf : ContDiff ℝ ∞ f)
    (i k : Fin 3) (x : Space) :
    spatialPartial i (fun y => f y k) x = spatialPartial i f x k :=
  fderiv_component hf k x (coordinateVector i)

theorem pressureGradient_component (p : PressureField) (t : ℝ)
    (x : Space) (k : Fin 3) :
    pressureGradient p t x k = spatialPartial k (fun y => p (t, y)) x := by
  change (EuclideanSpace.proj k : Space →L[ℝ] ℝ)
    (∑ i : Fin 3, spatialPartial i (fun y => p (t, y)) x • coordinateVector i) = _
  simp [map_sum, coordinateVector]

theorem spatialLaplacian_component {u : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x))) (x : Space) (k : Fin 3) :
    spatialLaplacian u t x k = scalarLaplacian (fun y => u (t, y) k) x := by
  change (EuclideanSpace.proj k : Space →L[ℝ] ℝ)
    (∑ i : Fin 3, spatialPartial i (spatialPartial i (fun y => u (t, y))) x) = _
  rw [map_sum]
  unfold scalarLaplacian
  apply Finset.sum_congr rfl
  intro i _
  rw [show spatialPartial i (fun y => u (t, y) k) =
    (fun y => spatialPartial i (fun z => u (t, z)) y k) from
    funext (fun y => partial_component hu i k y)]
  exact (partial_component (spatial_partial_contDiff hu i) i k x).symm

theorem advection_component {u : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x))) (x : Space) (k : Fin 3) :
    advection u t x k =
      ∑ i : Fin 3, u (t, x) i * spatialPartial i (fun y => u (t, y) k) x := by
  rw [show advection u t x k =
      fderiv ℝ (fun y => u (t, y) k) x (u (t, x)) from
    (fderiv_component hu k x (u (t, x))).symm]
  exact fderiv_apply_eq_sum _ _ _

/-- Divergence of the velocity outer product, before using incompressibility. -/
theorem outerProduct_divergence {u : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x))) (x : Space) (k : Fin 3) :
    (∑ i : Fin 3, spatialPartial i (fun y => u (t, y) k * u (t, y) i) x) =
      u (t, x) k * spatialDivergence u t x + advection u t x k := by
  simp_rw [partial_mul (component_contDiff hu k) (component_contDiff hu _)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← advection_component hu]
  simp_rw [partial_component hu]
  rfl

theorem tensorDiff_contDiff {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x))) (i j : Fin 3) :
    ContDiff ℝ ∞ (tensorDiff u v t i j) :=
  ((component_contDiff hu i).mul (component_contDiff hu j)).sub
    ((component_contDiff hv i).mul (component_contDiff hv j))

theorem tensorDiff_divergence {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (x : Space) (k : Fin 3)
    (hdivu : spatialDivergence u t x = 0)
    (hdivv : spatialDivergence v t x = 0) :
    (∑ i : Fin 3, spatialPartial i (tensorDiff u v t k i) x) =
      advection u t x k - advection v t x k := by
  unfold tensorDiff
  simp_rw [partial_sub ((component_contDiff hu k).mul (component_contDiff hu _))
    ((component_contDiff hv k).mul (component_contDiff hv _))]
  rw [Finset.sum_sub_distrib, outerProduct_divergence hu,
    outerProduct_divergence hv, hdivu, hdivv]
  simp

/-- The exact conservative equation for a difference of smooth solutions
having the same viscosity-one residual. -/
theorem conservative_difference_equation {u v : VelocityField} {p q : PressureField}
    {t : ℝ} {x : Space}
    (hu : ContDiff ℝ ∞ (fun y : Space => u (t, y)))
    (hv : ContDiff ℝ ∞ (fun y : Space => v (t, y)))
    (hp : ContDiff ℝ ∞ (fun y : Space => p (t, y)))
    (hq : ContDiff ℝ ∞ (fun y : Space => q (t, y)))
    (htu : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (htv : DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t)
    (hdivu : spatialDivergence u t x = 0)
    (hdivv : spatialDivergence v t x = 0)
    (hNS : navierStokesResidual u p t x = navierStokesResidual v q t x)
    (k : Fin 3) :
    temporalDerivative (u - v) t x k = spatialLaplacian (u - v) t x k -
      (∑ i : Fin 3, spatialPartial i (tensorDiff u v t k i) x) -
      spatialPartial k (fun y => (p - q) (t, y)) x := by
  have heq := congrArg (fun z : Space => z k)
    (difference_equation hu hv hp hq htu htv hNS)
  have hadv := congrArg (fun z : Space => z k) (advection_difference hu hv x)
  simp only [PiLp.sub_apply, PiLp.add_apply] at heq hadv
  rw [pressureGradient_component] at heq
  rw [tensorDiff_divergence hu hv x k hdivu hdivv]
  linarith

/-- Twice integrating by parts transfers a scalar Laplacian to the compact
test function, regardless of growth of the other smooth function. -/
theorem integral_scalarLaplacian_mul {f ψ : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) :
    (∫ x, scalarLaplacian f x * ψ x) = ∫ x, f x * scalarLaplacian ψ x := by
  have hil (i : Fin 3) :
      Integrable (fun x => spatialPartial i (spatialPartial i f) x * ψ x) :=
    ((spatial_partial_contDiff (spatial_partial_contDiff hf i) i).continuous.mul
      hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left
  have hir (i : Fin 3) :
      Integrable (fun x => f x * spatialPartial i (spatialPartial i ψ) x) :=
    (hf.continuous.mul
      (spatial_partial_contDiff (spatial_partial_contDiff hψ i) i).continuous).integrable_of_hasCompactSupport
      (CompactEnergy.compact_partial (CompactEnergy.compact_partial hcψ i) i).mul_left
  simp only [scalarLaplacian, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hil i),
    integral_finsetSum _ (fun i _ => hir i)]
  apply Finset.sum_congr rfl
  intro i _
  have h1 := CompactEnergy.integral_mul_partial hψ (spatial_partial_contDiff hf i) hcψ i
  have h2 := CompactEnergy.integral_mul_partial (spatial_partial_contDiff hψ i) hf
    (CompactEnergy.compact_partial hcψ i) i
  change (∫ x, ψ x * spatialPartial i (spatialPartial i f) x) =
    -(∫ x, spatialPartial i f x * spatialPartial i ψ x) at h1
  change (∫ x, spatialPartial i ψ x * spatialPartial i f x) =
    -(∫ x, f x * spatialPartial i (spatialPartial i ψ) x) at h2
  calc
    _ = ∫ x, ψ x * spatialPartial i (spatialPartial i f) x := by
      exact integral_congr_ae (Eventually.of_forall (fun x => mul_comm _ _))
    _ = -(∫ x, spatialPartial i f x * spatialPartial i ψ x) := h1
    _ = -(∫ x, spatialPartial i ψ x * spatialPartial i f x) := by
      congr 1
      exact integral_congr_ae (Eventually.of_forall (fun x => mul_comm _ _))
    _ = -(-(∫ x, f x * spatialPartial i (spatialPartial i ψ) x)) := congrArg Neg.neg h2
    _ = _ := neg_neg _

theorem integrable_mul_test {f ψ : Space → ℝ} (hf : Continuous f)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun x => f x * ψ x) :=
  (hf.mul hψ).integrable_of_hasCompactSupport hcψ.mul_left

theorem integral_tensorDiff_divergence_mul {u v : VelocityField} {t : ℝ}
    {ψ : Space → ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, (∑ i : Fin 3, spatialPartial i (tensorDiff u v t k i) x) * ψ x) =
      -(∑ i : Fin 3, ∫ x, tensorDiff u v t k i x * spatialPartial i ψ x) := by
  have hi (i : Fin 3) :
      Integrable (fun x => spatialPartial i (tensorDiff u v t k i) x * ψ x) :=
    integrable_mul_test (spatial_partial_contDiff (tensorDiff_contDiff hu hv k i) i).continuous
      hψ.continuous hcψ
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hi i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [spatialPartial, mul_comm] using
    CompactEnergy.integral_mul_partial hψ (tensorDiff_contDiff hu hv k i) hcψ i

/-- Testing the conservative equation against a compact scalar test transfers
all spatial derivatives off the velocity difference and tensor difference.
No global integrability assumption is imposed on either pressure. -/
theorem weak_pressure_gradient {u v : VelocityField} {p q : PressureField}
    {t : ℝ} {ψ : Space → ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t, x)))
    (htu : ∀ x, DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (htv : ∀ x, DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t)
    (hdivu : ∀ x, spatialDivergence u t x = 0)
    (hdivv : ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ x, navierStokesResidual u p t x = navierStokesResidual v q t x)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) =
      (∫ x, (u - v) (t, x) k * scalarLaplacian ψ x) -
      (∫ x, temporalDerivative (u - v) t x k * ψ x) +
      ∑ i : Fin 3, ∫ x, tensorDiff u v t k i x * spatialPartial i ψ x := by
  have hL : Continuous (fun x => spatialLaplacian (u - v) t x k) :=
    (component_contDiff (spatialLaplacian_contDiff (hu.sub hv)) k).continuous
  have hG : Continuous (fun x => ∑ i : Fin 3, spatialPartial i (tensorDiff u v t k i) x) :=
    (ContDiff.sum fun i _ => spatial_partial_contDiff (tensorDiff_contDiff hu hv k i) i).continuous
  have hP : Continuous (spatialPartial k (fun y => (p - q) (t, y))) :=
    (spatial_partial_contDiff (hp.sub hq) k).continuous
  have hdt : Continuous (fun x => temporalDerivative (u - v) t x k) := by
    have heq : (fun x => temporalDerivative (u - v) t x k) =
        (fun x => spatialLaplacian (u - v) t x k -
          (∑ i : Fin 3, spatialPartial i (tensorDiff u v t k i) x) -
          spatialPartial k (fun y => (p - q) (t, y)) x) :=
      funext fun x => conservative_difference_equation hu hv hp hq (htu x) (htv x)
        (hdivu x) (hdivv x) (hNS x) k
    rw [heq]
    exact (hL.sub hG).sub hP
  have hiL := integrable_mul_test hL hψ.continuous hcψ
  have hiG := integrable_mul_test hG hψ.continuous hcψ
  have hidt := integrable_mul_test hdt hψ.continuous hcψ
  have hiLD : Integrable (fun x => spatialLaplacian (u - v) t x k * ψ x -
      temporalDerivative (u - v) t x k * ψ x) := hiL.sub hidt
  have hpoint : (fun x => spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) =
      (fun x => spatialLaplacian (u - v) t x k * ψ x -
        temporalDerivative (u - v) t x k * ψ x -
        (∑ i : Fin 3, spatialPartial i (tensorDiff u v t k i) x) * ψ x) := by
    funext x
    have h := conservative_difference_equation hu hv hp hq (htu x) (htv x)
      (hdivu x) (hdivv x) (hNS x) k
    have hpEq : spatialPartial k (fun y => (p - q) (t, y)) x =
        spatialLaplacian (u - v) t x k - temporalDerivative (u - v) t x k -
        (∑ i : Fin 3, spatialPartial i (tensorDiff u v t k i) x) := by linarith
    rw [hpEq]
    ring
  have hLap : (∫ x, spatialLaplacian (u - v) t x k * ψ x) =
      ∫ x, (u - v) (t, x) k * scalarLaplacian ψ x := by
    simp_rw [spatialLaplacian_component (u := u - v) (t := t) (hu.sub hv)]
    exact integral_scalarLaplacian_mul (component_contDiff (hu.sub hv) k) hψ hcψ
  rw [hpoint, integral_sub hiLD hiG, integral_sub hiL hidt,
    hLap, integral_tensorDiff_divergence_mul hu hv hψ hcψ k]
  ring

/-- A slab version of the compact weak identity with time differentiability
supplied by joint smoothness. -/
theorem weak_pressure_gradient_on_slab {a b t : ℝ} {u v : VelocityField}
    {p q : PressureField} {ψ : Space → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab a b))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab a b))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab a b))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab a b))
    (ht : t ∈ Ioo a b)
    (hdivu : ∀ x, spatialDivergence u t x = 0)
    (hdivv : ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ x, navierStokesResidual u p t x = navierStokesResidual v q t x)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) =
      (∫ x, (u - v) (t, x) k * scalarLaplacian ψ x) -
      (∫ x, temporalDerivative (u - v) t x k * ψ x) +
      ∑ i : Fin 3, ∫ x, tensorDiff u v t k i x * spatialPartial i ψ x := by
  exact weak_pressure_gradient (spatial_smooth hu (Ioo_subset_Icc_self ht))
    (spatial_smooth hv (Ioo_subset_Icc_self ht)) (spatial_smooth hp (Ioo_subset_Icc_self ht))
    (spatial_smooth hq (Ioo_subset_Icc_self ht))
    (fun x => time_differentiable_at_interior hu ht x)
    (fun x => time_differentiable_at_interior hv ht x) hdivu hdivv hNS hψ hcψ k

theorem partial_partial_eq_fderiv {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (i j : Fin 3) (x : Space) :
    spatialPartial i (spatialPartial j f) x =
      fderiv ℝ (fderiv ℝ f) x (coordinateVector i) (coordinateVector j) := by
  have hdf := (hf.fderiv_right infty_add_one_le).differentiable (by simp) x
  change fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector j)) x (coordinateVector i) = _
  rw [fderiv_clm_apply hdf (differentiableAt_const (coordinateVector j))]
  simp

theorem partial_comm {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (i j : Fin 3) (x : Space) :
    spatialPartial i (spatialPartial j f) x =
      spatialPartial j (spatialPartial i f) x := by
  rw [partial_partial_eq_fderiv hf, partial_partial_eq_fderiv hf]
  exact ((hf.of_le (nat_le_infty 2)).contDiffAt.isSymmSndFDerivAt (by simp)) _ _

theorem partial_sum {f : Fin 3 → Space → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (k : Fin 3) (x : Space) :
    spatialPartial k (fun y => ∑ i : Fin 3, f i y) x =
      ∑ i : Fin 3, spatialPartial k (f i) x := by
  unfold spatialPartial
  rw [fderiv_fun_sum (fun i _ => (hf i).differentiable (by simp) x)]
  simp

theorem partial_scalarLaplacian {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (k : Fin 3) (x : Space) :
    spatialPartial k (scalarLaplacian f) x = scalarLaplacian (spatialPartial k f) x := by
  change spatialPartial k (fun y => ∑ i : Fin 3,
    spatialPartial i (spatialPartial i f) y) x = _
  rw [partial_sum (f := fun i => spatialPartial i (spatialPartial i f))
    (fun i => spatial_partial_contDiff (spatial_partial_contDiff hf i) i)]
  unfold scalarLaplacian
  apply Finset.sum_congr rfl
  intro i _
  rw [partial_comm (f := spatialPartial i f) (spatial_partial_contDiff hf i) k i x]
  exact congrArg (fun g : Space → ℝ => spatialPartial i g x)
    (funext (fun y => partial_comm hf k i y))

/-- A compact scalar test detects the ordinary divergence, even when the
vector field has no compact support. -/
theorem integral_divergence_free_test {w : Space → Space} {ψ : Space → ℝ}
    (hw : ContDiff ℝ ∞ w) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hdiv : ∀ x, (∑ i : Fin 3, spatialPartial i w x i) = 0) :
    (∑ i : Fin 3, ∫ x, w x i * spatialPartial i ψ x) = 0 := by
  have hi (i : Fin 3) : Integrable (fun x => ψ x * spatialPartial i w x i) :=
    (hψ.continuous.mul
      (component_contDiff (spatial_partial_contDiff hw i) i).continuous).integrable_of_hasCompactSupport
      hcψ.mul_right
  have hparts (i : Fin 3) : (∫ x, w x i * spatialPartial i ψ x) =
      -(∫ x, ψ x * spatialPartial i w x i) := by
    have h := CompactEnergy.integral_mul_partial hψ (component_contDiff hw i) hcψ i
    simp_rw [partial_component hw] at h
    linarith
  rw [Finset.sum_congr rfl (fun i _ => hparts i), Finset.sum_neg_distrib]
  have hsum : (∫ x, ψ x * ∑ i : Fin 3, spatialPartial i w x i) =
      ∑ i : Fin 3, ∫ x, ψ x * spatialPartial i w x i := by
    simp only [Finset.mul_sum]
    exact integral_finsetSum _ (fun i _ => hi i)
  rw [← hsum]
  simp only [hdiv, mul_zero, integral_zero, neg_zero]

/-- Differentiation of one component paired with a fixed compact spatial
test. The compact support supplies a common spatial domain for differentiation. -/
theorem component_test_hasDerivAt {a b t : ℝ} {w : VelocityField} {ψ : Space → ℝ}
    (hw : ContDiffOn ℝ ∞ w (Comparison.slab a b)) (ht : t ∈ Ioo a b)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    HasDerivAt (fun s => ∫ x, w (s, x) k * ψ x)
      (∫ x, temporalDerivative w t x k * ψ x) t := by
  have hF : ContDiffOn ℝ 1 (fun z : SpaceTime => w z k * ψ z.2)
      (Icc a b ×ˢ univ) :=
    (((EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn hw).mul
      (hψ.comp contDiff_snd).contDiffOn).of_le (nat_le_infty 1)
  refine CompactTimeIntegral.hasDerivAt_integral_of_contDiffOn_of_hasDerivAt
    hcψ hF ?_ ht ?_
  · intro s hs x hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  · intro x
    have htime : HasDerivAt (fun s => w (s, x)) (temporalDerivative w t x) t :=
      (time_differentiable_at_interior hw ht x).hasDerivAt
    exact ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t htime).mul_const (ψ x)

/-- The time derivative has zero distributional divergence. This follows by
differentiating a compact pairing that is identically zero on the time interval. -/
theorem integral_time_derivative_divergence_free {a b t : ℝ} {w : VelocityField}
    {ψ : Space → ℝ}
    (hw : ContDiffOn ℝ ∞ w (Comparison.slab a b)) (ht : t ∈ Ioo a b)
    (hdiv : ∀ s ∈ Ioo a b, ∀ x, spatialDivergence w s x = 0)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    (∑ k : Fin 3, ∫ x, temporalDerivative w t x k * spatialPartial k ψ x) = 0 := by
  have hderiv : HasDerivAt
      (fun s => ∑ k : Fin 3, ∫ x, w (s, x) k * spatialPartial k ψ x)
      (∑ k : Fin 3, ∫ x, temporalDerivative w t x k * spatialPartial k ψ x) t :=
    HasDerivAt.fun_sum fun k _ => component_test_hasDerivAt hw ht
      (spatial_partial_contDiff hψ k) (CompactEnergy.compact_partial hcψ k) k
  have heq : (fun s => ∑ k : Fin 3, ∫ x, w (s, x) k * spatialPartial k ψ x) =ᶠ[𝓝 t]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact integral_divergence_free_test (spatial_smooth hw (Ioo_subset_Icc_self hs))
      hψ hcψ (hdiv s hs)
  exact (hderiv.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const t (0 : ℝ))

theorem integral_gradient_pairing {f ψ : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    (∑ k : Fin 3, ∫ x, spatialPartial k f x * spatialPartial k ψ x) =
      -(∫ x, f x * scalarLaplacian ψ x) := by
  have hparts (k : Fin 3) :
      (∫ x, spatialPartial k f x * spatialPartial k ψ x) =
        -(∫ x, f x * spatialPartial k (spatialPartial k ψ) x) := by
    have h := CompactEnergy.integral_mul_partial (spatial_partial_contDiff hψ k) hf
      (CompactEnergy.compact_partial hcψ k) k
    change (∫ x, spatialPartial k ψ x * spatialPartial k f x) =
      -(∫ x, f x * spatialPartial k (spatialPartial k ψ) x) at h
    calc
      _ = ∫ x, spatialPartial k ψ x * spatialPartial k f x :=
        integral_congr_ae (Eventually.of_forall (fun x => mul_comm _ _))
      _ = _ := h
  have hi (k : Fin 3) :
      Integrable (fun x => f x * spatialPartial k (spatialPartial k ψ) x) :=
    integrable_mul_test hf.continuous
      (spatial_partial_contDiff (spatial_partial_contDiff hψ k) k).continuous
      (CompactEnergy.compact_partial (CompactEnergy.compact_partial hcψ k) k)
  rw [Finset.sum_congr rfl (fun k _ => hparts k), Finset.sum_neg_distrib]
  congr 1
  simp only [scalarLaplacian, Finset.mul_sum]
  exact (integral_finsetSum _ (fun k _ => hi k)).symm

/-- The pressure difference solves the compact-test Poisson equation obtained
from the actual Navier--Stokes residual and incompressibility. No pressure
normalization, growth hypothesis, or integrability at infinity is used. -/
theorem weak_pressure_poisson {a b t : ℝ} {u v : VelocityField}
    {p q : PressureField} {ψ : Space → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab a b))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab a b))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab a b))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab a b))
    (ht : t ∈ Ioo a b)
    (hdivu : ∀ s ∈ Ioo a b, ∀ x, spatialDivergence u s x = 0)
    (hdivv : ∀ s ∈ Ioo a b, ∀ x, spatialDivergence v s x = 0)
    (hNS : ∀ x, navierStokesResidual u p t x = navierStokesResidual v q t x)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    (∫ x, (p - q) (t, x) * scalarLaplacian ψ x) =
      -(∑ k : Fin 3, ∑ i : Fin 3,
        ∫ x, tensorDiff u v t k i x * spatialPartial i (spatialPartial k ψ) x) := by
  have hw : ContDiffOn ℝ ∞ (u - v) (Comparison.slab a b) := hu.sub hv
  have hwspace := spatial_smooth hw (Ioo_subset_Icc_self ht)
  have hdivw : ∀ s ∈ Ioo a b, ∀ x, spatialDivergence (u - v) s x = 0 := by
    intro s hs x
    rw [spatialDivergence_sub (spatial_smooth hu (Ioo_subset_Icc_self hs))
      (spatial_smooth hv (Ioo_subset_Icc_self hs)), hdivu s hs, hdivv s hs, sub_self]
  have hL : (∑ k : Fin 3, ∫ x, (u - v) (t, x) k *
      scalarLaplacian (spatialPartial k ψ) x) = 0 := by
    simp_rw [← partial_scalarLaplacian hψ]
    exact integral_divergence_free_test hwspace (scalarLaplacian_contDiff hψ)
      (compact_scalarLaplacian hcψ) (hdivw t ht)
  have hT := integral_time_derivative_divergence_free hw ht hdivw hψ hcψ
  have hsum : (∑ k : Fin 3, ∫ x,
      spatialPartial k (fun y => (p - q) (t, y)) x * spatialPartial k ψ x) =
      ∑ k : Fin 3, ((∫ x, (u - v) (t, x) k * scalarLaplacian (spatialPartial k ψ) x) -
        (∫ x, temporalDerivative (u - v) t x k * spatialPartial k ψ x) +
        ∑ i : Fin 3, ∫ x, tensorDiff u v t k i x * spatialPartial i (spatialPartial k ψ) x) := by
    apply Finset.sum_congr rfl
    intro k _
    exact weak_pressure_gradient_on_slab hu hv hp hq ht (hdivu t ht) (hdivv t ht) hNS
      (spatial_partial_contDiff hψ k) (CompactEnergy.compact_partial hcψ k) k
  rw [integral_gradient_pairing (f := fun y => (p - q) (t, y))
      ((spatial_smooth hp (Ioo_subset_Icc_self ht)).sub (spatial_smooth hq (Ioo_subset_Icc_self ht)))
      hψ hcψ, Finset.sum_add_distrib, Finset.sum_sub_distrib, hL, hT] at hsum
  linarith

end NavierStokesR3.ConservativeDifference
end

/-! Merged from `NavierStokes.R3.PressureTemporalIdentity` (in a section, so its `open`s cannot leak). -/
section
/-!
# Compact time tests of the conservative pressure identity

The temporal test has topological support inside the open time interval. The
spatial test is smooth and compactly supported. Consequently all pairings are
ordinary Lebesgue integrals even when the pressure grows at spatial infinity.
-/


noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace NavierStokesR3.PressureTemporalIdentity

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness
open ConservativeDifference
open Comparison (tensorDiff)

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

private theorem infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)

/-- A time cutoff supported in an open set turns a continuous function on
that set into a globally continuous product, regardless of its values outside. -/
theorem continuous_cutoff_mul {a F : ℝ → ℝ} {s : Set ℝ}
    (ha : Continuous a) (hF : ContinuousOn F s) (hs : IsOpen s)
    (hsupp : tsupport a ⊆ s) : Continuous (fun t => a t * F t) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t ∈ tsupport a
  · exact ha.continuousAt.mul ((hF t (hsupp ht)).continuousAt (hs.mem_nhds (hsupp ht)))
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds ht] with r hr
    rw [image_eq_zero_of_notMem_tsupport hr, zero_mul]

theorem component_test_continuousOn {T : ℝ} {w : VelocityField} {ψ : Space → ℝ}
    (hw : ContinuousOn w (Comparison.slab 0 T))
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    ContinuousOn (fun t => ∫ x, w (t, x) k * ψ x) (Icc 0 T) := by
  have hF : ContinuousOn (fun z : SpaceTime => w z k * ψ z.2) (Icc 0 T ×ˢ univ) :=
    ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_continuousOn hw).mul
      (hψ.comp continuous_snd).continuousOn
  apply CompactTimeIntegral.continuousOn_integral hcψ hF
  intro t ht x hx
  rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

theorem component_time_test_continuousOn {T : ℝ} {w : VelocityField} {ψ : Space → ℝ}
    (hw : ContDiffOn ℝ ∞ w (Comparison.slab 0 T))
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    ContinuousOn (fun t => ∫ x, temporalDerivative w t x k * ψ x) (Ioo 0 T) := by
  have htime : ContinuousOn (fun z : SpaceTime => temporalDerivative w z.1 z.2)
      (Ioo 0 T ×ˢ univ) := by
    simpa only [temporalDerivative, deriv] using
      CompactTimeIntegral.continuousOn_timeDeriv_of_contDiffOn (hw.of_le (nat_le_infty 1))
  have hF : ContinuousOn (fun z : SpaceTime => temporalDerivative w z.1 z.2 k * ψ z.2)
      (Ioo 0 T ×ˢ univ) :=
    ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_continuousOn htime).mul
      (hψ.comp continuous_snd).continuousOn
  apply CompactTimeIntegral.continuousOn_integral hcψ hF
  intro t ht x hx
  rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

theorem tensor_test_continuousOn {T : ℝ} {u v : VelocityField} {ψ : Space → ℝ}
    (hu : ContinuousOn u (Comparison.slab 0 T))
    (hv : ContinuousOn v (Comparison.slab 0 T))
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (i j : Fin 3) :
    ContinuousOn (fun t => ∫ x, tensorDiff u v t i j x * ψ x) (Icc 0 T) := by
  have hucomp (k : Fin 3) : ContinuousOn (fun z : SpaceTime => u z k) (Comparison.slab 0 T) :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_continuousOn hu
  have hvcomp (k : Fin 3) : ContinuousOn (fun z : SpaceTime => v z k) (Comparison.slab 0 T) :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_continuousOn hv
  have hF : ContinuousOn (fun z : SpaceTime => tensorDiff u v z.1 i j z.2 * ψ z.2)
      (Icc 0 T ×ˢ univ) :=
    (((hucomp i).mul (hucomp j)).sub ((hvcomp i).mul (hvcomp j))).mul
      (hψ.comp continuous_snd).continuousOn
  apply CompactTimeIntegral.continuousOn_integral hcψ hF
  intro t ht x hx
  rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

/-- Integration by parts with a temporal test supported away from both
endpoints. Only the cutoff-weighted derivative needs to be integrable. -/
theorem compact_time_integration_by_parts {T : ℝ} {a F D : ℝ → ℝ}
    (hT : 0 < T) (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    (hF : ContinuousOn F (Icc 0 T)) (hD : ContinuousOn D (Ioo 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt F (D t) t) :
    (∫ t in (0 : ℝ)..T, a t * D t) = -(∫ t in (0 : ℝ)..T, deriv a t * F t) := by
  have hda : Continuous (deriv a) := by
    change Continuous (fun t => fderiv ℝ a t 1)
    exact ((ha.fderiv_right infty_add_one_le).clm_apply contDiff_const).continuous
  have hi₁ : IntervalIntegrable (fun t => deriv a t * F t) volume 0 T :=
    ContinuousOn.intervalIntegrable_of_Icc hT.le (hda.continuousOn.mul hF)
  have hi₂ : IntervalIntegrable (fun t => a t * D t) volume 0 T :=
    (continuous_cutoff_mul ha.continuous hD isOpen_Ioo hsupp).intervalIntegrable _ _
  have hisum : IntervalIntegrable (fun t => deriv a t * F t + a t * D t) volume 0 T :=
    hi₁.add hi₂
  have hprod : ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun r => a r * F r) (deriv a t * F t + a t * D t) t := by
    intro t ht
    exact ((ha.differentiable (by simp) t).hasDerivAt).mul (hderiv t ht)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le
    (ha.continuous.continuousOn.mul hF) hprod hisum
  have ha0 : a 0 = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h
    exact (lt_irrefl 0) (hsupp h).1)
  have haT : a T = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h
    exact (lt_irrefl T) (hsupp h).2)
  rw [intervalIntegral.integral_add hi₁ hi₂, Pi.mul_apply, Pi.mul_apply, ha0, haT, zero_mul, zero_mul, sub_self] at hFTC
  linarith

/-- The compact pressure-gradient identity integrated against a time test.
Both derivatives of the velocity have transferred to the two test functions. -/
theorem pressure_time_identity_interval {T : ℝ} {u v : VelocityField}
    {p q : PressureField} {a : ℝ → ℝ} {ψ : Space → ℝ}
    (hT : 0 < T)
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hdivu : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence u t x = 0)
    (hdivv : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo 0 T, ∀ x,
      navierStokesResidual u p t x = navierStokesResidual v q t x)
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ t in (0 : ℝ)..T, a t *
      (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x)) =
      (∫ t in (0 : ℝ)..T, a t * (∫ x, (u - v) (t, x) k * scalarLaplacian ψ x)) +
      (∫ t in (0 : ℝ)..T, deriv a t * (∫ x, (u - v) (t, x) k * ψ x)) +
      (∫ t in (0 : ℝ)..T, a t *
        (∑ i : Fin 3, ∫ x, tensorDiff u v t k i x * spatialPartial i ψ x)) := by
  let W : ℝ → ℝ := fun t => ∫ x, (u - v) (t, x) k * ψ x
  let D : ℝ → ℝ := fun t => ∫ x, temporalDerivative (u - v) t x k * ψ x
  let L : ℝ → ℝ := fun t => ∫ x, (u - v) (t, x) k * scalarLaplacian ψ x
  let G : ℝ → ℝ := fun t => ∑ i : Fin 3,
    ∫ x, tensorDiff u v t k i x * spatialPartial i ψ x
  let P : ℝ → ℝ := fun t => ∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x
  have hW : ContinuousOn W (Icc 0 T) :=
    component_test_continuousOn (hu.sub hv).continuousOn hψ.continuous hcψ k
  have hD : ContinuousOn D (Ioo 0 T) :=
    component_time_test_continuousOn (hu.sub hv) hψ.continuous hcψ k
  have hL : ContinuousOn L (Icc 0 T) :=
    component_test_continuousOn (hu.sub hv).continuousOn
      (scalarLaplacian_contDiff hψ).continuous (compact_scalarLaplacian hcψ) k
  have hG : ContinuousOn G (Icc 0 T) :=
    continuousOn_finsetSum _ (fun i _ => tensor_test_continuousOn hu.continuousOn hv.continuousOn
      (spatial_partial_contDiff hψ i).continuous (CompactEnergy.compact_partial hcψ i) k i)
  have hparts : (∫ t in (0 : ℝ)..T, a t * D t) =
      -(∫ t in (0 : ℝ)..T, deriv a t * W t) :=
    compact_time_integration_by_parts hT ha hsupp hW hD
      (fun t ht => component_test_hasDerivAt (hu.sub hv) ht hψ hcψ k)
  have hiL : IntervalIntegrable (fun t => a t * L t) volume 0 T :=
    ContinuousOn.intervalIntegrable_of_Icc hT.le (ha.continuous.continuousOn.mul hL)
  have hiD : IntervalIntegrable (fun t => a t * D t) volume 0 T :=
    (continuous_cutoff_mul ha.continuous hD isOpen_Ioo hsupp).intervalIntegrable _ _
  have hiG : IntervalIntegrable (fun t => a t * G t) volume 0 T :=
    ContinuousOn.intervalIntegrable_of_Icc hT.le (ha.continuous.continuousOn.mul hG)
  have hiLD : IntervalIntegrable (fun t => a t * L t - a t * D t) volume 0 T := hiL.sub hiD
  have hpoint : (fun t => a t * P t) = (fun t => a t * L t - a t * D t + a t * G t) := by
    funext t
    by_cases ht : t ∈ Ioo 0 T
    · have h := weak_pressure_gradient_on_slab hu hv hp hq ht (hdivu t ht) (hdivv t ht)
        (hNS t ht) hψ hcψ k
      change P t = L t - D t + G t at h
      rw [h]
      ring
    · have hat : a t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (hsupp h))
      simp only [hat, zero_mul, sub_zero, add_zero]
  change (∫ t in (0 : ℝ)..T, a t * P t) =
    (∫ t in (0 : ℝ)..T, a t * L t) + (∫ t in (0 : ℝ)..T, deriv a t * W t) +
      (∫ t in (0 : ℝ)..T, a t * G t)
  rw [hpoint, intervalIntegral.integral_add hiLD hiG, intervalIntegral.integral_sub hiL hiD,
    hparts]
  ring

/-- The same identity as an ordinary set integral over the closed time
interval, convenient for subsequent Fubini and norm estimates. -/
theorem pressure_time_identity {T : ℝ} {u v : VelocityField}
    {p q : PressureField} {a : ℝ → ℝ} {ψ : Space → ℝ}
    (hT : 0 < T)
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hdivu : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence u t x = 0)
    (hdivv : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo 0 T, ∀ x,
      navierStokesResidual u p t x = navierStokesResidual v q t x)
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ t in Icc (0 : ℝ) T, a t *
      (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x)) =
      (∫ t in Icc (0 : ℝ) T, a t * (∫ x, (u - v) (t, x) k * scalarLaplacian ψ x)) +
      (∫ t in Icc (0 : ℝ) T, deriv a t * (∫ x, (u - v) (t, x) k * ψ x)) +
      (∫ t in Icc (0 : ℝ) T, a t *
        (∑ i : Fin 3, ∫ x, tensorDiff u v t k i x * spatialPartial i ψ x)) := by
  have h := pressure_time_identity_interval hT hu hv hp hq hdivu hdivv hNS ha hsupp hψ hcψ k
  simpa only [intervalIntegral.integral_of_le hT.le, ← integral_Icc_eq_integral_Ioc] using h

end NavierStokesR3.PressureTemporalIdentity
end



noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace NavierStokesR3.PressureRecovery

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness
open Comparison (ComplexTest tensorDiff)
open ConservativeDifference HarmonicTestFunctionals

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

/-- The canonical complex Schwartz test associated to a real compact test. -/
def realTest (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    ComplexTest :=
  CompactSchwartz.ofCompactSupport (fun x => (ψ x : ℂ))
    (Complex.ofRealCLM.contDiff.comp hψ)
    (hcψ.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp))

@[simp] theorem realTest_apply (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (x : Space) : realTest ψ hψ hcψ x = (ψ x : ℂ) := rfl


theorem partial_ofReal {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (i : Fin 3) (x : Space) :
    spatialPartial i (fun y => (ψ y : ℂ)) x = ((spatialPartial i ψ x : ℝ) : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt.comp x
    (hψ.differentiable (by simp) x).hasFDerivAt).fderiv
  exact congrArg (fun L : Space →L[ℝ] ℂ => L (coordinateVector i)) h

@[simp] theorem partialCLM_realTest (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (i : Fin 3) :
    partialCLM i (realTest ψ hψ hcψ) =
      realTest (spatialPartial i ψ) (spatial_partial_contDiff hψ i)
        (CompactEnergy.compact_partial hcψ i) := by
  ext x
  exact partial_ofReal hψ i x

@[simp] theorem laplacianCLM_realTest (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) :
    laplacianCLM (realTest ψ hψ hcψ) =
      realTest (scalarLaplacian ψ) (scalarLaplacian_contDiff hψ) (compact_scalarLaplacian hcψ) := by
  ext x
  rw [laplacianCLM_apply, realTest_apply]
  simp only [scalarLaplacian, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  change spatialPartial i (fun y => spatialPartial i (fun z => (ψ z : ℂ)) y) x = _
  have he : (fun y => spatialPartial i (fun z => (ψ z : ℂ)) y) =
      (fun y => ((spatialPartial i ψ y : ℝ) : ℂ)) := funext (partial_ofReal hψ i)
  rw [he]
  exact partial_ofReal (spatial_partial_contDiff hψ i) i x

theorem partial_laplacian_realTest (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    partialCLM k (laplacianCLM (realTest ψ hψ hcψ)) =
      laplacianCLM (partialCLM k (realTest ψ hψ hcψ)) := by
  rw [laplacianCLM_realTest ψ hψ hcψ,
    partialCLM_realTest (scalarLaplacian ψ) (scalarLaplacian_contDiff hψ)
      (compact_scalarLaplacian hcψ) k,
    partialCLM_realTest ψ hψ hcψ k,
    laplacianCLM_realTest (spatialPartial k ψ) (spatial_partial_contDiff hψ k)
      (CompactEnergy.compact_partial hcψ k)]
  ext x
  exact congrArg Complex.ofReal (partial_scalarLaplacian hψ k x)

/-- A compact complex Schwartz test splits into two compact real tests. -/
theorem compact_test_decomposition (ψ : ComplexTest)
    (hcψ : HasCompactSupport (ψ : Space → ℂ)) :
    ψ = realTest (fun x => (ψ x).re) (Complex.reCLM.contDiff.comp ψ.smooth')
      (hcψ.comp_left (g := Complex.re) (by simp)) +
      Complex.I • realTest (fun x => (ψ x).im) (Complex.imCLM.contDiff.comp ψ.smooth')
        (hcψ.comp_left (g := Complex.im) (by simp)) := by
  ext x
  change ψ x = ((ψ x).re : ℂ) + Complex.I * ((ψ x).im : ℂ)
  apply Complex.ext <;> simp

/-- Compact harmonicity of a complex linear functional can be verified using
real scalar tests alone. -/
theorem compact_harmonic_of_real (F : ComplexTest →ₗ[ℂ] ℂ)
    (hreal : ∀ (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ),
      F (laplacianCLM (realTest ψ hψ hcψ)) = 0) :
    ∀ ψ : ComplexTest, HasCompactSupport (ψ : Space → ℂ) → F (laplacianCLM ψ) = 0 := by
  intro ψ hcψ
  rw [compact_test_decomposition ψ hcψ]
  simp only [map_add, map_smul]
  rw [hreal (fun x => (ψ x).re) (Complex.reCLM.contDiff.comp ψ.smooth')
      (hcψ.comp_left (g := Complex.re) (by simp)),
    hreal (fun x => (ψ x).im) (Complex.imCLM.contDiff.comp ψ.smooth')
      (hcψ.comp_left (g := Complex.im) (by simp))]
  simp only [smul_zero, add_zero]

/-- The differentiated pressure Poisson equation, still tested only against
compact smooth functions. The derivative order agrees with the Riesz symbol. -/
theorem gradient_poisson_test {T t : ℝ} {u v : VelocityField}
    {p q : PressureField} {ψ : Space → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (ht : t ∈ Ioo 0 T)
    (hdivu : ∀ s ∈ Ioo 0 T, ∀ x, spatialDivergence u s x = 0)
    (hdivv : ∀ s ∈ Ioo 0 T, ∀ x, spatialDivergence v s x = 0)
    (hNS : ∀ x, navierStokesResidual u p t x = navierStokesResidual v q t x)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * scalarLaplacian ψ x) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x, tensorDiff u v t i j x *
          spatialPartial i (spatialPartial j (spatialPartial k ψ)) x := by
  have hπ := (spatial_smooth hp (Ioo_subset_Icc_self ht)).sub
    (spatial_smooth hq (Ioo_subset_Icc_self ht))
  have hibp := CompactEnergy.integral_mul_partial (scalarLaplacian_contDiff hψ) hπ
    (compact_scalarLaplacian hcψ) k
  change (∫ x, scalarLaplacian ψ x * spatialPartial k (fun y => (p - q) (t, y)) x) =
    -(∫ x, (p - q) (t, x) * spatialPartial k (scalarLaplacian ψ) x) at hibp
  have hpoisson := weak_pressure_poisson (ψ := spatialPartial k ψ) hu hv hp hq ht hdivu hdivv hNS
    (spatial_partial_contDiff hψ k) (CompactEnergy.compact_partial hcψ k)
  calc
    _ = -(∫ x, (p - q) (t, x) * spatialPartial k (scalarLaplacian ψ) x) := by
      calc
        _ = ∫ x, scalarLaplacian ψ x * spatialPartial k (fun y => (p - q) (t, y)) x :=
          integral_congr_ae (Eventually.of_forall (fun x => mul_comm _ _))
        _ = _ := hibp
    _ = -(∫ x, (p - q) (t, x) * scalarLaplacian (spatialPartial k ψ) x) := by
      simp only [partial_scalarLaplacian hψ]
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x, tensorDiff u v t i j x *
          spatialPartial j (spatialPartial i (spatialPartial k ψ)) x := by
      rw [hpoisson, neg_neg]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards [] with x
      rw [partial_comm (f := spatialPartial k ψ) (spatial_partial_contDiff hψ k) j i x]

/-- The compact physical pressure-gradient pairing is continuous at interior
times. Joint smoothness and the local equation suffice. -/
theorem pressure_gradient_pairing_continuousOn {T : ℝ} {u v : VelocityField}
    {p q : PressureField} {ψ : Space → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hdivu : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence u t x = 0)
    (hdivv : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo 0 T, ∀ x,
      navierStokesResidual u p t x = navierStokesResidual v q t x)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    ContinuousOn (fun t => ∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x)
      (Ioo 0 T) := by
  have hL := PressureTemporalIdentity.component_test_continuousOn (hu.sub hv).continuousOn
    (scalarLaplacian_contDiff hψ).continuous (compact_scalarLaplacian hcψ) k
  have hD := PressureTemporalIdentity.component_time_test_continuousOn (hu.sub hv)
    hψ.continuous hcψ k
  have hG : ContinuousOn (fun t => ∑ i : Fin 3,
      ∫ x, tensorDiff u v t k i x * spatialPartial i ψ x) (Icc 0 T) :=
    continuousOn_finsetSum _ (fun i _ => PressureTemporalIdentity.tensor_test_continuousOn
      hu.continuousOn hv.continuousOn (spatial_partial_contDiff hψ i).continuous
        (CompactEnergy.compact_partial hcψ i) k i)
  apply ((hL.mono Ioo_subset_Icc_self).sub hD |>.add (hG.mono Ioo_subset_Icc_self)).congr
  intro t ht
  exact weak_pressure_gradient_on_slab hu hv hp hq ht (hdivu t ht) (hdivv t ht) (hNS t ht)
    hψ hcψ k

end NavierStokesR3.PressureRecovery

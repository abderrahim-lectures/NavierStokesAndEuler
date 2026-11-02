import NavierStokes.SpatialCurl
import NavierStokes.ResidualStability
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NavierStokes.JetBounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Real oscillatory curl realization

The potential and curl below use actual Euclidean spatial derivatives. The
oscillatory carrier is kept separate from the stripped remainder coefficient.
-/

/-! Merged from `NavierStokes.CurlGeometry`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# Algebra of the curl realization in Lemma 8.8

The dot product below is bilinear, including over `ℂ`: for a real phase normal
its self-product is the real squared length. These results check the principal
symbol and the algebraic divergence cancellation. They do not establish
regularity, bounds for the differentiated amplitude, or descent from the lift.
-/

namespace NavierStokes.CurlGeometry

abbrev Vec3 (R : Type*) := Fin 3 → R

def dot {R : Type*} [CommRing R] (u v : Vec3 R) : R :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

def cross {R : Type*} [CommRing R] (u v : Vec3 R) : Vec3 R :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]








noncomputable def curlSymbol (ξ A : Vec3 ℂ) : Vec3 ℂ :=
  cross (Complex.I • ξ) A

/-- The coefficient of the potential (30), with the oscillatory exponential
factored out. `k` is its nonzero frequency and `n` its phase normal. -/
noncomputable def potentialCoefficient (k : ℂ) (n a : Vec3 ℂ) : Vec3 ℂ :=
  (Complex.I / (k * dot n n)) • cross n a


def complexify (n : Vec3 ℝ) : Vec3 ℂ := fun j => (n j : ℂ)




/-! ## Cylindrical differential cancellation

This is a conditional identity for three additive differential operators on a
commutative ring of coefficient functions. In the application `q = 1/R`.
The assumptions state pairwise commutation and precisely the radial/axial
product rules for multiplication by `q` used by the calculation. They must
still be established for the manuscript's graph derivatives.
-/

def cylindricalCurl {F : Type*} [CommRing F]
    (Dr Dθ Dz : F →+ F) (q : F) (A : Vec3 F) : Vec3 F :=
  ![q * Dθ (A 2) - Dz (A 1),
    Dz (A 0) - Dr (A 2),
    Dr (A 1) + q * A 1 - q * Dθ (A 0)]

def cylindricalDiv {F : Type*} [CommRing F]
    (Dr Dθ Dz : F →+ F) (q : F) (v : Vec3 F) : F :=
  Dr (v 0) + q * v 0 + q * Dθ (v 1) + Dz (v 2)


end NavierStokes.CurlGeometry


end


noncomputable section

namespace NavierStokes.OscillatoryCurl

open ProblemStatement Set Filter
open scoped Topology BigOperators ContDiff InnerProductSpace


/-- Cross product on the same Euclidean space as the PDE target, as a bounded
bilinear map. -/
def crossLinear : Space →L[ℝ] Space →L[ℝ] Space :=
  (EuclideanSpace.proj 1).smulRight ((EuclideanSpace.proj 2).smulRight (coordinateVector 0)) -
  (EuclideanSpace.proj 2).smulRight ((EuclideanSpace.proj 1).smulRight (coordinateVector 0)) +
  (EuclideanSpace.proj 2).smulRight ((EuclideanSpace.proj 0).smulRight (coordinateVector 1)) -
  (EuclideanSpace.proj 0).smulRight ((EuclideanSpace.proj 2).smulRight (coordinateVector 1)) +
  (EuclideanSpace.proj 0).smulRight ((EuclideanSpace.proj 1).smulRight (coordinateVector 2)) -
  (EuclideanSpace.proj 1).smulRight ((EuclideanSpace.proj 0).smulRight (coordinateVector 2))

def cross (u v : Space) : Space := crossLinear u v


theorem cross_apply (u v : Space) :
    cross u v =
      u 1 • (v 2 • coordinateVector 0) - u 2 • (v 1 • coordinateVector 0) +
      u 2 • (v 0 • coordinateVector 1) - u 0 • (v 2 • coordinateVector 1) +
      u 0 • (v 1 • coordinateVector 2) - u 1 • (v 0 • coordinateVector 2) := rfl

@[simp] theorem cross_zero (u v : Space) : (cross u v) 0 = u 1 * v 2 - u 2 * v 1 := by
  rw [cross_apply]
  simp [coordinateVector]

@[simp] theorem cross_one (u v : Space) : (cross u v) 1 = u 2 * v 0 - u 0 * v 2 := by
  rw [cross_apply]
  simp [coordinateVector]

@[simp] theorem cross_two (u v : Space) : (cross u v) 2 = u 0 * v 1 - u 1 * v 0 := by
  rw [cross_apply]
  simp [coordinateVector]

@[simp] theorem cross_smul_left (c : ℝ) (u v : Space) :
    cross (c • u) v = c • cross u v := by simp [cross]

@[simp] theorem cross_smul_right (c : ℝ) (u v : Space) :
    cross u (c • v) = c • cross u v := by simp [cross]

@[simp] theorem cross_zero_right (u : Space) : cross u 0 = 0 := by simp [cross]

theorem inner_coordinates (u v : Space) :
    ⟪u, v⟫_ℝ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]



/-- The inverse-square-normal coefficient used by the real potential. -/
def normalCoefficient (n a : Space) : Space := (‖n‖ ^ 2)⁻¹ • cross n a


/-- The actual Euclidean gradient map applied to a scalar derivative. -/
def gradientLinear : (Space →L[ℝ] ℝ) →L[ℝ] Space :=
  ∑ i : Fin 3, (ContinuousLinearMap.apply ℝ ℝ (coordinateVector i)).smulRight (coordinateVector i)

@[simp] theorem gradientLinear_apply (L : Space →L[ℝ] ℝ) (i : Fin 3) :
    (gradientLinear L) i = L (coordinateVector i) := by
  fin_cases i <;> simp [gradientLinear, Fin.sum_univ_three, coordinateVector]



def carrier (k s : ℝ) : ℝ := -Real.sin (k * s) / k

theorem carrier_hasDerivAt {k : ℝ} (hk : k ≠ 0) (s : ℝ) :
    HasDerivAt (carrier k) (-Real.cos (k * s)) s := by
  have h := ((Real.hasDerivAt_sin (k * s)).comp s
    ((hasDerivAt_id s).const_mul k)).neg.div_const k
  convert! h using 1
  field_simp

theorem carrier_contDiff (k : ℝ) : ContDiff ℝ ∞ (carrier k) :=
  ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).neg).div_const k

/-- Physical spatial phase normal, with time held fixed. -/
def phaseNormal (Φ : PressureField) : VelocityField :=
  fun z => gradientLinear (fderiv ℝ (fun y : Space => Φ (z.1, y)) z.2)


def coefficient (Φ : PressureField) (a : VelocityField) : VelocityField :=
  fun z => normalCoefficient (phaseNormal Φ z) (a z)

/-- `-sin(k Φ) (n × a)/(k |n|²)`, expressed by scalar multiplication. -/
def potential (k : ℝ) (Φ : PressureField) (a : VelocityField) : VelocityField :=
  fun z => carrier k (Φ z) • coefficient Φ a z

def wave (k : ℝ) (Φ : PressureField) (a : VelocityField) : VelocityField :=
  SpatialCurl.spatialCurl (potential k Φ a)

theorem phaseNormal_contDiffOn {U : Set SpaceTime} {Φ : PressureField}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U) : ContDiffOn ℝ ∞ (phaseNormal Φ) U :=
  (ResidualRegularity.contDiffOn_space_fderiv hU hΦ (m := ∞) (by simp)).continuousLinearMap_comp
    gradientLinear












theorem coefficient_periodic {times : Set ℝ} {Φ : PressureField} {a : VelocityField}
    (hn : UnitSpatialPeriodsOn times (phaseNormal Φ)) (ha : UnitSpatialPeriodsOn times a) :
    UnitSpatialPeriodsOn times (coefficient Φ a) := by
  intro t ht x i
  unfold coefficient
  rw [hn t ht x i, ha t ht x i]

/-- It suffices for the sine carrier and the normal/amplitude data to be
periodic; a real-valued phase itself may have nonzero winding. -/
theorem potential_periodic {times : Set ℝ} {Φ : PressureField} {a : VelocityField} (k : ℝ)
    (hcarrier : UnitSpatialPeriodsOn times (fun z => Real.sin (k * Φ z)))
    (hn : UnitSpatialPeriodsOn times (phaseNormal Φ)) (ha : UnitSpatialPeriodsOn times a) :
    UnitSpatialPeriodsOn times (potential k Φ a) := by
  intro t ht x i
  unfold potential carrier
  have hsin := hcarrier t ht x i
  dsimp only at hsin
  rw [hsin, coefficient_periodic hn ha t ht x i]



/-- The coefficient remaining after removing the sine oscillation. -/
def strippedRemainder (k : ℝ) (B : VelocityField) : VelocityField :=
  fun z => (1 / k) • SpatialCurl.spatialCurl B z




end NavierStokes.OscillatoryCurl

import NavierStokes.R3.H3UniformApproximation
import NavierStokes.R3.H3Definitions
import NavierStokes.R3.ViscousEnergyBalance

/-! # Curves in the genuine whole-space H³ topology

The topology is the finite product of the ordinary L² topologies of the
velocity and every weak coordinate derivative through order three. The weak
jets come from one smooth compact approximation at each time.
-/

/-! Merged from `NavierStokes.R3.H3CompactHelpers`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology BigOperators ContDiff

namespace NavierStokesR3.H3Compact

open ProblemStatement
open NavierStokes.ProblemStatement (coordinateVector)
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness (slab spatial_smooth)

/-- Coordinate derivatives are genuine spatial derivatives, including at a
closed time interval's endpoints. -/
def partialField (i : Fin 3) (u : VelocityField) : VelocityField :=
  fun z => spatialPartial i (fun y => u (z.1, y)) z.2

private theorem infinity_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)

theorem partialField_contDiffOn {a b : ℝ} (hab : a < b) {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (i : Fin 3) :
    ContDiffOn ℝ ∞ (partialField i u) (slab a b) := by
  have hs : UniqueDiffOn ℝ (slab a b) :=
    (uniqueDiffOn_Icc hab).prod uniqueDiffOn_univ
  have hc := (hu.fderivWithin hs infinity_add_one_le).clm_apply
    (show ContDiffOn ℝ ∞ (fun _ : SpaceTime => ((0 : ℝ), coordinateVector i))
      (slab a b) from contDiffOn_const)
  apply hc.congr
  intro z hz
  change NavierStokes.ProblemStatement.spatialDerivative u z.1 z.2 (coordinateVector i) = _
  rw [NavierStokes.PeriodicUniqueness.spatialDerivative_eq_within_comp hu hz.1 z.2]
  rfl

theorem partialField_support {a b : ℝ} {u : VelocityField} {K : Set Space}
    (hsupp : ∀ t ∈ Icc a b, tsupport (fun x => u (t, x)) ⊆ K) (i : Fin 3) :
    ∀ t ∈ Icc a b, tsupport (fun x => partialField i u (t, x)) ⊆ K := by
  intro t ht
  change tsupport (fun x => fderiv ℝ (fun y => u (t, y)) x (coordinateVector i)) ⊆ K
  exact (tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans (hsupp t ht)

/-- An arbitrary ordered word of ordinary coordinate derivatives. -/
def partialWord : List (Fin 3) → VelocityField → VelocityField
  | [], u => u
  | i :: is, u => partialField i (partialWord is u)

theorem partialWord_contDiffOn {a b : ℝ} (hab : a < b) {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (is : List (Fin 3)) :
    ContDiffOn ℝ ∞ (partialWord is u) (slab a b) := by
  induction is with
  | nil => exact hu
  | cons i is ih => exact partialField_contDiffOn hab ih i

theorem partialWord_support {a b : ℝ} {u : VelocityField} {K : Set Space}
    (hsupp : ∀ t ∈ Icc a b, tsupport (fun x => u (t, x)) ⊆ K)
    (is : List (Fin 3)) :
    ∀ t ∈ Icc a b, tsupport (fun x => partialWord is u (t, x)) ⊆ K := by
  induction is with
  | nil => exact hsupp
  | cons i is ih => exact partialField_support ih i


theorem partialWord_square_continuousOn {a b : ℝ} (hab : a < b) {u : VelocityField}
    {K : Set Space} (hK : IsCompact K) (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hsupp : ∀ t ∈ Icc a b, tsupport (fun x => u (t, x)) ⊆ K)
    (is : List (Fin 3)) :
    ContinuousOn (fun t => ∫ x : Space, ‖partialWord is u (t, x)‖ ^ 2) (Icc a b) := by
  apply CompactTimeIntegral.continuousOn_integral hK
    ((partialWord_contDiffOn hab hu is).continuousOn.norm.pow 2)
  intro t ht x hx
  change ‖partialWord is u (t, x)‖ ^ 2 = 0
  rw [CompactEnergy.zero_outside (partialWord_support hsupp is t ht) hx]
  simp

end NavierStokesR3.H3Compact


end


/-! Merged from `NavierStokes.R3.H3Continuity`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Continuity in the whole-space derivative H³ norm

The continuity assertion below uses the H³ norm of the difference of two
spatial fields. Thus it controls convergence of every spatial derivative
through order three in genuine Lebesgue L², rather than merely continuity of
the scalar norm of a field.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace NavierStokesR3.H3Embedding

open ProblemStatement H3Compact
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness (slab spatial_smooth)

/-- Continuity in the derivative H³ topology on a time set. All derivatives
through order three are square integrable at every time. -/
def H3ContinuousOn (u : VelocityField) (s : Set ℝ) : Prop :=
  (∀ t ∈ s, HasFiniteH3 (fun x => u (t, x))) ∧
    ∀ t ∈ s, Tendsto (fun r => derivativeH3Norm (fun x => u (r, x) - u (t, x)))
      (𝓝[s] t) (𝓝 0)




@[simp] theorem derivativeH3Norm_zero : derivativeH3Norm (fun _ : Space => (0 : Space)) = 0 := by
  have hz (i : Fin 3) : spatialPartial i (fun _ : Space => (0 : Space)) = fun _ => 0 := by
    funext x
    simp [spatialPartial]
  simp [derivativeH3Norm, derivativeH3Energy, mixedEnergy, squareEnergy, hz]



end NavierStokesR3.H3Embedding


end


noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace NavierStokesR3.H3Comparison

open ProblemStatement H3Embedding

/-- A continuous H³ curve, with its continuous spatial representative and
genuine weak derivative jets. Continuity is in the actual L² spaces. -/
structure H3Curve (u : VelocityField) (s : Set ℝ) where
  first : Fin 3 → VelocityField
  second : Fin 3 → Fin 3 → VelocityField
  third : Fin 3 → Fin 3 → Fin 3 → VelocityField
  spatial_continuous : ∀ t ∈ s, Continuous (fun x => u (t, x))
  approximation : ∀ t ∈ s, H3Approximation (fun x => u (t, x))
    (fun i x => first i (t, x)) (fun i j x => second i j (t, x))
    (fun i j k x => third i j k (t, x))
  velocity_continuous : Continuous (fun t : s =>
    ((approximation t t.property).memLp).toLp (fun x => u (t, x)))
  first_continuous : ∀ i, Continuous (fun t : s =>
    ((approximation t t.property).derivative_memLp i).toLp (fun x => first i (t, x)))
  second_continuous : ∀ i j, Continuous (fun t : s =>
    ((approximation t t.property).second_memLp i j).toLp (fun x => second i j (t, x)))
  third_continuous : ∀ i j k, Continuous (fun t : s =>
    ((approximation t t.property).third_memLp i j k).toLp (fun x => third i j k (t, x)))

namespace H3Curve

variable {u : VelocityField} {s : Set ℝ}

def normAt (h : H3Curve u s) (t : ℝ) : ℝ :=
  weakH3Norm (fun x => u (t, x)) (fun i x => h.first i (t, x))
    (fun i j x => h.second i j (t, x)) (fun i j k x => h.third i j k (t, x))

theorem normAt_nonneg (h : H3Curve u s) (t : ℝ) : 0 ≤ h.normAt t := Real.sqrt_nonneg _

theorem norm_le (h : H3Curve u s) {t : ℝ} (ht : t ∈ s) (x : Space) :
    ‖u (t, x)‖ ≤ 3 * h.normAt t :=
  norm_le_weakH3Norm (h.approximation t ht) (h.spatial_continuous t ht) x




/-- The L² velocity curve, extended by zero off its time set. The extension
is only used at times where the time set contains a neighborhood. -/
def velocityLp (h : H3Curve u s) (t : ℝ) : Lp Space 2 (volume : Measure Space) := by
  classical
  exact if ht : t ∈ s then (h.approximation t ht).memLp.toLp (fun x => u (t, x)) else 0

theorem velocityLp_eq (h : H3Curve u s) {t : ℝ} (ht : t ∈ s) :
    h.velocityLp t = (h.approximation t ht).memLp.toLp (fun x => u (t, x)) := by
  simp only [velocityLp, dite_eq_left ht]


def restrict (h : H3Curve u s) {r : Set ℝ} (hrs : r ⊆ s) : H3Curve u r where
  first := h.first
  second := h.second
  third := h.third
  spatial_continuous := fun t ht => h.spatial_continuous t (hrs ht)
  approximation := fun t ht => h.approximation t (hrs ht)
  velocity_continuous := h.velocity_continuous.comp
    (continuous_subtype_val.subtype_mk (fun t : r => hrs t.property))
  first_continuous := fun i => (h.first_continuous i).comp
    (continuous_subtype_val.subtype_mk (fun t : r => hrs t.property))
  second_continuous := fun i j => (h.second_continuous i j).comp
    (continuous_subtype_val.subtype_mk (fun t : r => hrs t.property))
  third_continuous := fun i j k => (h.third_continuous i j k).comp
    (continuous_subtype_val.subtype_mk (fun t : r => hrs t.property))


end H3Curve

end NavierStokesR3.H3Comparison

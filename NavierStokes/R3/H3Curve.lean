import NavierStokes.R3.H3UniformApproximation
import NavierStokes.R3.H3Continuity

/-! # Curves in the genuine whole-space H³ topology

The topology is the finite product of the ordinary L² topologies of the
velocity and every weak coordinate derivative through order three. The weak
jets come from one smooth compact approximation at each time.
-/

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

import NavierStokes.R3.H3Definitions
import NavierStokes.R3.H3CompactHelpers

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

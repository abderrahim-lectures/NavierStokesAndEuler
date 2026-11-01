import NavierStokes.R3FiniteEnergyComparison
import NavierStokes.R3ActualCandidate
import NavierStokes.R3.Theorem
import NavierStokes.R3.ComparatorBridge

/-!
# The full whole-space theorem implies option (C)

The unconditional whole-space theorem constructs one compactly supported flow
with a uniform energy bound up to time one for every positive viscosity. Its
same force and zero initial data satisfy the exact comparator conditions.
-/

noncomputable section

namespace NavierStokes.ComparatorBridge

open Set ProblemStatement
open scoped ContDiff


/-- Option (C) with exactly the comparator's quantifiers. -/
theorem navier_stokes_breakdown_R3 (ν : ℝ) (hν : ν > 0) :
    ∃ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (f : EuclideanSpace ℝ (Fin 3) → ℝ → EuclideanSpace ℝ (Fin 3)),
      Comparator.InitialVelocityConditionDecay u₀ ∧ Comparator.ForceConditionDecay f ∧
      ¬ (∃ v p, Comparator.NavierStokesExistenceAndSmoothnessRn ν u₀ f v p) := by
  obtain ⟨u, p, f, K, h, hglobal⟩ := NavierStokesR3.theorem_1_1 ν hν
  exact NavierStokesR3.comparator_of_breakdown h hglobal

end NavierStokes.ComparatorBridge

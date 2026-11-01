import NavierStokes.ComparatorBridge
import NavierStokes.ActualCandidateAssembly
import NavierStokes.CandidateConsequences
import NavierStokes.PeriodicPaperComparator

/-!
# The full periodic corollary implies option (D)

For every positive viscosity, the full periodic corollary supplies a solution
that blows up exactly at time one. Its same force and zero datum satisfy every
condition in the comparator, including the force derivative decay bounds.

No result here uses any of the comparator's unproved statements.
-/

noncomputable section

namespace NavierStokes.ComparatorBridge

open Set ProblemStatement
open scoped ContDiff


/-- Option (D), with exactly the comparator's quantifiers, from the project's
closed candidate construction. -/
theorem navier_stokes_breakdown_periodic (ν : ℝ) (hν : ν > 0) :
    ∃ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (f : EuclideanSpace ℝ (Fin 3) → ℝ → EuclideanSpace ℝ (Fin 3)),
      Comparator.InitialVelocityConditionPeriodic u₀ ∧ Comparator.ForceConditionPeriodic f ∧
      ¬ (∃ v p, Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν u₀ f v p) := by
  obtain ⟨u, p, f, K, h, hglobal⟩ := PeriodicPaper.periodic_corollary ν hν
  exact option_D_of_paper_candidate h hglobal

end NavierStokes.ComparatorBridge

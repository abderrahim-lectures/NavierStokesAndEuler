import NavierStokes.ComparatorBridge
import NavierStokes.PeriodicPaperTheorem
import NavierStokes.CandidateConsequences

/-!
# The periodic paper theorem implies the exact comparator statement

The force in this adapter is precisely the candidate's force, with its argument
order changed from `(time, space)` to `space, time`. Neither viscosity nor time
is rescaled. The smooth periodic force's compact future time support supplies
all decay estimates required by the comparator.
-/

/-! Merged from `NavierStokes.PeriodicComparatorSolution`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# The periodic comparator in the paper's coordinates

A smooth comparator solution gives a global smooth periodic solution for the
same viscosity and force. Only the order of the spacetime arguments changes.
-/

noncomputable section

namespace NavierStokes.ComparatorBridge

open ProblemStatement Set

/-- Change coordinates in a periodic comparator solution without changing its
viscosity, force, time variable, or zero initial datum. Smoothness on the closed
future domain is preserved, including its initial-time boundary. -/
def periodicPaperSolution_of_comparator {ν : ℝ} {f : VelocityField}
    {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
    (h : Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν (fun _ => 0)
      (toComparator f) v p) : PeriodicPaper.GlobalSmoothSolution ν f where
  velocity := fromComparator v
  pressure := fromComparator p
  velocity_smooth := fromComparator_smooth h.velocity_smooth
  pressure_smooth := fromComparator_smooth h.pressure_smooth
  velocity_periodic := by
    intro t ht x i
    exact h.isOnePeriodic_velocity t ht x i
  pressure_periodic := by
    intro t ht x i
    exact h.isOnePeriodic_pressure t ht x i
  zero_initial_velocity := h.initial_condition
  divergence_free := by
    intro t ht x
    rw [divergence_eq]
    exact h.div_free x t ht
  navier_stokes := by
    intro t ht x
    exact comparator_equation h ht x

end NavierStokes.ComparatorBridge


end


noncomputable section

namespace NavierStokes.ComparatorBridge

open Set ProblemStatement

/-- The force of a periodic paper candidate meets the comparator's full
periodic force condition, including all derivative decay estimates. -/
theorem forceConditionPeriodic_of_paper_candidate {ν : ℝ}
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (h : PeriodicPaper.CandidateProperties ν u p f K) :
    Comparator.ForceConditionPeriodic (toComparator f) :=
  forceConditionPeriodic_of_decay h.force_smooth.contDiffOn h.force_periodic
    (CandidateConsequences.futureJet_decay h.force_smooth.contDiffOn
      h.force_periodic h.force_time_support)

/-- The exact comparator conditions and exclusion hold for the same force as
the periodic paper candidate and the same viscosity. -/
theorem option_D_same_force_of_paper_candidate {ν : ℝ}
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (h : PeriodicPaper.CandidateProperties ν u p f K)
    (hno : ¬ Nonempty (PeriodicPaper.GlobalSmoothSolution ν f)) :
    Comparator.InitialVelocityConditionPeriodic (fun _ : Space => (0 : Space)) ∧
      Comparator.ForceConditionPeriodic (toComparator f) ∧
      ¬ (∃ v q, Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν
        (fun _ => 0) (toComparator f) v q) := by
  refine ⟨zero_initial_condition, forceConditionPeriodic_of_paper_candidate h, ?_⟩
  rintro ⟨v, q, hv⟩
  exact hno ⟨periodicPaperSolution_of_comparator hv⟩

/-- A periodic paper candidate and its global-solution exclusion imply option
(D), with exactly the comparator's existential quantifiers. -/
theorem option_D_of_paper_candidate {ν : ℝ}
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (h : PeriodicPaper.CandidateProperties ν u p f K)
    (hno : ¬ Nonempty (PeriodicPaper.GlobalSmoothSolution ν f)) :
    ∃ (u₀ : Space → Space) (g : Space → ℝ → Space),
      Comparator.InitialVelocityConditionPeriodic u₀ ∧ Comparator.ForceConditionPeriodic g ∧
      ¬ (∃ v q, Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν u₀ g v q) :=
  ⟨fun _ => 0, toComparator f, option_D_same_force_of_paper_candidate h hno⟩

end NavierStokes.ComparatorBridge

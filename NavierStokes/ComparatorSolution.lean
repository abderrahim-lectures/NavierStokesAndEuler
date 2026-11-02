import NavierStokes.R3.WholeSpaceUniqueness
import NavierStokes.R3CompactCandidate
import NavierStokes.ComparatorBridge
import NavierStokes.R3ActualCandidate
import NavierStokes.R3.Theorem
import NavierStokes.R3.ProblemStatement
import NavierStokes.CompactSpatialForceDecay
import NavierStokes.ActualCandidateAssembly
import NavierStokes.CandidateConsequences
import NavierStokes.PeriodicPaperTheorem

/-!
# Navier–Stokes Comparator submission: options (C) and (D)

Expose the project's proof adapters under the reference theorem names.
The adapters import `ComparatorDefinitions`, never the challenge module.
-/
/-! Merged from `NavierStokes.PeriodicPaperComparator` (in a section, so its `open`s cannot leak). -/
section
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
end


/-! Merged from `NavierStokes.ComparatorR3Bridge`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# Viscosity normalization for the whole-space comparator

This version retains the comparator's square integrability and uniform kinetic
energy bound. It makes no periodicity or compact-support assumption on a
hypothetical global solution.
-/

noncomputable section

namespace NavierStokes.ComparatorBridge

open Set MeasureTheory InnerProductSpace ProblemStatement
open scoped ContDiff Laplacian

theorem zero_initial_condition_decay :
    Comparator.InitialVelocityConditionDecay (fun _ : Space => (0 : Space)) := by
  refine ⟨⟨fun x => Comparator.divergence_const 0 x, contDiff_const⟩, ?_⟩
  intro m K
  exact ⟨0, by simp⟩

/-- A global whole-space solution in the original physical coordinates. -/
structure GlobalSolutionRn (f : VelocityField) (v : VelocityField) (p : PressureField) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ v futureDomain
  pressure_smooth : ContDiffOn ℝ ∞ p futureDomain
  initial_velocity : ∀ x : Space, v (0, x) = 0
  divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Space, spatialDivergence v t x = 0
  navier_stokes : ∀ t : ℝ, 0 < t → ∀ x : Space, navierStokesResidual v p t x = f (t, x)
  integrable : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Space => ‖v (t, x)‖) 2
  globally_bounded_energy : ∃ E : ℝ, ∀ t : ℝ, 0 ≤ t → (∫ x : Space, ‖v (t, x)‖ ^ 2) < E

theorem comparator_equation_Rn {ν : ℝ} {u₀ : Space → Space} {f v : Space → ℝ → Space}
    {p : Space → ℝ → ℝ}
    (h : Comparator.NavierStokesExistenceAndSmoothnessRn ν u₀ f v p)
    {t : ℝ} (ht : 0 < t) (x : Space) :
    temporalDerivative (fromComparator v) t x + advection (fromComparator v) t x -
      ν • spatialLaplacian (fromComparator v) t x +
      pressureGradient (fromComparator p) t x = f x t := by
  have hv := smooth_space_slice (fromComparator_smooth h.velocity_smooth) ht.le
  rw [temporalDerivative_eq _ ht, laplacian_eq _ _ _
    (hv.of_le (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2).le), gradient_eq]
  change derivWithin (v x) (Ici 0) t + fderiv ℝ (v · t) x (v x t) -
    ν • Δ (v · t) x + gradient (p · t) x = f x t
  rw [h.navier_stokes x t ht.le]
  abel


end NavierStokes.ComparatorBridge


end


/-! Merged from `NavierStokes.R3.ComparatorBridge`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# The full whole-space candidate implies the comparator statement

This bridge retains the viscosity and the prescribed force. Compact spacetime
support proves the force's required derivative decay, and a comparator solution
gives exactly a global solution in the whole-space paper statement.
-/

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace NavierStokesR3

open ProblemStatement NavierStokes.ComparatorBridge

theorem forceConditionDecay_of_compact {f : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    NavierStokes.Comparator.ForceConditionDecay (toComparator f) := by
  let K : Set Space := Prod.snd '' tsupport f
  have hK : IsCompact K := hs.isCompact.image continuous_snd
  have hspace : NavierStokes.CompactSpatialForceDecay.SupportedIn K f := by
    intro t ht x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hz
    exact hx ⟨(t, x), hz, rfl⟩
  obtain ⟨M, hM⟩ := hs.isCompact.exists_bound_of_continuousOn
    (continuous_fst.continuousOn : ContinuousOn (Prod.fst : SpaceTime → ℝ) (tsupport f))
  have htime : NavierStokes.ProblemStatement.CompactFutureTimeSupport f := by
    refine ⟨max M 0 + 1, by positivity, ?_⟩
    intro t ht x
    apply image_eq_zero_of_notMem_tsupport
    intro hz
    have hb := hM (t, x) hz
    have hmt := le_abs_self t
    have hmax := le_max_left M 0
    simp only [Real.norm_eq_abs] at hb
    linarith
  exact NavierStokes.CompactSpatialForceDecay.forceConditionDecay hK
    hf.contDiffOn hspace htime

/-- Translate a comparator solution without changing viscosity or time. -/
def globalSolutionOfComparator {ν : ℝ} {f : VelocityField}
    {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
    (h : NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn ν
      (fun _ => 0) (toComparator f) v p) : GlobalFiniteEnergySolution ν f where
  velocity := fromComparator v
  pressure := fromComparator p
  velocity_smooth := fromComparator_smooth h.velocity_smooth
  pressure_smooth := fromComparator_smooth h.pressure_smooth
  zero_initial_velocity := h.initial_condition
  divergence_free := by
    intro t ht x
    rw [divergence_eq]
    exact h.div_free x t ht
  navier_stokes := by
    intro t ht x
    exact comparator_equation_Rn h ht x
  energy_bounded := by
    obtain ⟨E, hE⟩ := h.globally_bounded_energy
    refine ⟨max 0 (E / 2), le_max_left _ _, ?_⟩
    intro t ht
    constructor
    · simpa only [SquareIntegrableAtTime, fromComparator, norm_norm] using!
        (memLp_two_iff_integrable_sq_norm (h.integrable t ht).aestronglyMeasurable).mp (h.integrable t ht)
    · change (1 / 2 : ℝ) * (∫ x : Space, ‖v x t‖ ^ 2) ≤ max 0 (E / 2)
      have hb := (hE t ht).le
      have hm := le_max_right 0 (E / 2)
      linarith

/-- The paper's complete conclusion gives option (C) with the same force. -/
theorem comparator_of_breakdown {ν : ℝ}
    {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (h : CandidateProperties ν u p f K)
    (hglobal : ¬ Nonempty (GlobalFiniteEnergySolution ν f)) :
    ∃ (u₀ : Space → Space) (f : Space → ℝ → Space),
      NavierStokes.Comparator.InitialVelocityConditionDecay u₀ ∧
      NavierStokes.Comparator.ForceConditionDecay f ∧
      ¬ (∃ v p, NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn ν u₀ f v p) := by
  refine ⟨fun _ => 0, toComparator f, zero_initial_condition_decay,
    forceConditionDecay_of_compact h.force_smooth h.force_support.1, ?_⟩
  rintro ⟨v, q, hv⟩
  exact hglobal ⟨globalSolutionOfComparator hv⟩

end NavierStokesR3


end


/-! Merged from `NavierStokes.R3FiniteEnergyComparison`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# Comparison with the compact candidate on all of R³

The whole-space uniqueness proof is ported from the verified R³ development.
The competitor retains exactly the smoothness and finite-energy conditions
of the comparator. The candidate's compact support supplies the reference
solution's bounds on each closed interval before time one.
-/

noncomputable section

namespace NavierStokes.ComparatorBridge

open Set MeasureTheory ProblemStatement
open scoped ContDiff

theorem GlobalSolutionRn.uniformFiniteEnergy {f v : VelocityField} {q : PressureField}
    (h : GlobalSolutionRn f v q) (T : ℝ) :
    NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v := by
  obtain ⟨E, hE⟩ := h.globally_bounded_energy
  refine ⟨max 0 (E / 2), le_max_left _ _, ?_⟩
  intro t ht
  constructor
  · simpa only [NavierStokesR3.ProblemStatement.SquareIntegrableAtTime, norm_norm] using!
      (memLp_two_iff_integrable_sq_norm
        (h.integrable t ht.1).aestronglyMeasurable).mp (h.integrable t ht.1)
  · change (1 / 2 : ℝ) * (∫ x : Space, ‖v (t, x)‖ ^ 2) ≤ max 0 (E / 2)
    have hb := (hE t ht.1).le
    have hm := le_max_right 0 (E / 2)
    linarith


end NavierStokes.ComparatorBridge


end


/-! Merged from `NavierStokes.ComparatorTheorem`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

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


end


/-! Merged from `NavierStokes.ComparatorR3Theorem`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

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


end


namespace NavierStokes.Comparator

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- (C) Breakdown of Navier–Stokes solutions on ℝ³. -/
theorem navier_stokes_breakdown_R3 (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p) := by
  exact ComparatorBridge.navier_stokes_breakdown_R3 nu hnu

/-- (D) Breakdown of Navier–Stokes solutions on ℝ³/ℤ³. -/
theorem navier_stokes_breakdown_periodic (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionPeriodic u₀ ∧ ForceConditionPeriodic f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p) := by
  exact ComparatorBridge.navier_stokes_breakdown_periodic nu hnu

end NavierStokes.Comparator

#print axioms NavierStokes.Comparator.navier_stokes_breakdown_R3
#print axioms NavierStokes.Comparator.navier_stokes_breakdown_periodic

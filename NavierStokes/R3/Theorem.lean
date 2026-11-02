import NavierStokes.R3.ActualCandidate
import NavierStokes.R3.WholeSpaceUniqueness
import NavierStokes.R3.ViscosityScaling
import NavierStokes.R3.IntegratedDissipation

/-!
# Theorem 1.1: unconditional whole-space forced Navier–Stokes blowup

The actual selected construction supplies the viscosity-one fields. Spatial
rescaling gives every positive viscosity while retaining singular time one,
compact support in strictly positive time for the force, and one kinetic-energy
bound for all times before the singularity. Whole-space comparison excludes a
global smooth finite-energy solution with the same prescribed force and datum.
-/

/-! Merged from `NavierStokes.R3.CandidateBreakdown`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# A compact singular candidate excludes a global finite-energy solution

The comparison theorem identifies the two velocities before time one. The
candidate's fixed compact spatial support then confines its unbounded speed
to a compact spacetime set on which a global smooth velocity is bounded.
-/

noncomputable section

open Set
open scoped ContDiff

namespace NavierStokesR3.ProblemStatement

theorem CandidateProperties.not_global_agreement {ν : ℝ}
    {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (h : CandidateProperties ν u p f K) {v : VelocityField}
    (hv : ContDiffOn ℝ ∞ v futureDomain) :
    ¬ (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, u (t, x) = v (t, x)) := by
  intro heq
  have hsub : Icc (0 : ℝ) 1 ×ˢ K ⊆ futureDomain :=
    fun _ hz => ⟨hz.1.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod h.support_compact).exists_bound_of_continuousOn
    (hv.continuousOn.mono hsub)
  have hpos : 0 < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨t, x, ht, _, hlarge⟩ := h.speed_unbounded (max M 1) hpos 1 zero_lt_one
  have hx : x ∈ K := by
    apply h.velocity_support t ⟨ht.1.le, ht.2⟩
    apply subset_tsupport
    intro hz
    change u (t, x) = 0 at hz
    rw [hz, norm_zero] at hlarge
    exact (not_lt_of_ge hpos.le) hlarge
  have hb := hM (t, x) ⟨⟨ht.1.le, ht.2.le⟩, hx⟩
  rw [heq t ⟨ht.1.le, ht.2⟩ x] at hlarge
  exact (not_lt_of_ge (hb.trans (le_max_left M 1))) hlarge

/-- The comparison class has only smoothness, the equation, zero initial
velocity, and a uniform energy bound; no support assumption is imposed on it. -/
theorem CandidateProperties.no_global_solution_one
    {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (h : CandidateProperties 1 u p f K) :
    ¬ Nonempty (GlobalFiniteEnergySolution 1 f) := by
  rintro ⟨v⟩
  exact h.not_global_agreement v.velocity_smooth
    (WholeSpaceUniqueness.candidate_global_agrees_before_one h v)


/-- One bound for the actual spatial square integrals, with integrability
proved separately so that the totalized integral cannot hide infinite energy. -/
theorem CandidateProperties.uniform_l2_sq_bound {ν : ℝ}
    {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (h : CandidateProperties ν u p f K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico (0 : ℝ) 1,
      SquareIntegrableAtTime u t ∧ (∫ x : Space, ‖u (t, x)‖ ^ 2) ≤ C := by
  obtain ⟨E, hE, hb⟩ := h.energy_bounded
  refine ⟨2 * E, by positivity, ?_⟩
  intro t ht
  obtain ⟨hi, he⟩ := hb t ht
  refine ⟨hi, ?_⟩
  change (1 / 2 : ℝ) * (∫ x : Space, ‖u (t, x)‖ ^ 2) ≤ E at he
  linarith

end NavierStokesR3.ProblemStatement


end


noncomputable section

open Set MeasureTheory

namespace NavierStokesR3

open ProblemStatement ViscosityScaling

/-- The full paper conclusion, together with the initial time interval on
which the constructed velocity is at rest. No construction hypotheses remain. -/
theorem theorem_1_1_with_initial_rest (ν : ℝ) (hν : 0 < ν) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧
      ¬ Nonempty (GlobalFiniteEnergySolution ν f) ∧
      ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space,
        u (t, x) = 0 ∧ p (t, x) = 0 := by
  obtain ⟨u, p, f, K, hc, hzero⟩ := ActualCandidate.selected_candidate_one_with_initial_rest
  refine ⟨scaledVelocity ν u, scaledPressure ν p, scaledVelocity ν f,
    (fun x : Space => Real.sqrt ν • x) '' K, candidate_at_viscosity hc hν, ?_, ?_⟩
  · rintro ⟨v⟩
    exact hc.no_global_solution_one ⟨normalized_global_solution hν v⟩
  · intro t ht x
    constructor
    · change Real.sqrt ν • u (t, (Real.sqrt ν)⁻¹ • x) = 0
      rw [(hzero t ht _).1, smul_zero]
    · change ν • p (t, (Real.sqrt ν)⁻¹ • x) = 0
      rw [(hzero t ht _).2, smul_zero]

/-- Theorem 1.1, with all properties of the same velocity, pressure, force,
and compact support witnessed simultaneously, for every positive viscosity. -/
theorem theorem_1_1 : ProblemStatement.breakdownStatement := by
  intro ν hν
  obtain ⟨u, p, f, K, hc, hg, _⟩ := theorem_1_1_with_initial_rest ν hν
  exact ⟨u, p, f, K, hc, hg⟩

/-- The primary whole-space candidate-existence assertion at any positive viscosity. -/
theorem candidateStatement (ν : ℝ) (hν : 0 < ν) :
    ProblemStatement.candidateStatement ν := by
  obtain ⟨u, p, f, K, hc, _⟩ := theorem_1_1 ν hν
  exact ⟨u, p, f, K, hc⟩

/-- The candidate construction is unconditional for every positive viscosity. -/
theorem coreBreakdownStatement : ProblemStatement.coreBreakdownStatement :=
  candidateStatement

/-- The whole-space breakdown assertion is an unconditional theorem. -/
theorem breakdownStatement : ProblemStatement.breakdownStatement := theorem_1_1

/-- Theorem 1.1 and all energy conclusions of Lemma 10.4 hold for the same
constructed fields. Total dissipation is explicitly integrable up to time one. -/
theorem theorem_1_1_with_dissipation (ν : ℝ) (hν : 0 < ν) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧
      ¬ Nonempty (GlobalFiniteEnergySolution ν f) ∧
      IntervalIntegrable (CompactEnergy.l2Norm f) volume 0 1 ∧
      IntegrableOn (CompactEnergy.dissipation u) (Ico (0 : ℝ) 1) ∧
      (∀ T ∈ Ico (0 : ℝ) 1,
        CompactEnergy.l2Sq u T +
          2 * ν * (∫ t in (0 : ℝ)..T, CompactEnergy.dissipation u t) ≤
            (CompactEnergy.cumulativeForceNorm f T) ^ 2) ∧
      2 * ν * (∫ t in Ico (0 : ℝ) 1, CompactEnergy.dissipation u t) ≤
        (CompactEnergy.cumulativeForceNorm f 1) ^ 2 := by
  obtain ⟨u, p, f, K, hc, hg⟩ := theorem_1_1 ν hν
  exact ⟨u, p, f, K, hc, hg, CompactEnergy.candidate_energy_estimates hν hc⟩

end NavierStokesR3

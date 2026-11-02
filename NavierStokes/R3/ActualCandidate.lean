import NavierStokes.R3ActualCandidate
import NavierStokes.R3.CompactEnergy
import NavierStokes.R3.ProblemStatement
import NavierStokes.SmoothCutoffs

/-!
# The full whole-space candidate from the selected construction

The selected construction supplies its actual compact spatial fields and a
globally smooth force. A smooth time cutoff preserves the equation and puts
the force's entire topological support strictly inside positive time. The
whole-space energy estimate then gives one bound up to the singular time.
-/

/-! Merged from `NavierStokes.R3.PositiveTimeForce`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# A smooth force cutoff separated from initial time

The cutoff equals one throughout `[3/8, 1]`, and its support is contained
in `[1/16, 21/16]`. Thus a force with a fixed compact spatial support can
be extended to a compactly supported force in strictly positive spacetime.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace NavierStokesR3.PositiveTimeForce

open ProblemStatement

def timeCutoff (t : ℝ) : ℝ :=
  NavierStokes.SmoothCutoffs.cutoff ((8 / 5 : ℝ) * (t - 11 / 16))

theorem timeCutoff_contDiff : ContDiff ℝ ∞ timeCutoff :=
  NavierStokes.SmoothCutoffs.cutoff_contDiff.comp
    (contDiff_const.mul (contDiff_id.sub contDiff_const))

theorem timeCutoff_eq_one {t : ℝ} (ht : t ∈ Icc (3 / 8 : ℝ) 1) :
    timeCutoff t = 1 := by
  apply NavierStokes.SmoothCutoffs.cutoff_one_of_abs_le
  rw [abs_le]
  constructor <;> nlinarith [ht.1, ht.2]

theorem timeCutoff_eq_zero {t : ℝ} (ht : t ∉ Icc (1 / 16 : ℝ) (21 / 16)) :
    timeCutoff t = 0 := by
  apply NavierStokes.SmoothCutoffs.cutoff_zero_of_one_le_abs
  rcases not_and_or.mp ht with h | h
  · have hlt : t < 1 / 16 := lt_of_not_ge h
    have hn : (8 / 5 : ℝ) * (t - 11 / 16) ≤ -1 := by linarith
    exact (by linarith : (1 : ℝ) ≤ -((8 / 5 : ℝ) * (t - 11 / 16))).trans
      (neg_le_abs _)
  · have hgt : 21 / 16 < t := lt_of_not_ge h
    exact (by linarith : (1 : ℝ) ≤ (8 / 5 : ℝ) * (t - 11 / 16)).trans
      (le_abs_self _)

def force (f : VelocityField) : VelocityField :=
  fun z => timeCutoff z.1 • f z

theorem force_contDiff {f : VelocityField} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (force f) :=
  (timeCutoff_contDiff.comp contDiff_fst).smul hf

theorem force_eq {f : VelocityField} {t : ℝ}
    (ht : t ∈ Icc (3 / 8 : ℝ) 1) (x : Space) : force f (t, x) = f (t, x) := by
  simp only [force, timeCutoff_eq_one ht, one_smul]

theorem force_eq_zero {f : VelocityField} {t : ℝ} {x : Space}
    (hf : f (t, x) = 0) : force f (t, x) = 0 := by
  simp only [force, hf, smul_zero]

theorem force_tsupport_subset {f : VelocityField} {K : Set Space}
    (hK : IsCompact K) (hf : ∀ t x, x ∉ K → f (t, x) = 0) :
    tsupport (force f) ⊆ Icc (1 / 16 : ℝ) (21 / 16) ×ˢ K := by
  apply closure_minimal _ (isClosed_Icc.prod hK.isClosed)
  rintro ⟨t, x⟩ hz
  constructor
  · by_contra ht
    exact hz (by simp only [force, timeCutoff_eq_zero ht, zero_smul])
  · by_contra hx
    exact hz (force_eq_zero (hf t x hx))

theorem force_compactPositiveTimeSupport {f : VelocityField} {K : Set Space}
    (hK : IsCompact K) (hf : ∀ t x, x ∉ K → f (t, x) = 0) :
    CompactPositiveTimeSupport (force f) := by
  have hs := force_tsupport_subset hK hf
  constructor
  · exact (isCompact_Icc.prod hK).of_isClosed_subset isClosed_closure hs
  · intro z hz
    have ht := (hs hz).1.1
    exact ⟨by change 0 < z.1; linarith, mem_univ _⟩

end NavierStokesR3.PositiveTimeForce


end


noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokesR3.ActualCandidate

open NavierStokes.ProblemStatement
open NavierStokes

theorem activatedVelocity_eventually_zero {u : VelocityField} {t : ℝ}
    (ht : |t| < 3 / 8) (x : Space) :
    TimeLocalization.activatedVelocity u =ᶠ[𝓝 (t, x)] (fun _ => 0) := by
  have hn : {z : SpaceTime | |z.1| < 3 / 8} ∈ 𝓝 (t, x) :=
    (isOpen_lt continuous_fst.abs continuous_const).mem_nhds ht
  filter_upwards [hn] with z hz
  exact TimeLocalization.activatedVelocity_zero_early u hz.le z.2

theorem activatedPressure_eventually_zero {p : PressureField} {t : ℝ}
    (ht : |t| < 3 / 8) (x : Space) :
    TimeLocalization.activatedPressure p =ᶠ[𝓝 (t, x)] (fun _ => 0) := by
  have hn : {z : SpaceTime | |z.1| < 3 / 8} ∈ 𝓝 (t, x) :=
    (isOpen_lt continuous_fst.abs continuous_const).mem_nhds ht
  filter_upwards [hn] with z hz
  exact TimeLocalization.activatedPressure_zero_early p hz.le z.2

theorem localized_residual_zero_early (A B : VelocityField) (P : PressureField)
    {t : ℝ} (ht : |t| < 3 / 8) (x : Space) :
    navierStokesResidual (R3CompactCandidate.velocity A B)
      (R3CompactCandidate.pressure P) t x = 0 := by
  unfold R3CompactCandidate.velocity R3CompactCandidate.pressure
  exact ResidualRegularity.residual_eq_zero_of_eventually_zero (z := (t, x))
    (activatedVelocity_eventually_zero
      (u := fun z => SpatialLocalization.cutVelocity A z + SpatialLocalization.cutPotential B z)
      ht x)
    (activatedPressure_eventually_zero (p := SpatialLocalization.cutPressure P) ht x)

theorem localized_velocity_tsupport (A B : VelocityField) (t : ℝ) :
    tsupport (fun x : Space => R3CompactCandidate.velocity A B (t, x)) ⊆
      SpatialLocalization.supportCylinder := by
  apply closure_minimal _ SpatialLocalization.isClosed_supportCylinder
  intro x hx
  by_contra h
  exact hx (R3CompactCandidate.velocity_supported A B t x h)

theorem localized_pressure_tsupport (P : PressureField) (t : ℝ) :
    tsupport (fun x : Space => R3CompactCandidate.pressure P (t, x)) ⊆
      SpatialLocalization.supportCylinder := by
  apply closure_minimal _ SpatialLocalization.isClosed_supportCylinder
  intro x hx
  by_contra h
  exact hx (R3CompactCandidate.pressure_supported P t x h)

theorem compactForce_smooth {f : VelocityField} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (R3CompactCandidate.compactForce f) :=
  (R3CompactCandidate.outerCutoff_smooth.comp contDiff_snd).smul hf

theorem compactForce_supported_all_times (f : VelocityField) (t : ℝ) (x : Space)
    (hx : x ∉ R3CompactCandidate.outerSupport) :
    R3CompactCandidate.compactForce f (t, x) = 0 := by
  simp [R3CompactCandidate.compactForce, R3CompactCandidate.outerCutoff_zero_outside hx]

/-- Preserve the original localized velocity and pressure, and use a force
whose compact support is separated from time zero. -/
theorem of_localized_fields {A B : VelocityField} {P : PressureField} {f : VelocityField}
    (h : NavierStokes.ProblemStatement.CandidateProperties
      (R3CompactCandidate.periodicVelocity A B) (R3CompactCandidate.periodicPressure P) f)
    (hf : ContDiff ℝ ∞ f) :
    ProblemStatement.CandidateProperties 1
      (R3CompactCandidate.velocity A B) (R3CompactCandidate.pressure P)
      (PositiveTimeForce.force (R3CompactCandidate.compactForce f))
      SpatialLocalization.supportCylinder := by
  have hc := R3CompactCandidate.of_localized_fields h
  have hF := PositiveTimeForce.force_contDiff (compactForce_smooth hf)
  have hsupport := PositiveTimeForce.force_compactPositiveTimeSupport
    R3CompactCandidate.outerSupport_compact (compactForce_supported_all_times f)
  have hNS : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
      navierStokesResidual (R3CompactCandidate.velocity A B)
        (R3CompactCandidate.pressure P) t x =
        PositiveTimeForce.force (R3CompactCandidate.compactForce f) (t, x) := by
    intro t ht x
    by_cases hearly : t < 3 / 8
    · have hzero := localized_residual_zero_early A B P
        (by rwa [abs_of_pos ht.1]) x
      have hforcezero : R3CompactCandidate.compactForce f (t, x) = 0 :=
        (hc.navier_stokes t ht x).symm.trans hzero
      rw [hzero, PositiveTimeForce.force_eq_zero hforcezero]
    · rw [PositiveTimeForce.force_eq ⟨le_of_not_gt hearly, ht.2.le⟩ x]
      exact hc.navier_stokes t ht x
  refine {
    velocity_smooth := hc.velocity_smooth
    pressure_smooth := hc.pressure_smooth
    support_compact := SpatialLocalization.isCompact_supportCylinder
    velocity_support := fun t _ => localized_velocity_tsupport A B t
    pressure_support := fun t _ => localized_pressure_tsupport P t
    force_smooth := hF
    force_support := hsupport
    zero_initial_velocity := hc.zero_initial_velocity
    divergence_free := hc.divergence_free
    navier_stokes := ?_
    energy_bounded := ?_
    speed_unbounded := hc.speed_unbounded
  }
  · intro t ht x
    simpa only [ProblemStatement.residual_at_viscosity_one] using hNS t ht x
  · exact CompactEnergy.uniform_finite_energy SpatialLocalization.isCompact_supportCylinder
      hc.velocity_smooth hc.pressure_smooth (fun t _ => localized_velocity_tsupport A B t)
      hF hsupport.1 hc.zero_initial_velocity
      (fun t ht => hc.divergence_free t ⟨ht.1.le, ht.2⟩) hNS



/-- Both fields are identically zero on an initial time interval, so a
delayed parabolic rescaling can be smoothly extended by zero. -/
theorem selected_candidate_one_with_initial_rest :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      ProblemStatement.CandidateProperties 1 u p f K ∧
        ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space,
          u (t, x) = 0 ∧ p (t, x) = 0 := by
  obtain ⟨a, _, ea, eb, ep, forcing, hc, hf, _⟩ :=
    ActualCandidateAssembly.selected_witness
  refine ⟨_, _, _, _, of_localized_fields hc hf, ?_⟩
  intro t ht x
  exact ⟨TimeLocalization.activatedVelocity_zero_early _ ht x,
    TimeLocalization.activatedPressure_zero_early _ ht x⟩

end NavierStokesR3.ActualCandidate

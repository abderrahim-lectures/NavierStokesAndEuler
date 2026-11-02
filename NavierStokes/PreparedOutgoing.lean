import NavierStokes.ExtendedHeatedOutgoing
import NavierStokes.TerminalCone
import NavierStokes.MatchingDebtBounds
import NavierStokes.OutgoingCone

/-!
# One prepared outgoing profile and arbitrarily late nominal matching

The reset bound precedes the outgoing exponent, the height bounds precede
the actual height, and the natural-axis choices use this same profile.
The clean cone below belongs to the unedited outgoing profile. Identification
with the complete edited nominal stress is a separate construction.
-/
/-! Merged from `NavierStokes.ScheduledProfileChoice` (in a section, so its `open`s cannot leak). -/
section
/-!
# A common scheduled profile below caller-supplied parameter bounds

The reset coefficient bound is selected before lambda. The caller's lambda
cap is intersected with the existing reset and energy thresholds before any
profile is constructed. The actual core is then fixed before choosing h.
-/

noncomputable section

namespace NavierStokes.ScheduledProfileChoice

open OutgoingProfile (Profile)
open ExtendedHeatedOutgoing (ScheduleBounds)

/-- The actual core and reset bound precede every subsequent height choice. -/
theorem exists_scheduled_core_below (P m : ℝ) (hP : 0 < P) (hm : 0 < m)
    (cap : ℝ → ℝ) (hcap : ∀ K : ℝ, 0 < K → 0 < cap K) :
    ∃ (K B : ℝ) (core : OutgoingSchedule.Parameters),
      0 < K ∧ 0 < B ∧ core.P = P ∧ core.m = m ∧
      core.wait = 60 * Real.log (1 / core.lam) ∧
      core.lam < cap K ∧ core.lam < 1 / 120 ∧
      ∀ h : ℝ, 0 < h → 2 * h < core.lam →
        ∃ F : Profile, F.data.core = core ∧ F.data.h = h ∧ F.coefficientBound = K ∧
          ScheduleBounds F ∧ OutgoingProfile.Specification F B := by
  obtain ⟨resetLam, K, hresetLam, hK, hreset⟩ := UniformAngularReset.exists_scheduled_reset
  obtain ⟨delta, hdelta, hrate⟩ := PulseAmplitude.exists_rate_threshold
    (CorrectedPulseAmplitude.combinedConstant P m K)
  let lam₀ := min (cap K) (min resetLam (min delta (1 / 120 : ℝ)))
  have hlam₀ : 0 < lam₀ := lt_min (hcap K hK) (lt_min hresetLam (lt_min hdelta (by norm_num)))
  let lam := lam₀ / 2
  have hlam : 0 < lam := half_pos hlam₀
  have hlam₀' : lam < lam₀ := half_lt_self hlam₀
  have hcaller : lam < cap K := hlam₀'.trans_le (min_le_left _ _)
  have hrest : lam < min resetLam (min delta (1 / 120 : ℝ)) :=
    hlam₀'.trans_le (min_le_right _ _)
  have hreset' : lam < resetLam := hrest.trans_le (min_le_left _ _)
  have hdelta' : lam < delta := hrest.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsmall : lam < 1 / 120 := hrest.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let core := OutgoingSchedule.paperParameters P m lam hP hm hlam (by linarith)
  refine ⟨K, 128 * CorrectedPulseAmplitude.combinedConstant P m K, core, hK,
    mul_pos (by norm_num) (CorrectedPulseAmplitude.combinedConstant_pos hP m K hK),
    rfl, rfl, rfl, hcaller, hsmall, ?_⟩
  intro h hh htail
  let d : OutgoingTail.TailData := ⟨core, h, hh, htail⟩
  obtain ⟨r⟩ := hreset d hreset'
  let F : Profile := ⟨d, K, r⟩
  have b : ScheduleBounds F := {
    coefficient_pos := hK
    lambda_small := hsmall.le
    wait_eq := rfl
    scale_small := hrate lam hlam hdelta' }
  exact ⟨F, rfl, rfl, rfl, b, b.specification⟩


/-- This number depends on the already fixed core and an additional caller
height bound. It is chosen before the terminal exponent h. -/
noncomputable def heightCap (core : OutgoingSchedule.Parameters) (extra : ℝ) : ℝ :=
  min (core.lam / 4)
    (min extra (min (1 / 1000) (min (1 / 4) (1 / (1 + TerminalCone.releaseBudget core)))))

theorem heightCap_pos (core : OutgoingSchedule.Parameters) {extra : ℝ} (he : 0 < extra) :
    0 < heightCap core extra := by
  have hb := TerminalCone.releaseBudget_nonneg core
  exact lt_min (div_pos core.lam_pos (by norm_num))
    (lt_min he (lt_min (by norm_num) (lt_min (by norm_num) (by positivity))))

theorem heightCap_bounds (core : OutgoingSchedule.Parameters) (extra : ℝ) :
    2 * heightCap core extra < core.lam ∧ heightCap core extra ≤ extra ∧
      heightCap core extra ≤ 1 / 1000 ∧ heightCap core extra ≤ 1 / 4 ∧
      heightCap core extra ≤ 1 / (1 + TerminalCone.releaseBudget core) := by
  have hl : heightCap core extra ≤ core.lam / 4 := min_le_left _ _
  have hr : heightCap core extra ≤
      min extra (min (1 / 1000) (min (1 / 4) (1 / (1 + TerminalCone.releaseBudget core)))) := min_le_right _ _
  have hrest := hr.trans (min_le_right _ _)
  have hlast := hrest.trans (min_le_right _ _)
  exact ⟨by linarith [core.lam_pos], hr.trans (min_le_left _ _),
    hrest.trans (min_le_left _ _), hlast.trans (min_le_left _ _), hlast.trans (min_le_right _ _)⟩

/-- The common lambda and all height caps are fixed before h and before the
actual reset/Profile. The additional cap may impose the outgoing-cone height
bound; the built-in caps also give the axis and terminal requirements. -/
theorem exists_scheduled_family_below (P m : ℝ) (hP : 0 < P) (hm : 0 < m)
    (cap : ℝ → ℝ) (hcap : ∀ K : ℝ, 0 < K → 0 < cap K)
    (extraHeight : OutgoingSchedule.Parameters → ℝ)
    (hextra : ∀ core : OutgoingSchedule.Parameters, 0 < extraHeight core) :
    ∃ (K B H : ℝ) (core : OutgoingSchedule.Parameters),
      0 < K ∧ 0 < B ∧ 0 < H ∧ core.P = P ∧ core.m = m ∧
      core.wait = 60 * Real.log (1 / core.lam) ∧
      core.lam < cap K ∧ core.lam < 1 / 120 ∧
      2 * H < core.lam ∧ H ≤ extraHeight core ∧ H ≤ 1 / 1000 ∧
      ∀ h : ℝ, 0 < h → h ≤ H →
        ∃ F : Profile, F.data.core = core ∧ F.data.h = h ∧ F.coefficientBound = K ∧
          ScheduleBounds F ∧ OutgoingProfile.Specification F B ∧ TerminalCone.SmallTail F.data := by
  obtain ⟨K, B, core, hK, hB, hcP, hcm, hwait, hcaller, hsmall, hf⟩ :=
    exists_scheduled_core_below P m hP hm cap hcap
  have hb := heightCap_bounds core (extraHeight core)
  refine ⟨K, B, heightCap core (extraHeight core), core, hK, hB,
    heightCap_pos core (hextra core), hcP, hcm, hwait, hcaller, hsmall,
    hb.1, hb.2.1, hb.2.2.1, ?_⟩
  intro h hh hH
  have ht : 2 * h < core.lam := (mul_le_mul_of_nonneg_left hH (by norm_num)).trans_lt hb.1
  obtain ⟨F, hcore, hh', hK', hs, hF⟩ := hf h hh ht
  refine ⟨F, hcore, hh', hK', hs, hF, ?_⟩
  unfold TerminalCone.SmallTail
  rw [hcore, hh']
  exact ⟨hH.trans hb.2.2.2.1, hH.trans hb.2.2.2.2⟩

end NavierStokes.ScheduledProfileChoice
end


noncomputable section

namespace NavierStokes.PreparedOutgoing

open Set Filter OutgoingProfile

/-- Data obtained from the actual schedule construction, with a clean cone
available at all sufficiently late matching radii. -/
structure PreparedProfile where
  profile : Profile
  bound : ℝ
  bound_pos : 0 < bound
  specification : Specification profile bound
  schedule : ExtendedHeatedOutgoing.ScheduleBounds profile
  terminal : TerminalCone.SmallTail profile.data
  amplitude_lower : 2 ≤ profile.data.core.P
  height_upper : profile.data.h ≤ 1 / 1000
  clean : ∀ left : ℝ, left ≤ 0 →
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ R : ℝ, R0 < R → OutgoingCone.ProfileCleanCone profile R left

/-- Select the reset bound and exponent together, respecting the clean-cone
cap before constructing the profile. No existing exponent is changed later. -/
theorem exists_prepared : Nonempty PreparedProfile := by
  classical
  obtain ⟨M, hM, hcone⟩ := OutgoingCone.exists_ordered_profile_cone
  let P : ℝ := max 2 (OutgoingEntranceCone.amplitudeThreshold M)
  have hP2 : 2 ≤ P := le_max_left _ _
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP2
  have hPamp : OutgoingEntranceCone.amplitudeThreshold M ≤ P := le_max_right _ _
  let caps := hcone M le_rfl P hPamp
  let cap : ℝ → ℝ := fun K =>
    if hK : 0 < K then Classical.choose (caps K hK) else 1
  have hcap : ∀ K : ℝ, 0 < K → 0 < cap K := by
    intro K hK
    dsimp only [cap]
    rw [dite_eq_left hK]
    exact (Classical.choose_spec (caps K hK)).1
  obtain ⟨K, B, H, core, hK, hB, hH, hcP, hcm, hwait, hlam, _hsmall,
      _h2H, hheight, hHsmall, hfamily⟩ :=
    ScheduledProfileChoice.exists_scheduled_family_below P M hPpos hM cap hcap
      (fun core => OutgoingCone.heightThreshold M core.lam)
      (fun core => OutgoingCone.heightThreshold_pos M core.lam_pos)
  obtain ⟨F, hcore, hh, hFK, hschedule, hspec, hterminal⟩ := hfamily H hH le_rfl
  have hFP : F.data.core.P = P := by rw [hcore, hcP]
  have hFm : F.data.core.m = M := by rw [hcore, hcm]
  have hFwait : F.data.core.wait = 60 * Real.log (1 / F.data.core.lam) := by
    rw [hcore]
    exact hwait
  have hFlam : F.data.core.lam < Classical.choose (caps K hK) := by
    rw [hcore]
    simpa only [cap, dite_eq_left hK] using hlam
  have hFheight : F.data.h ≤ OutgoingCone.heightThreshold M F.data.core.lam := by
    rw [hh, hcore]
    exact hheight
  have hclean := (Classical.choose_spec (caps K hK)).2 F hFP hFm hFK hFwait hFlam hFheight
  exact ⟨{
    profile := F
    bound := B
    bound_pos := hB
    specification := hspec
    schedule := hschedule
    terminal := hterminal
    amplitude_lower := by rw [hFP]; exact hP2
    height_upper := by rw [hh]; exact hHsmall
    clean := hclean }⟩

/-- The actual nominal matching radius can exceed any prescribed bound while
the outgoing profile and all its schedule choices remain fixed. -/
theorem PreparedProfile.large_nominal (d : PreparedProfile) (floor left : ℝ)
    (hleft : left ≤ 0) :
    ∃ W : NominalProfile.Witness d.profile,
      floor < W.controls.radius ∧
      OutgoingCone.ProfileCleanCone d.profile W.controls.radius left := by
  obtain ⟨R0, _hR0, hclean⟩ := d.clean left hleft
  have hrho : 0 < NominalProfile.resetSolver.radius / 2 :=
    div_pos NominalProfile.resetSolver.radius_pos (by norm_num)
  have hradius : NominalProfile.resetSolver.radius / 2 ≤ NominalProfile.resetSolver.radius := by
    linarith [NominalProfile.resetSolver.radius_pos]
  obtain ⟨eps, heps, _heps1, hordered⟩ :=
    MatchingDebtBounds.exists_ordered_nominal_witness d.specification d.amplitude_lower
      0 hrho hradius
  let j : ℝ := min (eps / 2) (1 / 2000)
  have hj : 0 < j := lt_min (by positivity) (by norm_num)
  have hjbound : |j| ≤ eps := by
    rw [abs_of_pos hj]
    exact (min_le_left _ _).trans (by linarith)
  have hsmall : NaturalAxisData.SmallParameters d.profile.data.h j :=
    ⟨d.profile.data.h_pos, d.height_upper, hj,
      (min_le_right _ _).trans (by norm_num)⟩
  obtain ⟨L0, hL0, hscale⟩ := hordered j hjbound hsmall
  obtain ⟨T, _hT, C0, _hC0, hnorm⟩ := hscale L0 (zero_lt_one.trans_le hL0) le_rfl
  obtain ⟨C, _hCpos, hC0, hR, _hsep⟩ :=
    (NominalProfile.eventually_matching_geometry d.profile T (max floor R0) C0).exists
  obtain ⟨W, _hjW, _hLW, hCW, _hTW, _hmatch⟩ := hnorm C hC0
  have hrad : W.controls.radius = NominalProfile.matchingRadius d.profile C := by
    change NominalProfile.matchingRadius d.profile W.axis.normalization = _
    rw [hCW]
  refine ⟨W, ?_, ?_⟩
  · rw [hrad]
    exact (le_max_left _ _).trans_lt hR
  · apply hclean
    rw [hrad]
    exact (le_max_right _ _).trans_lt hR

/-- An actual fixed prepared profile, obtained from the proved existence. -/
noncomputable def prepared : PreparedProfile := Classical.choice exists_prepared


end NavierStokes.PreparedOutgoing

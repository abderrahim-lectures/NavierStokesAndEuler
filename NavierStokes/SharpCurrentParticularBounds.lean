import NavierStokes.SharpCurrentModeJets
import NavierStokes.ActualCurrentParticularBounds
import NavierStokes.CurrentParticularLabelBounds


/-! Merged from `NavierStokes.CurrentPhysicalRadialClosure`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! Bounds on the open profile annulus extend to its closed edges while
the physical similarity scale and the dyadic band remain fixed. -/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.CurrentPhysicalRadialClosure

open ProblemStatement PhysicalWaveSum ActualCurrentWaveSupport

/-- Change only the transverse coordinates. -/
def radialScale (w : SpaceTime) (c : ℝ) : SpaceTime :=
  (w.1, c • w.2 + ((1 - c) * w.2 2) • EuclideanSpace.single 2 1)

theorem radialScale_continuous (w : SpaceTime) : Continuous (radialScale w) := by
  exact continuous_const.prodMk ((continuous_id.smul continuous_const).add
    (((continuous_const.sub continuous_id).mul continuous_const).smul continuous_const))

@[simp] theorem radialScale_one (w : SpaceTime) : radialScale w 1 = w := by
  simp [radialScale]

@[simp] theorem radialScale_time (w : SpaceTime) (c : ℝ) : (radialScale w c).1 = w.1 := rfl

@[simp] theorem radialScale_axial (w : SpaceTime) (c : ℝ) :
    (radialScale w c).2 2 = w.2 2 := by
  simp only [radialScale, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.single_apply, ite_eq_left, mul_one]
  ring

@[simp] theorem radialScale_q (h : ℝ) (w : SpaceTime) (c : ℝ) :
    physicalQ h (radialScale w c) = physicalQ h w := by
  simp only [physicalQ, SimilarityProfile.q, AxisymmetricFields.profilePoint,
    radialScale_time, radialScale_axial]

theorem radialScale_projection (w : SpaceTime) (c : ℝ) :
    PhysicalGraphBounds.radialProjection (radialScale w c) =
      c • PhysicalGraphBounds.radialProjection w := by
  ext <;> simp [PhysicalGraphBounds.radialProjection_apply, radialScale]

theorem radialScale_radius (h : ℝ) (w : SpaceTime) {c : ℝ} (hc : 0 < c) :
    profileRadius h (radialScale w c) = c * profileRadius h w := by
  simp only [profileRadius, AnnularEndpoint.radius, radialScale_projection,
    PolarCharts.radius_smul hc, radialScale_q]
  ring

/-- Every closed-annulus point is a limit of strict-annulus points in its
same physical-scale fiber, hence in the same open dyadic band. -/
theorem closed_mem_closure_fiber {h a b : ℝ} (ha : 0 < a) (hab : a < b)
    {n : ℕ} {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band h n)
    (hr : profileRadius h w ∈ Icc a b) :
    w ∈ closure {y : SpaceTime | y ∈ ValidDyadicBandCover.band h n ∧
      physicalQ h y = physicalQ h w ∧ profileRadius h y ∈ Ioo a b} := by
  have hR : 0 < profileRadius h w := ha.trans_le hr.1
  let g : ℝ → SpaceTime := fun r => radialScale w (r / profileRadius h w)
  have hg : Continuous g := (radialScale_continuous w).comp
    (continuous_id.div_const _)
  have he : g (profileRadius h w) = w := by
    simp only [g, div_self hR.ne', radialScale_one]
  have hmap : MapsTo g (Ioo a b) {y : SpaceTime |
      y ∈ ValidDyadicBandCover.band h n ∧ physicalQ h y = physicalQ h w ∧
        profileRadius h y ∈ Ioo a b} := by
    intro r hrr
    have hc : 0 < r / profileRadius h w := div_pos (ha.trans hrr.1) hR
    have hband : g r ∈ ValidDyadicBandCover.band h n := by
      simpa only [ValidDyadicBandCover.band, mem_ofPred_eq, preterminal, g,
        radialScale_time, radialScale_q] using hw
    refine ⟨hband, radialScale_q _ _ _, ?_⟩
    change profileRadius h (radialScale w (r / profileRadius h w)) ∈ Ioo a b
    rwa [radialScale_radius h w hc, div_mul_cancel₀ _ hR.ne']
  have hcl : g (profileRadius h w) ∈ closure (g '' Ioo a b) := by
    apply mem_closure_image hg.continuousAt
    rw [closure_Ioo hab.ne]
    exact hr
  rw [he] at hcl
  exact closure_mono hmap.image_subset hcl

/-- A bound depending arbitrarily on the physical scale extends to both
annulus edges. No continuity assumption on the scale bound is needed. -/
theorem jet_bound_on_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h a b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    {n : ℕ} {f : SpaceTime → E}
    (hf : ContDiffOn ℝ ∞ f (ValidDyadicBandCover.band h n))
    (m : ℕ) (bound : ℝ → ℝ) {qcap : ℝ}
    (hb : ∀ y ∈ ValidDyadicBandCover.band h n, physicalQ h y ≤ qcap →
      profileRadius h y ∈ Ioo a b → ‖iteratedFDeriv ℝ m f y‖ ≤ bound (physicalQ h y))
    {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band h n)
    (hq : physicalQ h w ≤ qcap) (hr : profileRadius h w ∈ Icc a b) :
    ‖iteratedFDeriv ℝ m f w‖ ≤ bound (physicalQ h w) := by
  apply LocalPhysicalCopyBounds.jet_bound_at_closure
    (hf.contDiffAt ((ValidDyadicBandCover.band_open hh hh1 n).mem_nhds hw))
    (closed_mem_closure_fiber ha hab hw hr) m
  intro y hy
  simpa only [hy.2.1] using hb y hy.1 (hy.2.1 ▸ hq) hy.2.2

end NavierStokes.CurrentPhysicalRadialClosure


end

noncomputable section

namespace NavierStokes.SharpCurrentParticularBounds

open Set Function Filter ProblemStatement CorrectionStep
open CorrectionInitialization ActualCurrentParticularBounds
open CorrectionInitialization.ActualPrimary (h outgoing nominal)
open LocalPhysicalCopyBounds SharpCurrentModeJets
open SharpCurrentPhysicalPhase (nativeMap fullMap smoothNear_comp weightedPhase_smoothNear nativeMap_smoothNear)
open scoped Topology ContDiff BigOperators

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (ActualInitialization.Index B N0)}

private theorem commonGap_bound (n : ℕ) :
    CurrentPhysicalModeGerms.commonGap n ≤ CommonWindow.gap h := by
  have hn := CommonWindow.native_le_index_add h outgoing.data.h_pos.le n
  unfold CurrentPhysicalModeGerms.commonGap
  omega

/-- The sharp bound first on the strict profile annulus, where the native
coefficient class is defined. The phase is used only on its actual copy cell. -/
theorem potential_mode_strict_bound (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℤ) (hj : j ≠ 0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ (l : Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, PhysicalWaveSum.physicalQ h w ≤ 1 →
      ActualCurrentWaveSupport.profileRadius h w ∈
        Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotentialMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (h * (σ + 1) - h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h) *
            (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ P := by
  let y := ActualCycleParameters.particularState x
  have hcar := ActualParticularCycleData.preservesCarriers H
  have hin := ActualParticularCycleData.native_inputSupport H
  have hsrc := ActualParticularCycleData.native_source_class H j hj
  have hf := actual_potential_coefficient_class y hcar hin hN j hj hsrc
  obtain ⟨A, hA, e, hab⟩ := (native_source_bounds hf).chart_bound m
  have hg : h * ((1 / 2 + σ) + 1 / 2) = h * (σ + 1) := by ring
  rw [hg] at hab
  obtain ⟨D, hD, p, hd⟩ := rotated_mode_bound (B := B) (N0 := N0)
    (b := CurrentModeGeometry.chartOuter) CurrentModeGeometry.chartInner_pos
    (CommonWindow.gap h) m (h * (σ + 1)) A e hA j
  obtain ⟨C, hC, P, hc⟩ := rescaled_log_bound (E := HarmonicCalculus.ComplexVector)
    (F := Space) m (h * (σ + 1) - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h)
    h D 3 p hD (by norm_num)
  refine ⟨C, hC, P, ?_⟩
  intro l n hn w hw hq hr
  have hqpos := PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1
  have hann := CurrentModeGeometry.scaledRadial_mem_annulus n hw ⟨hr.1.le, hr.2.le⟩
  let c := PhysicalWaveSum.chooseChart CurrentModeGeometry.chartInner (PhysicalGraphBounds.scaledRadial n w)
  let d := CurrentPhysicalModeGerms.commonGap n
  have hchart := PhysicalWaveSum.chooseChart_valid CurrentModeGeometry.chartInner_pos hann
  have hzD := CurrentModeGeometry.point_mem_nativeDomain n CurrentModeGeometry.chartInner_pos c hw hchart
  have hzR := CurrentModeGeometry.point_profileRadius n CurrentModeGeometry.chartInner_pos c hw.1 hchart
  have hz : nativeMap CurrentModeGeometry.chartInner c n d w ∈ nativeStrip.domain := by
    apply ActualCurrentParticularPhysical.nativeStrip_mem hzD
    rwa [hzR]
  have haxis := PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree CurrentModeGeometry.chartInner_pos hann)
  let f := potentialCoefficient y l j n
  let F : SpaceTime → HarmonicCalculus.ComplexVector := fun z =>
    PhysicalGraphBounds.character (j : ℝ) (ActualCurrentCarrierJets.weightedPhase l n
      (nativeMap CurrentModeGeometry.chartInner c n d z)) •
        CurrentPhysicalChartJets.rotated CurrentModeGeometry.chartInner c f (PhysicalWaveSum.commonLift h n d z)
  have hmode : ActualCurrentParticularPhysical.localPotentialMode y l j n =ᶠ[𝓝 w]
      (fun z => ChartScales.Q n ^ (-h) • CurrentPhysicalChartJets.realVectorCLM (F z)) := by
    have he := CurrentPhysicalModeGerms.localPotentialMode_germ y l j
      (ActualParticularStageControls.preserves_frequency hcar l) n CurrentModeGeometry.chartInner_pos c hchart
    filter_upwards [he] with z hz
    rw [hz, actual_nativePotential_eq_character y hcar]
    simp only [F, f, nativeMap, Function.comp_def, CurrentPhysicalChartJets.rotated,
      CurrentPhysicalChartJets.rotation, CurrentPhysicalChartJets.chartMap,
      CurrentPhysicalChartJets.realVectorCLM_apply, rotationMap_complex_smul]
    rfl
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hmode m]
  rcases common_control_or_zero y hin hN l j n hz with ⟨k, hk⟩ | hzero
  · have hi : fullMap CurrentModeGeometry.chartInner c n d w ∈ ActualPhaseJetBounds.phaseCell n (l,k) :=
      ActualParticularStageControls.controlPatch_subset_padded l n k hk
    have hnear : SmoothNear f (nativeMap CurrentModeGeometry.chartInner c n d w) :=
      ⟨_, nativeStrip.isOpen_domain, hz, hf.smooth l n⟩
    have hjets := hd n hn d (commonGap_bound n) c (l,k) w hann
      (PhysicalStageBounds.abs_time_le_one outgoing.data.h_pos outgoing.data.h_lt_half hw.1 hq)
      hi f hnear (hab l n hn _ hz)
    have hrot := CurrentPhysicalChartJets.rotated_smoothNear CurrentModeGeometry.chartInner_pos
      (PhysicalClassBounds.commonLift_mem_cylindricalDomain CurrentModeGeometry.chartInner_pos h n d w hann) hnear
    have hFn : SmoothNear F w := modulated_smoothNear
      (smoothNear_comp hrot (commonLift_smoothNear n d haxis))
      (weightedPhase_smoothNear CurrentModeGeometry.chartInner_pos c n d haxis hi) (j : ℝ)
    have he := hc n (by omega) _ hqpos (CurrentModeGeometry.band_q_comparison n hw).1
      (CurrentModeGeometry.band_q_comparison n hw).2 w F hFn hjets
      CurrentPhysicalChartJets.realVectorCLM CurrentPhysicalChartJets.norm_realVectorCLM_le
    have heq : h * (σ + 1) - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h - h =
        h * (σ + 1) - h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h := by ring
    simpa only [heq] using he
  · have h0 := hzero.1.comp_tendsto
      (nativeMap_smoothNear CurrentModeGeometry.chartInner_pos c n d haxis).contDiffAt.continuousAt
    have hF0 : F =ᶠ[𝓝 w] (fun _ => 0) := by
      filter_upwards [h0] with z hz
      simp only [F, CurrentPhysicalChartJets.rotated, f, nativeMap, Function.comp_def] at hz ⊢
      rw [hz, map_zero, smul_zero]
    have hscaled : (fun z => ChartScales.Q n ^ (-h) • CurrentPhysicalChartJets.realVectorCLM (F z))
        =ᶠ[𝓝 w] (fun _ => 0) := by
      filter_upwards [hF0] with z hz
      rw [hz, map_zero, smul_zero]
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hscaled m]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos hqpos _).le) (by positivity)

theorem pressure_mode_strict_bound (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℤ) (hj : j ≠ 0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ (l : Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, PhysicalWaveSum.physicalQ h w ≤ 1 →
      ActualCurrentWaveSupport.profileRadius h w ∈
        Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressureMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (h * (σ + 1) - 2 * CoordinateAlgebra.A h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h) *
            (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ P := by
  let y := ActualCycleParameters.particularState x
  have hcar := ActualParticularCycleData.preservesCarriers H
  have hin := ActualParticularCycleData.native_inputSupport H
  have hsrc := ActualParticularCycleData.native_source_class H j hj
  have hf := actual_pressure_coefficient_class y hcar hin hN j hj hsrc
  obtain ⟨A, hA, e, hab⟩ := (native_source_bounds hf).chart_bound m
  have hg : h * ((1 / 2 + σ) + 1 / 2) = h * (σ + 1) := by ring
  rw [hg] at hab
  obtain ⟨D, hD, p, hd⟩ := native_mode_bound (E := ℂ) (B := B) (N0 := N0)
    (b := CurrentModeGeometry.chartOuter) CurrentModeGeometry.chartInner_pos
    (CommonWindow.gap h) m (h * (σ + 1)) A e hA j
  obtain ⟨C, hC, P, hc⟩ := rescaled_log_bound (E := ℂ)
    (F := ℝ) m (h * (σ + 1) - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h)
    (2 * CoordinateAlgebra.A h) D 1 p hD zero_le_one
  refine ⟨C, hC, P, ?_⟩
  intro l n hn w hw hq hr
  have hqpos := PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1
  have hann := CurrentModeGeometry.scaledRadial_mem_annulus n hw ⟨hr.1.le, hr.2.le⟩
  let c := PhysicalWaveSum.chooseChart CurrentModeGeometry.chartInner (PhysicalGraphBounds.scaledRadial n w)
  let d := CurrentPhysicalModeGerms.commonGap n
  have hchart := PhysicalWaveSum.chooseChart_valid CurrentModeGeometry.chartInner_pos hann
  have hzD := CurrentModeGeometry.point_mem_nativeDomain n CurrentModeGeometry.chartInner_pos c hw hchart
  have hzR := CurrentModeGeometry.point_profileRadius n CurrentModeGeometry.chartInner_pos c hw.1 hchart
  have hz : nativeMap CurrentModeGeometry.chartInner c n d w ∈ nativeStrip.domain := by
    apply ActualCurrentParticularPhysical.nativeStrip_mem hzD
    rwa [hzR]
  have haxis := PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree CurrentModeGeometry.chartInner_pos hann)
  let f := (ActualParticularStageControls.data y l j).common.pressure n
  let F : SpaceTime → ℂ := fun z =>
    PhysicalGraphBounds.character (j : ℝ) (ActualCurrentCarrierJets.weightedPhase l n
      (nativeMap CurrentModeGeometry.chartInner c n d z)) •
        f (nativeMap CurrentModeGeometry.chartInner c n d z)
  have hmode : ActualCurrentParticularPhysical.localPressureMode y l j n =ᶠ[𝓝 w]
      (fun z => ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h)) • Complex.reCLM (F z)) := by
    have he := CurrentPhysicalModeGerms.localPressureMode_germ y l j
      (ActualParticularStageControls.preserves_frequency hcar l) n CurrentModeGeometry.chartInner_pos c hchart
    filter_upwards [he] with z hz
    rw [hz, actual_nativePressure_eq_character y hcar]
    simp only [F, f, nativeMap, Function.comp_def, CurrentPhysicalChartJets.chartMap,
      neg_mul, smul_eq_mul]
    rfl
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hmode m]
  rcases common_control_or_zero y hin hN l j n hz with ⟨k, hk⟩ | hzero
  · have hi : fullMap CurrentModeGeometry.chartInner c n d w ∈ ActualPhaseJetBounds.phaseCell n (l,k) :=
      ActualParticularStageControls.controlPatch_subset_padded l n k hk
    have hnear : SmoothNear f (nativeMap CurrentModeGeometry.chartInner c n d w) :=
      ⟨_, nativeStrip.isOpen_domain, hz, hf.smooth l n⟩
    have hjets := hd n hn d (commonGap_bound n) c (l,k) w hann
      (PhysicalStageBounds.abs_time_le_one outgoing.data.h_pos outgoing.data.h_lt_half hw.1 hq)
      hi f hnear (hab l n hn _ hz)
    have hFn : SmoothNear F w := modulated_smoothNear
      (smoothNear_comp hnear (nativeMap_smoothNear CurrentModeGeometry.chartInner_pos c n d haxis))
      (weightedPhase_smoothNear CurrentModeGeometry.chartInner_pos c n d haxis hi) (j : ℝ)
    have he := hc n (by omega) _ hqpos (CurrentModeGeometry.band_q_comparison n hw).1
      (CurrentModeGeometry.band_q_comparison n hw).2 w F hFn hjets
      Complex.reCLM (by
        apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro z
        simpa only [Complex.reCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_re_le_norm z)
    have heq : h * (σ + 1) - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h - 2 * CoordinateAlgebra.A h =
        h * (σ + 1) - 2 * CoordinateAlgebra.A h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h := by ring
    simpa only [heq] using he
  · have h0 := hzero.2.comp_tendsto
      (nativeMap_smoothNear CurrentModeGeometry.chartInner_pos c n d haxis).contDiffAt.continuousAt
    have hF0 : F =ᶠ[𝓝 w] (fun _ => 0) := by
      filter_upwards [h0] with z hz
      change PhysicalGraphBounds.character _ _ • f (nativeMap CurrentModeGeometry.chartInner c n d z) = 0
      change f (nativeMap CurrentModeGeometry.chartInner c n d z) = 0 at hz
      rw [hz, smul_zero]
    have hscaled : (fun z => ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h)) • Complex.reCLM (F z))
        =ᶠ[𝓝 w] (fun _ => 0) := by
      filter_upwards [hF0] with z hz
      rw [hz, map_zero, smul_zero]
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hscaled m]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos hqpos _).le) (by positivity)

/-- The full valid-band bound for the actual current potential mode. Closed
annulus edges follow by continuity in a fixed physical-scale fiber. -/
theorem current_potential_mode_bound (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℤ) (hj : j ≠ 0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ (l : Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotentialMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (h * (σ + 1) - h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h) *
            (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ P := by
  obtain ⟨C, hC, P, hb⟩ := potential_mode_strict_bound H hN j hj m
  refine ⟨C, hC, P, ?_⟩
  intro l n hn w hw hq
  by_cases hr : ActualCurrentWaveSupport.profileRadius h w ∈
      Icc (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)
  · exact CurrentPhysicalRadialClosure.jet_bound_on_closed outgoing.data.h_pos
      outgoing.data.h_lt_half (PrimaryTargetBounds.leftRadius_pos nominal)
      (PrimaryTargetBounds.radii_ordered nominal)
      (CurrentParticularLabelBounds.current_modes_contDiffOn H hN l j hj n).1 m
      (fun q => C * q ^ (h * (σ + 1) - h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h) *
        (1 + |Real.log q|) ^ P) (hb l n hn) hw hq hr
  · have hs := (ActualCurrentWaveSupport.current_mode_annulus hN
      (ActualCycleParameters.particularState x) l (H.inputSupport (l.2,l.1)) j 0).1
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq
      (hs.zero_germ outgoing.data.h_pos outgoing.data.h_lt_half (Nat.zero_le n) hw hr) m]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    have hqpos := PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1
    exact mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos hqpos _).le) (by positivity)

/-- The pressure estimate has its literal quadratic physical scale and the
same per-derivative loss as the potential estimate. -/
theorem current_pressure_mode_bound (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℤ) (hj : j ≠ 0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ (l : Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressureMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (h * (σ + 1) - 2 * CoordinateAlgebra.A h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h) *
            (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ P := by
  obtain ⟨C, hC, P, hb⟩ := pressure_mode_strict_bound H hN j hj m
  refine ⟨C, hC, P, ?_⟩
  intro l n hn w hw hq
  by_cases hr : ActualCurrentWaveSupport.profileRadius h w ∈
      Icc (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)
  · exact CurrentPhysicalRadialClosure.jet_bound_on_closed outgoing.data.h_pos
      outgoing.data.h_lt_half (PrimaryTargetBounds.leftRadius_pos nominal)
      (PrimaryTargetBounds.radii_ordered nominal)
      (CurrentParticularLabelBounds.current_modes_contDiffOn H hN l j hj n).2 m
      (fun q => C * q ^ (h * (σ + 1) - 2 * CoordinateAlgebra.A h -
        (m : ℝ) * SharpPhysicalCarrier.derivativeCost h) * (1 + |Real.log q|) ^ P)
      (hb l n hn) hw hq hr
  · have hs := (ActualCurrentWaveSupport.current_mode_annulus hN
      (ActualCycleParameters.particularState x) l (H.inputSupport (l.2,l.1)) j 0).2
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq
      (hs.zero_germ outgoing.data.h_pos outgoing.data.h_lt_half (Nat.zero_le n) hw hr) m]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    have hqpos := PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1
    exact mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos hqpos _).le) (by positivity)

end NavierStokes.SharpCurrentParticularBounds

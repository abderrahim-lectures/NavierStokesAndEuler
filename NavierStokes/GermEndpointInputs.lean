import NavierStokes.GenericEndpointExtension
import NavierStokes.MixedDiagonalExtensions
import NavierStokes.CutStageEstimates
import NavierStokes.ActualPhysicalStageBounds
import NavierStokes.MixedCandidateAssembly
import NavierStokes.ActualMeanStageData
import NavierStokes.TailGaugePotential
import NavierStokes.SlowBaseEndpoint
import NavierStokes.ActualStageEstimates
import NavierStokes.GermCandidateAssembly
import NavierStokes.InitialPhysicalData

/-!
# Endpoint inputs for physical fields assembled by germs

The potential increments may be literal glued physical fields.  Only their
interior smoothness and actual derivative estimates enter the extension
argument; a representation by a fixed-reference copy family is unnecessary.
The zeroth potential and pressure retain the separately extended slow base.
-/
/-! Merged from `NavierStokes.OffplaneJetExtensions` (in a section, so its `open`s cannot leak). -/
section
/-!
# Off-plane endpoint extensions from actual raw jets

A compact spacetime localization converts bounds on every actual derivative
in a past half-ball into a genuine smooth extension.  The physical scale is
then localized away from zero, so raw power-logarithmic jet bounds supply
the required estimates without a recursive continuation assumption.
-/

noncomputable section

namespace NavierStokes.OffplaneJetExtensions

open Set Function Filter Metric ProblemStatement
open scoped Topology ContDiff BigOperators

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

noncomputable def pastBall (x : Space) (r : ℝ) : Set SpaceTime :=
  Metric.ball (1, x) r ∩ SpacetimeEndpoint.openPast 1

theorem pastBall_open (x : Space) (r : ℝ) : IsOpen (pastBall x r) :=
  isOpen_ball.inter (SpacetimeEndpoint.openPast_isOpen 1)

noncomputable def localBump (x : Space) {r : ℝ} (hr : 0 < r) : ContDiffBump ((1 : ℝ), x) where
  rIn := r / 4
  rOut := r / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

theorem localBump_support (x : Space) {r : ℝ} (hr : 0 < r) :
    tsupport (localBump x hr) ⊆ Metric.ball ((1 : ℝ), x) r := by
  rw [(localBump x hr).tsupport_eq]
  exact Metric.closedBall_subset_ball (by change r / 2 < r; linarith)

theorem localBump_jet_bounded (x : Space) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : SpaceTime, ‖iteratedFDeriv ℝ m (localBump x hr) w‖ ≤ C := by
  obtain ⟨C, hC⟩ := ((localBump x hr).hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) m).exists_bound_of_continuous
    ((localBump x hr).contDiff.continuous_iteratedFDeriv (nat_le_infty m))
  exact ⟨max C 0, le_max_right _ _, fun w => (hC w).trans (le_max_left _ _)⟩

section LocalExtension

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def localized (f : SpaceTime → V) (x : Space) {r : ℝ} (hr : 0 < r)
    (w : SpaceTime) : V := localBump x hr w • f w

theorem localized_zero_germ (f : SpaceTime → V) (x : Space) {r : ℝ} (hr : 0 < r)
    {w : SpaceTime} (hw : w ∉ tsupport (localBump x hr)) :
    localized f x hr =ᶠ[𝓝 w] fun _ => 0 := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hw] with z hz
  simp only [localized, hz, Pi.zero_apply, zero_smul]

theorem localized_smooth {f : SpaceTime → V} {x : Space} {r : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (pastBall x r)) :
    ContDiffOn ℝ ∞ (localized f x hr) GenericEndpointExtension.openStrip := by
  intro w hw
  by_cases hs : w ∈ tsupport (localBump x hr)
  · have hlocal : w ∈ pastBall x r :=
      ⟨localBump_support x hr hs, hw.1.2, mem_univ _⟩
    exact (((localBump x hr).contDiff.contDiffAt).smul
      (hf.contDiffAt ((pastBall_open x r).mem_nhds hlocal))).contDiffWithinAt
  · exact ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : SpaceTime => (0 : V)) w).congr_of_eventuallyEq
      (localized_zero_germ f x hr hs)).contDiffWithinAt

theorem localized_jets_bounded {f : SpaceTime → V} {x : Space} {r : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (pastBall x r))
    (hb : ∀ m : ℕ, ∃ C : ℝ, ∀ w ∈ pastBall x r, ‖iteratedFDeriv ℝ m f w‖ ≤ C) :
    ∀ m : ℕ, ∃ C : ℝ, ∀ w ∈ GenericEndpointExtension.openStrip,
      ‖iteratedFDeriv ℝ m (localized f x hr) w‖ ≤ C := by
  choose A hA using hb
  choose C hC hCb using localBump_jet_bounded x hr
  intro m
  let K : ℝ := ∑ i ∈ Finset.range (m + 1),
    (m.choose i : ℝ) * C i * max (A (m - i)) 0
  have hK : 0 ≤ K := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (le_max_right _ _)
  refine ⟨K, fun w hw => ?_⟩
  by_cases hs : w ∈ tsupport (localBump x hr)
  · have hlocal : w ∈ pastBall x r :=
      ⟨localBump_support x hr hs, hw.1.2, mem_univ _⟩
    have hprod := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ)
      (localBump x hr).contDiff.contDiffOn hf (pastBall_open x r).uniqueDiffOn
      hlocal (nat_le_infty m)
    simp only [iteratedFDerivWithin_of_isOpen _ (pastBall_open x r) hlocal] at hprod
    apply hprod.trans
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hCb i w) (Nat.cast_nonneg _))
      ((hA (m - i) w hlocal).trans (le_max_left _ _))
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC i))
  · have hz : iteratedFDeriv ℝ m (localized f x hr) w = 0 := by
      simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using
        (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq (localized_zero_germ f x hr hs) m).self_of_nhds
    rw [hz, norm_zero]
    exact hK

variable [CompleteSpace V]

/-- A local bound for every actual joint derivative supplies an actual
smooth extension. Endpoint derivative limits are constructed by the
generic extension theorem; they are not additional inputs. -/
theorem extension_of_local_jets {f : SpaceTime → V} {x : Space} {r : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (pastBall x r))
    (hb : ∀ m : ℕ, ∃ C : ℝ, ∀ w ∈ pastBall x r, ‖iteratedFDeriv ℝ m f w‖ ≤ C) :
    Nonempty (JointResidualLimits.OneSidedExtension f x) := by
  let g := localized f x hr
  have hg : ContDiffOn ℝ ∞ g GenericEndpointExtension.openStrip := localized_smooth hr hf
  have hgb : ∀ m : ℕ, ∃ C : ℝ, ∀ w ∈ GenericEndpointExtension.openStrip,
      ‖iteratedFDeriv ℝ m g w‖ ≤ C := localized_jets_bounded hr hf hb
  refine ⟨{
    value := GenericEndpointExtension.extension g hg hgb
    domain := Metric.ball ((1 : ℝ), x) (r / 4) ∩ {w : SpaceTime | -1 < w.1}
    isOpen := isOpen_ball.inter (isOpen_lt continuous_const continuous_fst)
    mem := ⟨Metric.mem_ball_self (by positivity), by norm_num⟩
    smooth := (GenericEndpointExtension.extension_contDiff hg hgb).contDiffOn
    agrees := ?_ }⟩
  intro w hw
  have hstrip : w ∈ GenericEndpointExtension.openStrip :=
    ⟨⟨hw.1.2, hw.2.1⟩, mem_univ _⟩
  rw [GenericEndpointExtension.extension_eq hg hgb hstrip]
  have hc : localBump x hr w = 1 :=
    (localBump x hr).one_of_mem_closedBall (Metric.mem_closedBall.mpr hw.1.1.le)
  simp only [g, localized, hc, one_smul]

end LocalExtension

section PhysicalScale

/-- One neighborhood controls the physical scale for all derivative
orders. Only the actual past coordinate is used in the conclusion. -/
theorem exists_scale_neighborhood {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {x : Space} (hx : x 2 ≠ 0)
    (hq : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    ∃ r : ℝ, 0 < r ∧ ∀ w ∈ pastBall x r,
      w ∈ CutStageEstimates.physicalSublevel h qbig ∧
      EndpointCoordinates.endpointRoot (2 * h) (x 2) / 2 < PhysicalWaveSum.physicalQ h w ∧
      |w.1| ≤ 1 := by
  have hp := EndpointCoordinates.endpointRoot_pos (2 * h) hx
  have hlim := MixedDiagonalExtensions.physicalQ_tendsto_endpoint hh hh1 hx
  have he : ∀ᶠ w in 𝓝[SpacetimeEndpoint.openPast 1] (1, x),
      PhysicalWaveSum.physicalQ h w ∈
        Ioo (EndpointCoordinates.endpointRoot (2 * h) (x 2) / 2) qbig :=
    hlim.eventually (isOpen_Ioo.mem_nhds ⟨by linarith, hq⟩)
  obtain ⟨U, hU, hxU, hsub⟩ := mem_nhdsWithin.mp he
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  refine ⟨min r 1, lt_min hr zero_lt_one, ?_⟩
  intro w hw
  have hwU : w ∈ U := hball (ball_subset_ball (min_le_left _ _) hw.1)
  have hscale := hsub ⟨hwU, hw.2⟩
  have hfst : dist w.1 (1 : ℝ) ≤ dist w ((1 : ℝ), x) := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hdist : dist w.1 (1 : ℝ) < 1 :=
    hfst.trans_lt (hw.1.trans_le (min_le_right _ _))
  have htime : 0 < w.1 := by
    rw [Real.dist_eq] at hdist
    have hs := (abs_lt.mp hdist).1
    linarith
  exact ⟨⟨hw.2.1, hscale.2⟩, hscale.1,
    by rw [abs_of_pos htime]; exact hw.2.1.le⟩

/-- Arbitrary real powers and logarithmic losses are uniformly bounded
when the scale lies in a fixed compact subinterval of `(0,∞)`. -/
theorem powerLog_bounded {a : ℝ} (ha : 0 < a) (C p e : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q ∈ Icc a 1,
      C * (1 + |Real.log q|) ^ p * q ^ e ≤ K := by
  have hne : ∀ q ∈ Icc a (1 : ℝ), q ≠ 0 := fun q hq => (ha.trans_le hq.1).ne'
  have hl : ContinuousOn (fun q : ℝ => 1 + |Real.log q|) (Icc a 1) :=
    continuousOn_const.add ((continuousOn_id.log hne).abs)
  have hlne : ∀ q ∈ Icc a (1 : ℝ), (1 + |Real.log q|) ≠ 0 := by
    intro q _
    positivity
  have hc : ContinuousOn (fun q : ℝ => C * (1 + |Real.log q|) ^ p * q ^ e) (Icc a 1) :=
    (continuousOn_const.mul (hl.rpow_const (fun q hq => Or.inl (hlne q hq)))).mul
      (continuousOn_id.rpow_const (fun q hq => Or.inl (hne q hq)))
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max K 0, le_max_right _ _, fun q hq => ?_⟩
  have hk : |C * (1 + |Real.log q|) ^ p * q ^ e| ≤ K := by
    simpa only [Real.norm_eq_abs] using hK q hq
  exact (le_abs_self _).trans (hk.trans (le_max_left _ _))

end PhysicalScale

section PhysicalExtensions

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- A single-field endpoint theorem, including the bounded finite pieces
at stage zero. It assumes only their actual interior jet estimates. -/
theorem extension_of_powerLog_jets {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : qbig ≤ 1) {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (CutStageEstimates.physicalSublevel h qbig))
    (hb : ∀ m : ℕ, ∃ C p e : ℝ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      |w.1| ≤ 1 → PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤
        C * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ p *
          PhysicalWaveSum.physicalQ h w ^ e)
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension f x) := by
  obtain ⟨r, hr, hscale⟩ := exists_scale_neighborhood hh hh1 hx hqx
  apply extension_of_local_jets hr (hf.mono (fun w hw => (hscale w hw).1))
  intro m
  obtain ⟨C, p, e, hm⟩ := hb m
  obtain ⟨K, _, hK⟩ := powerLog_bounded (half_pos (EndpointCoordinates.endpointRoot_pos (2 * h) hx)) C p e
  refine ⟨K, fun w hw => ?_⟩
  have hs := hscale w hw
  have hq1 : PhysicalWaveSum.physicalQ h w ≤ 1 := hs.1.2.le.trans hqbig
  exact (hm w hs.1 hs.2.2 hq1).trans (hK _ ⟨hs.2.1.le, hq1⟩)




end PhysicalExtensions

section Assembly

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Combine, for example, the existing base-gauge extension with the
separately derived extension of the finite initial correction. -/
noncomputable def addExtension {f g : SpaceTime → V} {x : Space}
    (ef : JointResidualLimits.OneSidedExtension f x)
    (eg : JointResidualLimits.OneSidedExtension g x) :
    JointResidualLimits.OneSidedExtension (fun w => f w + g w) x where
  value w := ef.value w + eg.value w
  domain := ef.domain ∩ eg.domain
  isOpen := ef.isOpen.inter eg.isOpen
  mem := ⟨ef.mem, eg.mem⟩
  smooth := (ef.smooth.mono inter_subset_left).add (eg.smooth.mono inter_subset_right)
  agrees := fun w hw => by
    change ef.value w + eg.value w = f w + g w
    rw [ef.agrees ⟨hw.1.1, hw.2⟩, eg.agrees ⟨hw.1.2, hw.2⟩]

theorem extension_add {f g : SpaceTime → V} {x : Space}
    (hf : Nonempty (JointResidualLimits.OneSidedExtension f x))
    (hg : Nonempty (JointResidualLimits.OneSidedExtension g x)) :
    Nonempty (JointResidualLimits.OneSidedExtension (fun w => f w + g w) x) :=
  hf.elim fun ef => hg.elim fun eg => ⟨addExtension ef eg⟩

/-- The constructed stage need only agree with the bounded model on its
actual validity region. The positive scale margin supplies the required
past neighborhood automatically. -/
theorem extension_of_eqOn_sublevel {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f g : SpaceTime → V} (he : EqOn f g (CutStageEstimates.physicalSublevel h qbig))
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig)
    (eg : Nonempty (JointResidualLimits.OneSidedExtension g x)) :
    Nonempty (JointResidualLimits.OneSidedExtension f x) := by
  obtain ⟨eg⟩ := eg
  apply MixedDiagonalExtensions.extension_of_eventuallyEq _ eg
  filter_upwards [self_mem_nhdsWithin,
    (MixedDiagonalExtensions.physicalQ_tendsto_endpoint hh hh1 hx).eventually (gt_mem_nhds hqx)] with w hw hq
  exact he ⟨hw.1, hq⟩

end Assembly

section FiniteInitialPieces

open ActualPhysicalStageBounds



variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}



end FiniteInitialPieces

end NavierStokes.OffplaneJetExtensions
end


/-! Merged from `NavierStokes.ActualEndpointInputs`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# Endpoint inputs for the actual raw candidate stages

Positive stages use their already proved raw estimates.  Stage zero uses
the actual initial mean families and the existing extensions of the same
base potential and pressure.  No output extension is an input below.
-/

noncomputable section

namespace NavierStokes.ActualEndpointInputs

open Set Function Filter ProblemStatement
open CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff

universe u

/-- The three off-plane endpoint obligations of `candidate_of_finite_stages`.
This is an output package; the construction below does not assume its fields. -/
structure EndpointInputs (h qbig : ℝ) (A V : ℕ → VelocityField) (P : ℕ → PressureField) : Prop where
  potential : ∀ x : Space, x 2 ≠ 0 → EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig →
    ∀ j, Nonempty (JointResidualLimits.OneSidedExtension (A j) x)
  direct : ∀ x : Space, x 2 ≠ 0 → EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig →
    ∀ j, Nonempty (JointResidualLimits.OneSidedExtension (V j) x)
  pressure : ∀ x : Space, x 2 ≠ 0 → EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig →
    ∀ j, Nonempty (JointResidualLimits.OneSidedExtension (P j) x)

section InitialModels

variable {DA DP : Type} [NormedAddCommGroup DA] [NormedSpace ℝ DA]
  [NormedAddCommGroup DP] [NormedSpace ℝ DP] {IA KA IP KP : Type*}









end InitialModels

section RawFamilies

variable {DA DP : Type} [NormedAddCommGroup DA] [NormedSpace ℝ DA]
  [NormedAddCommGroup DP] [NormedSpace ℝ DP] {IA KA IP KP : Type*}




end RawFamilies

section ActualRun

variable {B N0 N : ℕ}
  {DP DS DA0 DP0 : Type}
  [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  [NormedAddCommGroup DS] [NormedSpace ℝ DS]
  [NormedAddCommGroup DA0] [NormedSpace ℝ DA0]
  [NormedAddCommGroup DP0] [NormedSpace ℝ DP0]
  {IP KP IS KS IA0 KA0 IP0 KP0 : Type*}


end ActualRun

end NavierStokes.ActualEndpointInputs


end


noncomputable section

namespace NavierStokes.GermEndpointInputs

open Set Function Filter ProblemStatement
open scoped Topology ContDiff


/-- Interior data for one actual physical field.  The exponent and logarithmic
loss may depend on the derivative order and on the field.  In particular this
record neither assumes an endpoint limit nor compares different stages. -/
structure PhysicalJets (h qbig : ℝ) {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f : SpaceTime → V) : Prop where
  smooth : ContDiffOn ℝ ∞ f (CutStageEstimates.physicalSublevel h qbig)
  bound : ∀ m : ℕ, ∃ C p e : ℝ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
    |w.1| ≤ 1 → PhysicalWaveSum.physicalQ h w ≤ 1 →
    ‖iteratedFDeriv ℝ m f w‖ ≤
      C * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ p *
        PhysicalWaveSum.physicalQ h w ^ e

namespace PhysicalJets

variable {h qbig : ℝ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {f : SpaceTime → V}

/-- Adapter for the power bounds of the current-band physical construction.
The time restriction is kept, as in the physical wave estimate. -/
theorem of_power
    (hf : ContDiffOn ℝ ∞ f (CutStageEstimates.physicalSublevel h qbig))
    (hb : ∀ m : ℕ, ∃ C e : ℝ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      |w.1| ≤ 1 → PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ e) :
    PhysicalJets h qbig f := by
  refine ⟨hf, fun m => ?_⟩
  obtain ⟨C, e, hm⟩ := hb m
  refine ⟨C, 0, e, fun w hw ht hq => ?_⟩
  simpa only [Real.rpow_zero, mul_one] using hm w hw ht hq

/-- The positive-index restriction in `RawStageBounds` is preserved. -/
theorem of_rawStage {A : ℕ → SpaceTime → V} {g L : ℕ → ℝ}
    {C p : ℕ → ℕ → ℝ}
    (hb : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) A g L C p
      (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig))
    {j : ℕ} (hj : 1 ≤ j)
    (hf : ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbig)) :
    PhysicalJets h qbig (A j) := by
  refine ⟨hf, fun m => ⟨C j m, p j m, g j - L m, ?_⟩⟩
  exact fun w hw _ hq => hb j hj m w ⟨hw.1, hw⟩ hq

/-- A smaller scale cap preserves the same constants. -/
theorem mono {qsmall : ℝ} (J : PhysicalJets h qbig f) (hq : qsmall ≤ qbig) :
    PhysicalJets h qsmall f := by
  have hsub : CutStageEstimates.physicalSublevel h qsmall ⊆
      CutStageEstimates.physicalSublevel h qbig :=
    fun _ hw => ⟨hw.1, hw.2.trans_le hq⟩
  exact ⟨J.smooth.mono hsub, fun m => by
    obtain ⟨C, p, e, hb⟩ := J.bound m
    exact ⟨C, p, e, fun w hw => hb w (hsub hw)⟩⟩

/-- Physical identities on the open validity region identify every actual
ordinary jet.  Values at a chart face or beyond the region are irrelevant. -/
theorem congr (J : PhysicalJets h qbig f) {g : SpaceTime → V}
    (hh : 0 < h) (hh1 : h < 1 / 2)
    (he : EqOn g f (CutStageEstimates.physicalSublevel h qbig)) :
    PhysicalJets h qbig g := by
  refine ⟨J.smooth.congr he, fun m => ?_⟩
  obtain ⟨C, p, e, hb⟩ := J.bound m
  refine ⟨C, p, e, fun w hw ht hq => ?_⟩
  have hloc : g =ᶠ[𝓝 w] f := by
    filter_upwards [(CutStageEstimates.physicalSublevel_open hh hh1 qbig).mem_nhds hw]
      with z hz
    exact he hz
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hloc m]
  exact hb w hw ht hq

/-- Finite sums retain derivative bounds without identifying a summand with
any copy-family construction. -/
theorem add (J : PhysicalJets h qbig f) {g : SpaceTime → V}
    (K : PhysicalJets h qbig g) (hh : 0 < h) (hh1 : h < 1 / 2) :
    PhysicalJets h qbig (fun w => f w + g w) := by
  refine ⟨J.smooth.add K.smooth, fun m => ?_⟩
  obtain ⟨C, p, e, hb⟩ := J.bound m
  obtain ⟨D, r, s, hk⟩ := K.bound m
  refine ⟨max C 0 + max D 0, max p r, min e s, fun w hw ht hq => ?_⟩
  have hq0 := PhysicalWaveSum.physicalQ_pos hh hh1 hw.1
  have hl : (1 : ℝ) ≤ 1 + |Real.log (PhysicalWaveSum.physicalQ h w)| := by
    linarith [abs_nonneg (Real.log (PhysicalWaveSum.physicalQ h w))]
  have hmono (C' p' e' : ℝ) (hp : p' ≤ max p r) (he : min e s ≤ e') :
      C' * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ p' *
          PhysicalWaveSum.physicalQ h w ^ e' ≤
        max C' 0 * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ max p r *
          PhysicalWaveSum.physicalQ h w ^ min e s := by
    calc
      _ ≤ max C' 0 * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ p' *
          PhysicalWaveSum.physicalQ h w ^ e' := by
        gcongr
        exact le_max_left _ _
      _ ≤ max C' 0 * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ max p r *
          PhysicalWaveSum.physicalQ h w ^ min e s := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hl hp) (le_max_right _ _)
        · exact Real.rpow_le_rpow_of_exponent_ge hq0 hq he
        · exact Real.rpow_nonneg hq0.le _
        · positivity
  calc
    _ ≤ ‖iteratedFDeriv ℝ m f w‖ + ‖iteratedFDeriv ℝ m g w‖ :=
      ResidualStability.norm_jet_add_le
        (CutStageEstimates.physicalSublevel_open hh hh1 qbig) J.smooth K.smooth hw m
    _ ≤ C * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ p *
          PhysicalWaveSum.physicalQ h w ^ e +
        D * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ r *
          PhysicalWaveSum.physicalQ h w ^ s := add_le_add (hb w hw ht hq) (hk w hw ht hq)
    _ ≤ _ := (add_le_add
      (hmono C p e (le_max_left _ _) (min_le_left _ _))
      (hmono D r s (le_max_right _ _) (min_le_right _ _))).trans_eq (by ring)

/-- This is an application of the existing local bounded-jet extension
theorem.  No new boundary regularity hypothesis is introduced. -/
theorem extension [CompleteSpace V] (J : PhysicalJets h qbig f)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : qbig ≤ 1)
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension f x) :=
  OffplaneJetExtensions.extension_of_powerLog_jets hh hh1 hqbig J.smooth J.bound hx hqx

end PhysicalJets

section MeanInputs

/-- The actual mean-pressure native bounds supply the single-field input. -/
theorem mean_field_jets {h degree qbig : ℝ}
    (M : ActualPhysicalStageBounds.MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand) :
    PhysicalJets h qbig M.family.field := by
  apply PhysicalJets.of_power (M.field_smooth hh hh1 hq)
  intro m
  obtain ⟨C, _, hb⟩ := M.field_bound hh hh1 hq m
  exact ⟨C, h * M.alpha - PhysicalMeanJetBounds.loss degree m, fun w hw _ => hb w hw⟩

/-- This applies to both actual mean-stream potentials and the direct angular
increments, with their own physical degree and their original first band. -/
theorem mean_angular_jets {h degree qbig : ℝ}
    (M : ActualPhysicalStageBounds.MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand) :
    PhysicalJets h qbig M.family.angularField := by
  apply PhysicalJets.of_power (M.angular_smooth hh hh1 hq)
  intro m
  obtain ⟨C, _, hb⟩ := M.angular_bound hh hh1 hq m
  exact ⟨C, h * M.alpha - PhysicalMeanJetBounds.loss degree m, fun w hw _ => hb w hw⟩

end MeanInputs

section ExistingWaveInputs

variable {h qbig : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {I K : Type*}

/-- Existing initial or signed wave data can be used for those summands.
No such data are requested for the glued particular summand. -/
theorem wave_vector_jets (W : PhysicalStageBounds.WaveData h D I K (Fin 3))
    (hh : 0 < h) (hh1 : h < 1 / 2) : PhysicalJets h qbig W.vector := by
  apply PhysicalJets.of_power ((W.vector_smooth hh hh1).mono inter_subset_left)
  intro m
  obtain ⟨C, _, hb⟩ := W.vector_bound hh hh1 m
  exact ⟨C, h * W.alpha - PhysicalClassBounds.physicalLoss h W.shift m,
    fun w hw _ => hb w hw.1⟩

theorem wave_pressure_jets (W : PhysicalStageBounds.WaveData h D I K Unit)
    (hh : 0 < h) (hh1 : h < 1 / 2) : PhysicalJets h qbig W.pressure := by
  apply PhysicalJets.of_power ((W.pressure_smooth hh hh1).mono inter_subset_left)
  intro m
  obtain ⟨C, _, hb⟩ := W.pressure_bound hh hh1 m
  exact ⟨C, h * W.alpha - PhysicalClassBounds.physicalLoss h W.shift m,
    fun w hw _ => hb w hw.1⟩

end ExistingWaveInputs

section InitialCorrections

open CorrectionInitialization.ActualPrimary

variable {DA DP : Type} [NormedAddCommGroup DA] [NormedSpace ℝ DA]
  [NormedAddCommGroup DP] [NormedSpace ℝ DP] {IA KA IP KP : Type*}

/-- The finite potential correction at index zero uses the actual initial
wave, temporal mean, and rank mean.  The slow-base gauge is excluded here. -/
theorem initial_potential_jets (B N0 N : ℕ) (hN : 4 ≤ N)
    (WA : PhysicalStageBounds.WaveData h DA IA KA (Fin 3))
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    PhysicalJets h qbig
      (fun w => WA.vector w + (ActualMeanPhysicalData.initialStreamFamily B N0 N).angularField w) := by
  have ht := mean_angular_jets
    (ActualPhysicalStageBounds.actualInitialTemporalInput B N0 N hN)
    outgoing.data.h_pos outgoing.data.h_lt_half hq
  have hr := mean_angular_jets
    (ActualPhysicalStageBounds.actualInitialRankInput B N0 N hN)
    outgoing.data.h_pos outgoing.data.h_lt_half hq
  apply ((wave_vector_jets WA outgoing.data.h_pos outgoing.data.h_lt_half).add
    (ht.add hr outgoing.data.h_pos outgoing.data.h_lt_half)
    outgoing.data.h_pos outgoing.data.h_lt_half).congr outgoing.data.h_pos outgoing.data.h_lt_half
  intro w _
  rw [ActualMeanPhysicalData.initialStream_angularField]
  rfl

theorem initial_direct_jets (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    PhysicalJets h qbig (ActualMeanPhysicalData.initialAngularFamily B N0 N).angularField :=
  mean_angular_jets (ActualPhysicalStageBounds.actualInitialAngularInput B N0 N hN)
    outgoing.data.h_pos outgoing.data.h_lt_half hq

/-- The finite initial pressure correction retains the actual initial
wave pressure and the pressure mean. -/
theorem initial_pressure_jets (B N0 N : ℕ) (hN : 4 ≤ N)
    (WP : PhysicalStageBounds.WaveData h DP IP KP Unit)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    PhysicalJets h qbig
      (fun w => WP.pressure w + (ActualMeanPhysicalData.initialPressureFamily B N0 N).field w) :=
  (wave_pressure_jets WP outgoing.data.h_pos outgoing.data.h_lt_half).add
    (mean_field_jets (ActualPhysicalStageBounds.actualInitialPressureInput B N0 N hN)
      outgoing.data.h_pos outgoing.data.h_lt_half hq)
    outgoing.data.h_pos outgoing.data.h_lt_half

end InitialCorrections


section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

/-- Bounds for literal raw fields imply all three candidate endpoint inputs.
The base gauge is never subjected to a growth assumption, and the positive
stage estimate is never applied to index zero. -/
theorem endpoints_of_bounds (upper : ℝ) (bandFloor : ℕ) {qbig : ℝ}
    (hqbig : qbig ≤ 1) {A V : ℕ → VelocityField} {P : ℕ → PressureField}
    {initial : VelocityField} {pInitial : PressureField}
    (hA0 : EqOn (A 0)
      (fun w => TailGaugePotential.finalPotential H v upper bandFloor w + initial w)
      (CutStageEstimates.physicalSublevel F.data.h qbig))
    (hP0 : EqOn (P 0)
      (fun w => FinalSlowBase.pressure H v upper bandFloor w + pInitial w)
      (CutStageEstimates.physicalSublevel F.data.h qbig))
    (Jinitial : PhysicalJets F.data.h qbig initial)
    (JpInitial : PhysicalJets F.data.h qbig pInitial)
    (JA : ∀ j, 1 ≤ j → PhysicalJets F.data.h qbig (A j))
    (JV : ∀ j, PhysicalJets F.data.h qbig (V j))
    (JP : ∀ j, 1 ≤ j → PhysicalJets F.data.h qbig (P j)) :
    ActualEndpointInputs.EndpointInputs F.data.h qbig A V P := by
  constructor
  · intro x hx hqx j
    cases j with
    | zero =>
        have hx0 : x ≠ 0 := by intro he; exact hx (by simp [he])
        apply OffplaneJetExtensions.extension_of_eqOn_sublevel
          F.data.h_pos F.data.h_lt_half hA0 hx hqx
        exact OffplaneJetExtensions.extension_add
          (TailGaugePotential.finalPotential_awayExtensions H v upper bandFloor x hx0)
          (Jinitial.extension F.data.h_pos F.data.h_lt_half hqbig hx hqx)
    | succ j =>
        exact (JA (j + 1) (Nat.succ_le_succ (Nat.zero_le j))).extension
          F.data.h_pos F.data.h_lt_half hqbig hx hqx
  · intro x hx hqx j
    exact (JV j).extension F.data.h_pos F.data.h_lt_half hqbig hx hqx
  · intro x hx hqx j
    cases j with
    | zero =>
        apply OffplaneJetExtensions.extension_of_eqOn_sublevel
          F.data.h_pos F.data.h_lt_half hP0 hx hqx
        exact OffplaneJetExtensions.extension_add
          ⟨SlowBaseEndpoint.finalPressureNonzeroAxial H v upper bandFloor hx⟩
          (JpInitial.extension F.data.h_pos F.data.h_lt_half hqbig hx hqx)
    | succ j =>
        exact (JP (j + 1) (Nat.succ_le_succ (Nat.zero_le j))).extension
          F.data.h_pos F.data.h_lt_half hqbig hx hqx

/-- Literal fields accepted by `GermCandidateAssembly`.  In particular
`stages j` may be a glued current-particular field plus signed and mean
corrections; there is no copy-family or potential-stage argument. -/
theorem germ_stage_endpoints (upper : ℝ) (bandFloor : ℕ) {qbig : ℝ}
    (hqbig : qbig ≤ 1) (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData
      (LocalAngularDiagonal.localSlowDomain F.data.h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (Jinitial : PhysicalJets F.data.h qbig initial)
    (Jstages : ∀ j, PhysicalJets F.data.h qbig (stages j))
    (JD : ∀ j, PhysicalJets F.data.h qbig (LocalAngularDiagonal.rawSeries D j))
    (JpInitial : PhysicalJets F.data.h qbig pInitial)
    (JpStages : ∀ j, PhysicalJets F.data.h qbig (pStages j)) :
    ActualEndpointInputs.EndpointInputs F.data.h qbig
      (GermCandidateAssembly.potentialStages H v upper bandFloor initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages H v upper bandFloor pInitial pStages) := by
  apply endpoints_of_bounds H v upper bandFloor hqbig
    (fun _ _ => rfl) (fun _ _ => MixedCandidateAssembly.pressureStages_zero ..)
    Jinitial JpInitial ?_ JD ?_
  · intro j hj
    cases j with
    | zero => omega
    | succ j => exact Jstages j
  · intro j hj
    cases j with
    | zero => omega
    | succ j => simpa only [MixedCandidateAssembly.pressureStages_succ] using JpStages j


end ActualBase

section ActualInitialChoice

open CorrectionInitialization.ActualPrimary

/-- The chosen initial potential supplies its own native wave data.  The
consumer does not have to provide or postulate such a witness. -/
theorem actual_initial_potential_jets (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    PhysicalJets h qbig
      (fun w => InitialPhysicalData.potential B N0 w +
        (ActualMeanPhysicalData.initialStreamFamily B N0 N).angularField w) := by
  simpa only [InitialPhysicalData.potentialWaveData_vector] using
    initial_potential_jets B N0 N hN (InitialPhysicalData.potentialWaveData B N0) hq

theorem actual_initial_pressure_jets (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    PhysicalJets h qbig
      (fun w => InitialPhysicalData.pressure B N0 w +
        (ActualMeanPhysicalData.initialPressureFamily B N0 N).field w) := by
  simpa only [InitialPhysicalData.pressureWaveData_pressure] using
    initial_pressure_jets B N0 N hN (InitialPhysicalData.pressureWaveData B N0) hq

/-- The same-choice mixed raw sequence has all endpoint inputs.  Positive
fields are arbitrary physical fields, including the genuine glued particular
fields.  Only their derived interior jet estimates are used.  Initialization
is bound to the actual initial wave and actual mean families by local field
identities, with no supplied wave-data or endpoint-extension witness. -/
theorem actual_germ_stage_endpoints (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)
    (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (hInitial : EqOn initial
      (fun w => InitialPhysicalData.potential B N0 w +
        (ActualMeanPhysicalData.initialStreamFamily B N0 N).angularField w)
      (CutStageEstimates.physicalSublevel h qbig))
    (hDirect : EqOn (LocalAngularDiagonal.rawSeries D 0)
      (ActualMeanPhysicalData.initialAngularFamily B N0 N).angularField
      (CutStageEstimates.physicalSublevel h qbig))
    (hPressure : EqOn pInitial
      (fun w => InitialPhysicalData.pressure B N0 w +
        (ActualMeanPhysicalData.initialPressureFamily B N0 N).field w)
      (CutStageEstimates.physicalSublevel h qbig))
    (Jstages : ∀ j, PhysicalJets h qbig (stages j))
    (Jdirect : ∀ j, 1 ≤ j → PhysicalJets h qbig (LocalAngularDiagonal.rawSeries D j))
    (JpStages : ∀ j, PhysicalJets h qbig (pStages j)) :
    ActualEndpointInputs.EndpointInputs h qbig
      (GermCandidateAssembly.potentialStages certificate modulation upper B initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages certificate modulation upper B pInitial pStages) := by
  apply germ_stage_endpoints certificate modulation upper B (hq.trans (ChartScales.Q_le_one N))
    initial stages D pInitial pStages
    ((actual_initial_potential_jets B N0 N hN hq).congr
      outgoing.data.h_pos outgoing.data.h_lt_half hInitial)
    Jstages ?_
    ((actual_initial_pressure_jets B N0 N hN hq).congr
      outgoing.data.h_pos outgoing.data.h_lt_half hPressure) JpStages
  intro j
  cases j with
  | zero =>
      exact (initial_direct_jets B N0 N hN hq).congr
        outgoing.data.h_pos outgoing.data.h_lt_half hDirect
  | succ j => exact Jdirect (j + 1) (Nat.succ_le_succ (Nat.zero_le j))

/-- A derived `StageEstimates` record is an alternative source of the
positive-stage estimates.  No quantitative conclusion or representation of
the glued particular field is added as a hypothesis here. -/
theorem actual_germ_stage_endpoints_of_estimates (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)
    (initial : VelocityField) (stages : ℕ → VelocityField)
    (D : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain h qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (E : MixedCandidateAssembly.StageEstimates h qbig
      (GermCandidateAssembly.potentialStages certificate modulation upper B initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages certificate modulation upper B pInitial pStages))
    (hInitial : EqOn initial
      (fun w => InitialPhysicalData.potential B N0 w +
        (ActualMeanPhysicalData.initialStreamFamily B N0 N).angularField w)
      (CutStageEstimates.physicalSublevel h qbig))
    (hDirect : EqOn (LocalAngularDiagonal.rawSeries D 0)
      (ActualMeanPhysicalData.initialAngularFamily B N0 N).angularField
      (CutStageEstimates.physicalSublevel h qbig))
    (hPressure : EqOn pInitial
      (fun w => InitialPhysicalData.pressure B N0 w +
        (ActualMeanPhysicalData.initialPressureFamily B N0 N).field w)
      (CutStageEstimates.physicalSublevel h qbig)) :
    ActualEndpointInputs.EndpointInputs h qbig
      (GermCandidateAssembly.potentialStages certificate modulation upper B initial stages)
      (LocalAngularDiagonal.rawSeries D)
      (MixedCandidateAssembly.pressureStages certificate modulation upper B pInitial pStages) := by
  apply actual_germ_stage_endpoints B N0 N hN hq initial stages D pInitial pStages
    hInitial hDirect hPressure
  · intro j
    exact PhysicalJets.of_rawStage E.potential_bound (Nat.succ_le_succ (Nat.zero_le j))
      (E.potential_smooth (j + 1))
  · intro j hj
    exact PhysicalJets.of_rawStage E.direct_bound hj (E.direct_smooth j)
  · intro j
    simpa only [MixedCandidateAssembly.pressureStages_succ] using
      PhysicalJets.of_rawStage E.pressure_bound (Nat.succ_le_succ (Nat.zero_le j))
        (E.pressure_smooth (j + 1))

end ActualInitialChoice

end NavierStokes.GermEndpointInputs

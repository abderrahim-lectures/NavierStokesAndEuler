import NavierStokes.LocalPotentialRebundle
import NavierStokes.LocalResidualFlatness
import NavierStokes.LocalScheduleWitness
import NavierStokes.ActualCandidateAssembly
import NavierStokes.LocalScaleApproach
import NavierStokes.LocalJetBounds
import NavierStokes.LocalAngularGrowth

/-!
# The local theorem, with all conclusions for the same fields

The finite-stage construction selects one schedule retaining all residual
orders. Its smooth endpoint extensions, angular asymptotic, and literal heat
exterior are then combined without choosing new fields for different clauses.
-/

/-! Merged from `NavierStokes.LocalPaperDomain`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # A common local domain for the paper's heat-exterior formula -/

noncomputable section

namespace NavierStokes.LocalPaperDomain

open Set Filter ProblemStatement CorrectionInitialization
open scoped Topology

def residualBand : ℕ :=
  ActualCandidateConstruction.residualBand ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold

def qstar (a : ℕ → ℕ) : ℝ :=
  min (ChartScales.Q residualBand) ((1 / 2) / (|(a 0 : ℝ)| + 1))

def innerEdge : ℝ := NominalConeAssembly.activeLeft ActualPrimary.nominal

def outerEdge : ℝ :=
  max innerEdge (max (NominalConeAssembly.activeRight ActualPrimary.nominal)
    (BaseExterior.nominalExteriorRadius ActualPrimary.nominal)) + 1

def radius (w : SpaceTime) : ℝ :=
  AxisymmetricFields.radialEnergy w.2 / PhysicalWaveSum.physicalQ ActualPrimary.h w


theorem qstar_pos (a : ℕ → ℕ) : 0 < qstar a :=
  lt_min (ChartScales.Q_pos _) (div_pos (by norm_num) (by positivity))

theorem innerEdge_pos : 0 < innerEdge := NominalConeAssembly.activeLeft_pos _

theorem innerEdge_lt_outerEdge : innerEdge < outerEdge := by
  have := le_max_left innerEdge
    (max (NominalConeAssembly.activeRight ActualPrimary.nominal)
      (BaseExterior.nominalExteriorRadius ActualPrimary.nominal))
  dsimp only [outerEdge]
  linarith

theorem exterior_conditions {a : ℕ → ℕ} {w : SpaceTime} (ht : w.1 < 1)
    (hq : PhysicalWaveSum.physicalQ ActualPrimary.h w < qstar a)
    (hX : outerEdge ≤ radius w) :
    w ∈ ActualExteriorPrefix.exteriorDomain residualBand ∧
      w ∈ BaseExterior.cartesianExterior ActualPrimary.h
        (BaseExterior.nominalExteriorRadius ActualPrimary.nominal) ∧
      |(a 0 : ℝ) * PhysicalWaveSum.physicalQ ActualPrimary.h w| < 1 / 2 := by
  have hright : NominalConeAssembly.activeRight ActualPrimary.nominal < radius w := by
    have h1 := le_max_left (NominalConeAssembly.activeRight ActualPrimary.nominal)
      (BaseExterior.nominalExteriorRadius ActualPrimary.nominal)
    have h2 := le_max_right innerEdge
      (max (NominalConeAssembly.activeRight ActualPrimary.nominal)
        (BaseExterior.nominalExteriorRadius ActualPrimary.nominal))
    dsimp only [outerEdge] at hX
    linarith
  have hext : BaseExterior.nominalExteriorRadius ActualPrimary.nominal < radius w := by
    have h1 := le_max_right (NominalConeAssembly.activeRight ActualPrimary.nominal)
      (BaseExterior.nominalExteriorRadius ActualPrimary.nominal)
    have h2 := le_max_right innerEdge
      (max (NominalConeAssembly.activeRight ActualPrimary.nominal)
        (BaseExterior.nominalExteriorRadius ActualPrimary.nominal))
    dsimp only [outerEdge] at hX
    linarith
  refine ⟨ActualExteriorPrefix.mem_exteriorDomain.mpr ⟨ht,
    hq.trans_le (min_le_left _ _), ?_⟩, ⟨ht, hext⟩, ?_⟩
  · intro ha
    exact (not_le_of_gt hright) ha.2
  · have hpos := PhysicalWaveSum.physicalQ_pos ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half ht
    have hδ := (lt_div_iff₀ (show 0 < |(a 0 : ℝ)| + 1 by positivity)).mp
      (hq.trans_le (min_le_right _ _))
    rw [abs_mul, abs_of_pos hpos]
    nlinarith

/-- The three strict exterior conditions persist on a neighborhood. -/
theorem exterior_conditions_eventually {a : ℕ → ℕ} {w : SpaceTime}
    (hw : w ∈ ActualExteriorPrefix.exteriorDomain residualBand)
    (he : w ∈ BaseExterior.cartesianExterior ActualPrimary.h
      (BaseExterior.nominalExteriorRadius ActualPrimary.nominal))
    (hc : |(a 0 : ℝ) * PhysicalWaveSum.physicalQ ActualPrimary.h w| < 1 / 2) :
    ∀ᶠ z in 𝓝 w,
      z ∈ ActualExteriorPrefix.exteriorDomain residualBand ∧
      z ∈ BaseExterior.cartesianExterior ActualPrimary.h
        (BaseExterior.nominalExteriorRadius ActualPrimary.nominal) ∧
      |(a 0 : ℝ) * PhysicalWaveSum.physicalQ ActualPrimary.h z| < 1 / 2 := by
  have hq := (PhysicalWaveSum.physicalQ_smoothAt ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half he.1).continuousAt
  filter_upwards [(ActualExteriorPrefix.exteriorDomain_open residualBand).mem_nhds hw,
    (BaseExterior.cartesianExterior_isOpen ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half _).mem_nhds he,
    ((hq.const_mul (a 0 : ℝ)).abs).eventually_lt_const hc] with z hz hez hcz
  exact ⟨hz, hez, hcz⟩

end NavierStokes.LocalPaperDomain


end


/-! Merged from `NavierStokes.LocalScheduleAngular`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# Solenoidality for every admissible actual schedule

The literal direct angular sum, its spatial localization, and the mixed
velocity retain their divergence equation for any selected schedule.
-/

noncomputable section

namespace NavierStokes.LocalScheduleAngular

open Set Filter ProblemStatement ActualCandidateAssembly
open CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff

abbrev Schedule (a : ℕ → ℕ) : Prop :=
  MixedCandidateWitness.SelectedSchedule h
    (ActualCandidateConstruction.qbig ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold)
    selectedPotentialStages selectedDirectStages selectedPressureStages a

abbrev potentialSum (a : ℕ → ℕ) : VelocityField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
    selectedPotentialStages

abbrev directSum (a : ℕ → ℕ) : VelocityField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
    selectedDirectStages

abbrev pressureSum (a : ℕ → ℕ) : PressureField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
    selectedPressureStages

theorem directSum_divergence {a : ℕ → ℕ} (ha : Schedule a)
    {w : SpaceTime} (ht : w.1 < 1) : spatialDivergence (directSum a) w.1 w.2 = 0 := by
  obtain ⟨_, hap, _, ham, hat, hgap, _, _⟩ := ha
  have ha0 : 0 < (a 0 : ℝ) := by exact_mod_cast hap 0
  have hamin (j : ℕ) : (a 0 : ℝ) ≤ (a j : ℝ) := by
    exact_mod_cast ham.monotone (Nat.zero_le j)
  exact LocalAngularDiagonal.angularSum_divergence outgoing.data.h_pos
    outgoing.data.h_lt_half
    (directData ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry)
    hat ha0 hamin (hgap 0) ht


theorem mixed_divergence {a : ℕ → ℕ} (ha : Schedule a)
    {w : SpaceTime} (ht : w.1 < 1) :
    spatialDivergence
      (fun y => SpatialCurl.spatialCurl (potentialSum a) y + directSum a y) w.1 w.2 = 0 := by
  have hs := ha.2.2.2.2.2.2.1
  have hA := hs.potential.contDiffAt (PhysicalWaveSum.preterminal_open.mem_nhds ht)
  have hB := hs.direct.contDiffAt (PhysicalWaveSum.preterminal_open.mem_nhds ht)
  have hc := SpatialCurl.contDiffAt_spatialCurl hA (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)
  rw [MixedPeriodicAssembly.spatialDivergence_add
    ((hc.comp w.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
    ((hB.comp w.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)),
    SpatialCurl.spatialDivergence_spatialCurl _ _ _
      ((hA.comp w.2 (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)),
    directSum_divergence ha ht, add_zero]

end NavierStokes.LocalScheduleAngular


end


noncomputable section

namespace NavierStokes.LocalPaper

open Set Filter ProblemStatement CorrectionInitialization
open scoped Topology ContDiff

/-- Uniform bounds on compact subsets of the closed past avoiding the one
singular point. This also covers compact positive-scale strips. -/
def UniformJetsOnCompacts {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : SpaceTime → V) : Prop :=
  ∀ K : Set SpaceTime, IsCompact K → (∀ w ∈ K, w.1 ≤ 1) →
    (1, (0 : Space)) ∉ K → ∀ n : ℕ,
      ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, w.1 < 1 → ‖iteratedFDeriv ℝ n f w‖ ≤ C

/-- Uniform derivative bounds on compact spatial sets with scale bounded
above and separated from zero, up to the one-sided terminal boundary. -/
def UniformJetsOnScaleStrips {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (h : ℝ) (f : SpaceTime → V) : Prop :=
  ∀ K : Set Space, IsCompact K → ∀ c c' : ℝ, 0 < c → ∀ n : ℕ,
    ∃ C : ℝ, 0 < C ∧ ∀ w : SpaceTime, w.1 < 1 → w.2 ∈ K →
      c ≤ PhysicalWaveSum.physicalQ h w → PhysicalWaveSum.physicalQ h w ≤ c' →
      ‖iteratedFDeriv ℝ n f w‖ ≤ C

/-- The paper's quantitative angular asymptotic at one fixed inner radius. -/
def AngularRayGrowth (h Xa : ℝ) (u : VelocityField) : Prop :=
  ∃ Xin : ℝ, 0 < Xin ∧ Xin < Xa ∧ ∃ e₀ C δ : ℝ,
    0 < e₀ ∧ 0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧
    ∀ τ : ℝ, 0 < τ → τ < δ →
      |τ ^ CoordinateAlgebra.A h * u (1 - τ, BaseAngularGrowth.ray Xin τ) 1 - e₀| ≤
        C * τ ^ (2 * h)

/-- Every clause of the local theorem. Smoothness on all `t < 1` and compact
jet bounds on the nonsingular closed past are stronger than their restrictions
to the paper's local positive-scale domain. `AwayExtensions` records actual
smooth extensions, so the endpoint derivatives are compatible. -/
structure Properties (h qstar Xa Xext heatNormalization : ℝ)
    (A D u : VelocityField) (p : PressureField) : Prop where
  exponent_small : 0 < h ∧ h < 1 / 100
  scale_positive : 0 < qstar
  edges_ordered : 0 < Xa ∧ Xa < Xext
  potential_smooth : ContDiffOn ℝ ∞ A PhysicalWaveSum.preterminal
  direct_smooth : ContDiffOn ℝ ∞ D PhysicalWaveSum.preterminal
  velocity_smooth : ContDiffOn ℝ ∞ u PhysicalWaveSum.preterminal
  pressure_smooth : ContDiffOn ℝ ∞ p PhysicalWaveSum.preterminal
  direct_angular : ∃ b : DirectAngularDiagonal.Coefficient,
    EqOn D (DirectAngularDiagonal.angularField b) PhysicalWaveSum.preterminal
  decomposition : ∀ w : SpaceTime, w.1 < 1 →
    u w = SpatialCurl.spatialCurl A w + D w
  divergence_free : ∀ w : SpaceTime, w.1 < 1 → spatialDivergence u w.1 w.2 = 0
  potential_extensions : JointResidualLimits.AwayExtensions A
  direct_extensions : JointResidualLimits.AwayExtensions D
  pressure_extensions : JointResidualLimits.AwayExtensions p
  potential_jets_bounded : UniformJetsOnScaleStrips h A
  direct_jets_bounded : UniformJetsOnScaleStrips h D
  pressure_jets_bounded : UniformJetsOnScaleStrips h p
  residual_flatness : ∀ m : ℕ, ∀ r : ℝ, 0 ≤ r → ∀ X : ℝ, 0 ≤ X →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ w : SpaceTime,
      w.1 < 1 → PhysicalWaveSum.physicalQ h w < δ →
      AxisymmetricFields.radialEnergy w.2 / PhysicalWaveSum.physicalQ h w ≤ X →
      ‖iteratedFDeriv ℝ m (fun z => navierStokesResidual u p z.1 z.2) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ r
  exterior : ∀ w : SpaceTime, w.1 < 1 → PhysicalWaveSum.physicalQ h w < qstar →
    Xext ≤ AxisymmetricFields.radialEnergy w.2 / PhysicalWaveSum.physicalQ h w →
      A w = 0 ∧ D w = BaseExterior.heatVelocity heatNormalization h w ∧
      p w = BaseExterior.heatPressureField heatNormalization h w ∧
      navierStokesResidual u p w.1 w.2 = 0
  angular_growth : AngularRayGrowth h Xa u


theorem uniformJetsOnScaleStrips_of_extensions {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f : SpaceTime → V} {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hf : ContDiffOn ℝ ∞ f PhysicalWaveSum.preterminal)
    (he : JointResidualLimits.AwayExtensions f) : UniformJetsOnScaleStrips h f := by
  intro K hK c c' hc n
  exact LocalJetBounds.uniform_jets_on_scale_strip (hf.mono (fun _ hw => hw.1)) he hh hh1 hK hc n

theorem selected_exterior_residual_zero {a : ℕ → ℕ}
    (ha : Tendsto (fun j => (a j : ℝ)) atTop atTop) {w : SpaceTime}
    (hw : w ∈ ActualExteriorPrefix.exteriorDomain LocalPaperDomain.residualBand)
    (he : w ∈ BaseExterior.cartesianExterior ActualPrimary.h
      (BaseExterior.nominalExteriorRadius ActualPrimary.nominal))
    (hc : |(a 0 : ℝ) * PhysicalWaveSum.physicalQ ActualPrimary.h w| < 1 / 2) :
    navierStokesResidual (LocalAngularGrowth.selectedRawVelocity a)
      (LocalPotentialRebundle.pressure a) w.1 w.2 = 0 := by
  have hnear := LocalPaperDomain.exterior_conditions_eventually hw he hc
  have hu : LocalAngularGrowth.selectedRawVelocity a =ᶠ[𝓝 w]
      FinalSlowBase.velocity ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper ActualCandidateConstruction.selectedBudget := by
    filter_upwards [hnear] with z hz
    exact LocalAngularGrowth.rawVelocity_eq_base
      (ActualCandidateAssembly.exteriorStages ActualCandidateConstruction.selectedBudget
        ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry)
      ha hz.1 hz.2.2
  have hp : LocalPotentialRebundle.pressure a =ᶠ[𝓝 w]
      FinalSlowBase.pressure ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper ActualCandidateConstruction.selectedBudget := by
    filter_upwards [hnear] with z hz
    exact LocalPotentialRebundle.pressure_eq_base hz.1 hz.2.2
  rw [ResidualRegularity.residual_congr hu hp]
  exact FinalSlowBase.exterior_residual_zero ActualPrimary.certificate ActualPrimary.modulation
    ActualPrimary.upper ActualCandidateConstruction.selectedBudget he

/-- All local properties are retained by any actual schedule with the proved
all-order residual bounds. -/
theorem properties_of_schedule {a : ℕ → ℕ} (hs : LocalScheduleWitness.Selected a)
    (hr : LocalResidualFlatness.AllResidualJetRates ActualPrimary.h
      ActualCandidateAssembly.selectedPotentialStages ActualCandidateAssembly.selectedDirectStages
      ActualCandidateAssembly.selectedPressureStages a) :
    Properties ActualPrimary.h (LocalPaperDomain.qstar a) LocalPaperDomain.innerEdge
      LocalPaperDomain.outerEdge (BaseExterior.nominalHeatNormalization ActualPrimary.nominal)
      (LocalPotentialRebundle.potential a) (LocalPotentialRebundle.direct a)
      (LocalAngularGrowth.selectedRawVelocity a) (LocalPotentialRebundle.pressure a) := by
  have hat := hs.2.2.2.2.1
  have hsm := hs.2.2.2.2.2.2.1
  obtain ⟨eA, eD, eP⟩ := LocalScheduleWitness.selected_awayExtensions hs
  obtain ⟨eA', eD'⟩ := LocalPotentialRebundle.awayExtensions eA eD
  have hAs := LocalPotentialRebundle.potential_smooth hsm
  have hDs := LocalPotentialRebundle.direct_smooth hsm
  refine {
    exponent_small := LocalAngularGrowth.selected_exponent_small
    scale_positive := LocalPaperDomain.qstar_pos a
    edges_ordered := ⟨LocalPaperDomain.innerEdge_pos, LocalPaperDomain.innerEdge_lt_outerEdge⟩
    potential_smooth := hAs
    direct_smooth := hDs
    velocity_smooth := MixedDiagonalResidual.velocity_smooth_of_sums hsm
    pressure_smooth := hsm.pressure
    direct_angular := ?_
    decomposition := fun w hw => (LocalPotentialRebundle.velocity_eq_original hsm hw).symm
    divergence_free := fun w hw => LocalScheduleAngular.mixed_divergence hs hw
    potential_extensions := eA'
    direct_extensions := eD'
    pressure_extensions := eP
    potential_jets_bounded := uniformJetsOnScaleStrips_of_extensions
      ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half hAs eA'
    direct_jets_bounded := uniformJetsOnScaleStrips_of_extensions
      ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half hDs eD'
    pressure_jets_bounded := uniformJetsOnScaleStrips_of_extensions
      ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half hsm.pressure eP
    residual_flatness := ?_
    exterior := ?_
    angular_growth := ?_
  }
  · exact ⟨LocalPotentialRebundle.angularScalar a,
      fun w hw => LocalPotentialRebundle.direct_eq_angularField hat hw⟩
  · intro m r hr0 X hX
    exact LocalScaleApproach.jetRate_uniform_small_scale ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half (hr m r hr0) X hX
  · intro w ht hq hX
    obtain ⟨hw, he, hc⟩ := LocalPaperDomain.exterior_conditions ht hq hX
    obtain ⟨hA, hD, hP⟩ := LocalPotentialRebundle.exterior hw he hc
    exact ⟨hA, hD, hP, selected_exterior_residual_zero hat hw he hc⟩
  · exact ⟨LocalAngularGrowth.innerRadius, LocalAngularGrowth.innerRadius_pos,
      LocalAngularGrowth.innerRadius_lt_left, LocalAngularGrowth.selectedRawVelocity_angularGrowth hat⟩

/-- The complete local theorem, with no finite-stage or schedule hypotheses. -/
theorem local_theorem :
    ∃ h qstar Xa Xext heatNormalization : ℝ,
      ∃ A D u : VelocityField, ∃ p : PressureField,
        Properties h qstar Xa Xext heatNormalization A D u p := by
  obtain ⟨a, hs, _, hr⟩ := LocalResidualFlatness.selected_schedule
  exact ⟨_, _, _, _, _, _, _, _, _, properties_of_schedule hs hr⟩

end NavierStokes.LocalPaper

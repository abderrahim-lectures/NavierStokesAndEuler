import NavierStokes.LocalAngularGrowth
import NavierStokes.TailGaugePotential
import NavierStokes.ActualCandidateAssembly
import NavierStokes.R3.ActualCandidate
import NavierStokes.PhysicalWaveSum
import NavierStokes.DiagonalResidual
import NavierStokes.SpacetimeEndpoint
import NavierStokes.JointResidualLimits
import NavierStokes.AnnularEndpoint
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# The local theorem, with all conclusions for the same fields

The finite-stage construction selects one schedule retaining all residual
orders. Its smooth endpoint extensions, angular asymptotic, and literal heat
exterior are then combined without choosing new fields for different clauses.
-/
/-! Merged from `NavierStokes.LocalPotentialRebundle`. -/
/-!
# The local paper's potential representation

The selected construction stores the base swirl in an axial potential.
Moving that axial component into the direct angular field preserves the
velocity and gives the paper's vanishing vector potential in the heat exterior.
-/
/-! Merged from `NavierStokes.LocalHeatExterior`. -/
/-!
# The axial part of the actual slow-base potential

The stream coefficients vanish in the proved heat exterior. Consequently the
anchored potential is purely axial there, and its axial projection has the
same spatial curl as the constructed slow base.
-/

noncomputable section

namespace NavierStokes.LocalHeatExterior

open Set Filter ProblemStatement
open scoped Topology ContDiff

/-- Projection of a potential onto its axial component. -/
noncomputable def axialPart (A : VelocityField) : VelocityField :=
  fun w => A w 2 • coordinateVector 2

theorem axialPart_smooth {A : VelocityField} {S : Set SpaceTime}
    (hA : ContDiffOn ℝ ∞ A S) : ContDiffOn ℝ ∞ (axialPart A) S := by
  exact ((AxisymmetricFields.projection 2).contDiff.comp_contDiffOn hA).smul_const
    (coordinateVector 2)

theorem axialPart_awayExtensions {A : VelocityField}
    (hA : JointResidualLimits.AwayExtensions A) :
    JointResidualLimits.AwayExtensions (axialPart A) := by
  intro x hx
  obtain ⟨e⟩ := hA x hx
  refine ⟨{
    value := axialPart e.value
    domain := e.domain
    isOpen := e.isOpen
    mem := e.mem
    smooth := axialPart_smooth e.smooth
    agrees := ?_ }⟩
  intro w hw
  exact congrArg (fun u : Space => u 2 • coordinateVector 2) (e.agrees hw)

theorem axialPart_potential (H K : AxisymmetricFields.Profile) :
    axialPart (AxisymmetricFields.potential H K) = AxisymmetricFields.potential (fun _ => 0) K := by
  ext w i
  fin_cases i <;> simp [axialPart, AxisymmetricFields.potential, coordinateVector]

theorem axialPotential_curl (K : AxisymmetricFields.Profile) {w : SpaceTime}
    (hK : DifferentiableAt ℝ K (AxisymmetricFields.profilePoint w.1 w.2)) :
    SpatialCurl.spatialCurl (AxisymmetricFields.potential (fun _ => 0) K) w =
      (-AxisymmetricFields.partialS K (AxisymmetricFields.profilePoint w.1 w.2)) •
        BaseResidual.angularVector w := by
  change AxisymmetricFields.velocity (fun _ => 0) K w = _
  ext i
  fin_cases i
  · change AxisymmetricFields.velocity (fun _ => 0) K (w.1, w.2) 0 = _
    rw [AxisymmetricFields.velocity_zero (fun _ => 0) K w.1 w.2 (differentiableAt_const 0) hK]
    simp [AxisymmetricFields.partialZ, BaseResidual.angularVector, coordinateVector]
    ring
  · change AxisymmetricFields.velocity (fun _ => 0) K (w.1, w.2) 1 = _
    rw [AxisymmetricFields.velocity_one (fun _ => 0) K w.1 w.2 (differentiableAt_const 0) hK]
    simp [AxisymmetricFields.partialZ, BaseResidual.angularVector, coordinateVector]
    ring
  · change AxisymmetricFields.velocity (fun _ => 0) K (w.1, w.2) 2 = _
    rw [AxisymmetricFields.velocity_two (fun _ => 0) K w.1 w.2 (differentiableAt_const 0) hK]
    simp [AxisymmetricFields.partialS, BaseResidual.angularVector, coordinateVector]

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

/-- The angular coefficient of the curl of the axial projection. -/
noncomputable def axialCurlCoefficient (upper : ℝ) (B : ℕ) : AxisymmetricFields.Profile :=
  fun p => -AxisymmetricFields.partialS
    (TailGaugePotential.gaugedSwirl (FinalSlowBase.scales H v upper B) F.data.h
      W.axis.normalization (FinalSlowBase.coefficients H v)) p


theorem axialPart_finalPotential_curl_angular (upper : ℝ) (B : ℕ) {w : SpaceTime}
    (ht : w.1 < 1) :
    SpatialCurl.spatialCurl (axialPart (TailGaugePotential.finalPotential H v upper B)) w =
      axialCurlCoefficient H v upper B (AxisymmetricFields.profilePoint w.1 w.2) •
        BaseResidual.angularVector w := by
  unfold TailGaugePotential.finalPotential TailGaugePotential.potential
  rw [axialPart_potential]
  exact axialPotential_curl _
    ((TailGaugePotential.gaugedSwirl_smoothAt (FinalSlowBase.scales_strictMono H v upper B)
      F.data.h_pos F.data.h_lt_half (FinalSlowBase.coefficients_smooth H v) ht).differentiableAt
      (by simp))

theorem finalPotential_eq_axialPart (upper : ℝ) (B : ℕ) {w : SpaceTime}
    (hw : w ∈ BaseExterior.cartesianExterior F.data.h (BaseExterior.nominalExteriorRadius W)) :
    TailGaugePotential.finalPotential H v upper B w =
      axialPart (TailGaugePotential.finalPotential H v upper B) w := by
  have hext := ModulatedExterior.realized_exterior_coefficients W v.profiles v.finiteModification
    (FinalSlowBase.realizesScheme H v) (EntranceAlignedBase.modulated_base_eq H v)
    (EntranceAlignedBase.modulated_outer H v)
  have hzero := BaseExterior.exterior_stream_zero
    (a := FinalSlowBase.scales H v upper B) (C := W.axis.normalization)
    (p := AxisymmetricFields.profilePoint w.1 w.2)
    F.data.h_pos F.data.h_lt_half (BaseExterior.nominalExteriorRadius_pos W).le hext hw
  have he : TailGaugePotential.finalPotential H v upper B w =
      TailGaugePotential.gaugedSwirl (FinalSlowBase.scales H v upper B) F.data.h
        W.axis.normalization (FinalSlowBase.coefficients H v)
        (AxisymmetricFields.profilePoint w.1 w.2) • coordinateVector 2 := by
    simp only [TailGaugePotential.finalPotential, TailGaugePotential.potential,
      AxisymmetricFields.potential, hzero, mul_zero, zero_smul, zero_add]
  unfold axialPart
  rw [he]
  simp [coordinateVector]


theorem axialPart_finalPotential_germ (upper : ℝ) (B : ℕ) {w : SpaceTime}
    (hw : w ∈ BaseExterior.cartesianExterior F.data.h (BaseExterior.nominalExteriorRadius W)) :
    axialPart (TailGaugePotential.finalPotential H v upper B) =ᶠ[𝓝 w]
      TailGaugePotential.finalPotential H v upper B := by
  filter_upwards [(BaseExterior.cartesianExterior_isOpen F.data.h_pos F.data.h_lt_half
    (BaseExterior.nominalExteriorRadius W)).mem_nhds hw] with y hy
  exact (finalPotential_eq_axialPart H v upper B hy).symm

theorem axialPart_finalPotential_curl (upper : ℝ) (B : ℕ) {w : SpaceTime}
    (hw : w ∈ BaseExterior.cartesianExterior F.data.h (BaseExterior.nominalExteriorRadius W)) :
    SpatialCurl.spatialCurl (axialPart (TailGaugePotential.finalPotential H v upper B)) w =
      FinalSlowBase.velocity H v upper B w := by
  rw [(SolenoidalDiagonal.spatialCurl_eventuallyEq
    (axialPart_finalPotential_germ H v upper B hw)).self_of_nhds]
  exact TailGaugePotential.finalPotential_sameCurl H v upper B hw.1



end ActualBase

end NavierStokes.LocalHeatExterior

/-! Merged from `NavierStokes.LocalAngularScalar` (in a section, so its `open`s cannot leak). -/
section
/-!
# A scalar representation of the selected direct angular field

The same locally finite cutoffs can be summed as scalar cylindrical
coefficients. The resulting scalar is independent of the polar angle, and
its angular vector field is the actual selected direct sum.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace NavierStokes.LocalAngularScalar

open ProblemStatement DirectAngularDiagonal CorrectionInitialization

def angularDirection (w : SpaceTime) : Space :=
  (-w.2 1 / radius w) • coordinateVector 0 +
    (w.2 0 / radius w) • coordinateVector 1

theorem angularField_eq_smul (b : Coefficient) (w : SpaceTime) :
    angularField b w = b (cylPoint w) • angularDirection w := by
  simp only [angularField, angularDirection, smul_add, smul_smul]
  rw [mul_comm (b (cylPoint w)) (-w.2 1 / radius w),
    mul_comm (b (cylPoint w)) (w.2 0 / radius w)]

theorem angularField_add (b c : Coefficient) :
    angularField (fun p => b p + c p) = fun w => angularField b w + angularField c w := by
  funext w
  simp only [angularField_eq_smul, add_smul]

/-- Convert a smooth coefficient of the Cartesian rotation vector into its
physical angular magnitude in cylindrical coordinates. -/
def magnitudeOfProfile (F : AxisymmetricFields.Profile) : Coefficient :=
  fun p => p.2.1 * F (p.1, (p.2.1 ^ 2 / 2, p.2.2))

theorem angularField_magnitudeOfProfile (F : AxisymmetricFields.Profile) (w : SpaceTime) :
    angularField (magnitudeOfProfile F) w =
      F (AxisymmetricFields.profilePoint w.1 w.2) • BaseResidual.angularVector w := by
  have hrsq : radius w ^ 2 = w.2 0 ^ 2 + w.2 1 ^ 2 :=
    PolarCharts.radius_sq (PhysicalGraphBounds.radialProjection w)
  have hval : magnitudeOfProfile F (cylPoint w) =
      radius w * F (AxisymmetricFields.profilePoint w.1 w.2) := by
    simp only [magnitudeOfProfile, cylPoint, hrsq, AxisymmetricFields.profilePoint,
      AxisymmetricFields.radialEnergy]
  simp only [angularField, hval, BaseResidual.angularVector, smul_add, smul_smul]
  by_cases hr : radius w = 0
  · have hx0 : w.2 0 = 0 := by rw [hr] at hrsq; nlinarith [sq_nonneg (w.2 1)]
    have hx1 : w.2 1 = 0 := by rw [hr] at hrsq; nlinarith [sq_nonneg (w.2 0)]
    simp only [hx0, hx1, neg_zero, zero_div, zero_mul, mul_zero, zero_smul, add_zero]
  · have h0 : (-w.2 1 / radius w) *
        (radius w * F (AxisymmetricFields.profilePoint w.1 w.2)) =
          F (AxisymmetricFields.profilePoint w.1 w.2) * -w.2 1 := by
      field_simp [hr]
    have h1 : (w.2 0 / radius w) *
        (radius w * F (AxisymmetricFields.profilePoint w.1 w.2)) =
          F (AxisymmetricFields.profilePoint w.1 w.2) * w.2 0 := by
      field_simp [hr]
    rw [h0, h1]

def scalarSum (a : ℕ → ℝ) (q : Coefficient) (b : ℕ → Coefficient) : Coefficient :=
  fun p => ∑' j : ℕ, SmoothCutoffs.scaledCutoff (a j) (q p) * b j p

/-- Local finiteness of the cutoff series justifies pulling the angular
direction through the scalar sum, including at the axis. -/
theorem angularSum_eq_scalarSum {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    (q : Coefficient) (b : ℕ → Coefficient) {w : SpaceTime}
    (hq : ContinuousAt (fun y : SpaceTime => q (cylPoint y)) w)
    (hpos : 0 < q (cylPoint w)) :
    angularSum a (fun y => q (cylPoint y)) b w = angularField (scalarSum a q b) w := by
  have hs : Summable (fun j : ℕ =>
      SmoothCutoffs.scaledCutoff (a j) (q (cylPoint w)) * b j (cylPoint w)) := by
    simpa only [SolenoidalDiagonal.cutStage, smul_eq_mul] using
      SolenoidalDiagonal.summable_cutStage ha hq hpos
        (fun j (y : SpaceTime) => b j (cylPoint y))
  simp only [angularSum, SolenoidalDiagonal.potentialSum, SolenoidalDiagonal.cutStage,
    angularField_eq_smul, smul_smul]
  rw [hs.tsum_smul_const]
  rfl

def selectedScalar (a : ℕ → ℕ) : Coefficient :=
  scalarSum (fun j => (a j : ℝ)) (qCoefficient ActualPrimary.h)
    (fun j => (ActualCandidateAssembly.directData ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold
      ActualCandidateConstruction.selectedThreshold_geometry j).scalar)

/-- The actual selected direct sum is one axisymmetric scalar times the
angular unit vector on the entire preterminal domain. -/
theorem selectedDirect_eq_angularField {a : ℕ → ℕ}
    (ha : Tendsto (fun j => (a j : ℝ)) atTop atTop) :
    EqOn (LocalAngularGrowth.selectedDirect a) (angularField (selectedScalar a))
      PhysicalWaveSum.preterminal := by
  intro w hw
  have hq : ContinuousAt (fun y : SpaceTime => qCoefficient ActualPrimary.h (cylPoint y)) w :=
    (PhysicalWaveSum.physicalQ_smoothAt ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half hw).continuousAt
  have hpos : 0 < qCoefficient ActualPrimary.h (cylPoint w) :=
    PhysicalWaveSum.physicalQ_pos ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half hw
  exact angularSum_eq_scalarSum ha (qCoefficient ActualPrimary.h)
    (fun j => (ActualCandidateAssembly.directData ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold
      ActualCandidateConstruction.selectedThreshold_geometry j).scalar) hq hpos

end NavierStokes.LocalAngularScalar
end


noncomputable section

namespace NavierStokes.LocalPotentialRebundle

open Set Filter ProblemStatement CorrectionInitialization
open scoped Topology ContDiff

abbrev basePotential : VelocityField :=
  TailGaugePotential.finalPotential ActualPrimary.certificate ActualPrimary.modulation
    ActualPrimary.upper ActualCandidateConstruction.selectedBudget

def removedPotential : VelocityField := LocalHeatExterior.axialPart basePotential

def potential (a : ℕ → ℕ) : VelocityField :=
  fun w => LocalAngularGrowth.selectedPotential a w - removedPotential w

def direct (a : ℕ → ℕ) : VelocityField :=
  fun w => LocalAngularGrowth.selectedDirect a w + SpatialCurl.spatialCurl removedPotential w

def pressure (a : ℕ → ℕ) : PressureField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
    (PhysicalWaveSum.physicalQ ActualPrimary.h) ActualCandidateAssembly.selectedPressureStages

def velocity (a : ℕ → ℕ) : VelocityField :=
  MixedPeriodicAssembly.velocity (potential a) (direct a)

/-- The tangential magnitude is a scalar in cylindrical `(t,r,z)` coordinates. -/
def angularScalar (a : ℕ → ℕ) : DirectAngularDiagonal.Coefficient :=
  fun p => LocalAngularScalar.selectedScalar a p +
    LocalAngularScalar.magnitudeOfProfile
      (LocalHeatExterior.axialCurlCoefficient ActualPrimary.certificate
        ActualPrimary.modulation ActualPrimary.upper ActualCandidateConstruction.selectedBudget) p

theorem direct_eq_angularField {a : ℕ → ℕ}
    (ha : Tendsto (fun j => (a j : ℝ)) atTop atTop) {w : SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal) :
    direct a w = DirectAngularDiagonal.angularField (angularScalar a) w := by
  change direct a w = DirectAngularDiagonal.angularField
    (fun p => LocalAngularScalar.selectedScalar a p +
      LocalAngularScalar.magnitudeOfProfile
        (LocalHeatExterior.axialCurlCoefficient ActualPrimary.certificate
          ActualPrimary.modulation ActualPrimary.upper ActualCandidateConstruction.selectedBudget) p) w
  rw [LocalAngularScalar.angularField_add]
  dsimp only
  change LocalAngularGrowth.selectedDirect a w + SpatialCurl.spatialCurl removedPotential w = _
  rw [LocalAngularScalar.selectedDirect_eq_angularField ha hw,
    LocalAngularScalar.angularField_magnitudeOfProfile]
  exact congrArg (fun v : Space =>
    DirectAngularDiagonal.angularField (LocalAngularScalar.selectedScalar a) w + v)
    (LocalHeatExterior.axialPart_finalPotential_curl_angular ActualPrimary.certificate
      ActualPrimary.modulation ActualPrimary.upper ActualCandidateConstruction.selectedBudget hw)

theorem spatialCurl_sub {A J : VelocityField} {w : SpaceTime}
    (hA : ContDiffAt ℝ ∞ A w) (hJ : ContDiffAt ℝ ∞ J w) :
    SpatialCurl.spatialCurl (fun z => A z - J z) w =
      SpatialCurl.spatialCurl A w - SpatialCurl.spatialCurl J w := by
  exact BaseResidual.spatialCurl_sub
    (hA.differentiableAt (by simp)) (hJ.differentiableAt (by simp))

theorem removedPotential_smooth : ContDiffOn ℝ ∞ removedPotential PhysicalWaveSum.preterminal :=
  LocalHeatExterior.axialPart_smooth
    ((TailGaugePotential.finalPotential_smooth ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.upper ActualCandidateConstruction.selectedBudget).mono
        (fun _ hw => ⟨hw, mem_univ _⟩))

theorem potential_smooth {a : ℕ → ℕ}
    (hs : MixedDiagonalSchedule.ThreeSmoothSums a ActualPrimary.h
      ActualCandidateAssembly.selectedPotentialStages ActualCandidateAssembly.selectedDirectStages
      ActualCandidateAssembly.selectedPressureStages) :
    ContDiffOn ℝ ∞ (potential a) PhysicalWaveSum.preterminal :=
  hs.potential.sub removedPotential_smooth

theorem direct_smooth {a : ℕ → ℕ}
    (hs : MixedDiagonalSchedule.ThreeSmoothSums a ActualPrimary.h
      ActualCandidateAssembly.selectedPotentialStages ActualCandidateAssembly.selectedDirectStages
      ActualCandidateAssembly.selectedPressureStages) :
    ContDiffOn ℝ ∞ (direct a) PhysicalWaveSum.preterminal := by
  intro w hw
  exact ((hs.direct.contDiffAt (PhysicalWaveSum.preterminal_open.mem_nhds hw)).add
    (SpatialCurl.contDiffAt_spatialCurl
      (removedPotential_smooth.contDiffAt (PhysicalWaveSum.preterminal_open.mem_nhds hw))
      (by simp))).contDiffWithinAt

theorem velocity_eq_original {a : ℕ → ℕ}
    (hs : MixedDiagonalSchedule.ThreeSmoothSums a ActualPrimary.h
      ActualCandidateAssembly.selectedPotentialStages ActualCandidateAssembly.selectedDirectStages
      ActualCandidateAssembly.selectedPressureStages) {w : SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal) :
    velocity a w = MixedPeriodicAssembly.velocity
      (LocalAngularGrowth.selectedPotential a) (LocalAngularGrowth.selectedDirect a) w := by
  change SpatialCurl.spatialCurl
    (fun z => LocalAngularGrowth.selectedPotential a z - removedPotential z) w + direct a w = _
  rw [spatialCurl_sub (A := LocalAngularGrowth.selectedPotential a)
    (hs.potential.contDiffAt (PhysicalWaveSum.preterminal_open.mem_nhds hw))
    (removedPotential_smooth.contDiffAt (PhysicalWaveSum.preterminal_open.mem_nhds hw))]
  simp only [direct, MixedPeriodicAssembly.velocity]
  abel



theorem sum_eq_first {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : ℕ → SpaceTime → V} {f : SpaceTime → V} {a : ℕ → ℝ}
    {q : SpaceTime → ℝ} {w : SpaceTime}
    (h0 : A 0 w = f w) (hz : ∀ k, A (k + 1) w = 0)
    (hsmall : |a 0 * q w| < 1 / 2) :
    SolenoidalDiagonal.potentialSum a q A w = f w := by
  rw [SolenoidalDiagonal.potentialSum, tsum_eq_single 0]
  · simp only [SolenoidalDiagonal.cutStage,
      (SmoothCutoffs.scaledCutoff_eventually_one hsmall).self_of_nhds, one_smul, h0]
  · intro j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp only [SolenoidalDiagonal.cutStage, hz k, smul_zero]

theorem selectedPotential_eq_base {a : ℕ → ℕ} {w : SpaceTime}
    (hw : w ∈ ActualExteriorPrefix.exteriorDomain
      (ActualCandidateConstruction.residualBand ActualCandidateConstruction.selectedBudget
        ActualCandidateConstruction.selectedThreshold))
    (hsmall : |(a 0 : ℝ) * PhysicalWaveSum.physicalQ ActualPrimary.h w| < 1 / 2) :
    LocalAngularGrowth.selectedPotential a w = basePotential w := by
  have H := ActualCandidateAssembly.exteriorStages ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry
  exact sum_eq_first (H.potential_zero hw) (fun k => H.potential_succ k hw) hsmall

theorem selectedDirect_eq_zero {a : ℕ → ℕ} {w : SpaceTime}
    (hw : w ∈ ActualExteriorPrefix.exteriorDomain
      (ActualCandidateConstruction.residualBand ActualCandidateConstruction.selectedBudget
        ActualCandidateConstruction.selectedThreshold)) :
    LocalAngularGrowth.selectedDirect a w = 0 := by
  have H := ActualCandidateAssembly.exteriorStages ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry
  have hz (j : ℕ) : ActualCandidateAssembly.selectedDirectStages j w = 0 := H.direct_zero j hw
  simp only [LocalAngularGrowth.selectedDirect, SolenoidalDiagonal.potentialSum,
    SolenoidalDiagonal.cutStage, hz, smul_zero, tsum_zero]

theorem pressure_eq_base {a : ℕ → ℕ} {w : SpaceTime}
    (hw : w ∈ ActualExteriorPrefix.exteriorDomain
      (ActualCandidateConstruction.residualBand ActualCandidateConstruction.selectedBudget
        ActualCandidateConstruction.selectedThreshold))
    (hsmall : |(a 0 : ℝ) * PhysicalWaveSum.physicalQ ActualPrimary.h w| < 1 / 2) :
    pressure a w = FinalSlowBase.pressure ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.upper ActualCandidateConstruction.selectedBudget w := by
  have H := ActualCandidateAssembly.exteriorStages ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry
  exact sum_eq_first (H.pressure_zero hw) (fun k => H.pressure_succ k hw) hsmall

/-- All three fields have the literal heat-exterior representation from
the local theorem, after transferring the axial potential to direct swirl. -/
theorem exterior {a : ℕ → ℕ} {w : SpaceTime}
    (hw : w ∈ ActualExteriorPrefix.exteriorDomain
      (ActualCandidateConstruction.residualBand ActualCandidateConstruction.selectedBudget
        ActualCandidateConstruction.selectedThreshold))
    (he : w ∈ BaseExterior.cartesianExterior ActualPrimary.h
      (BaseExterior.nominalExteriorRadius ActualPrimary.nominal))
    (hsmall : |(a 0 : ℝ) * PhysicalWaveSum.physicalQ ActualPrimary.h w| < 1 / 2) :
    potential a w = 0 ∧
      direct a w = BaseExterior.heatVelocity
        (BaseExterior.nominalHeatNormalization ActualPrimary.nominal) ActualPrimary.h w ∧
      pressure a w = BaseExterior.heatPressureField
        (BaseExterior.nominalHeatNormalization ActualPrimary.nominal) ActualPrimary.h w := by
  refine ⟨?_, ?_, ?_⟩
  · rw [potential, selectedPotential_eq_base hw hsmall]
    exact sub_eq_zero.mpr (LocalHeatExterior.finalPotential_eq_axialPart
      ActualPrimary.certificate ActualPrimary.modulation ActualPrimary.upper
      ActualCandidateConstruction.selectedBudget he)
  · rw [direct, selectedDirect_eq_zero hw, zero_add]
    exact (LocalHeatExterior.axialPart_finalPotential_curl ActualPrimary.certificate
      ActualPrimary.modulation ActualPrimary.upper ActualCandidateConstruction.selectedBudget he).trans
      ((FinalSlowBase.exterior_fields_eq_heat ActualPrimary.certificate
        ActualPrimary.modulation ActualPrimary.upper ActualCandidateConstruction.selectedBudget).1 he)
  · exact (pressure_eq_base hw hsmall).trans
      ((FinalSlowBase.exterior_fields_eq_heat ActualPrimary.certificate
        ActualPrimary.modulation ActualPrimary.upper ActualCandidateConstruction.selectedBudget).2 he)

theorem extension_sub {A J : VelocityField} {x : Space}
    (eA : JointResidualLimits.OneSidedExtension A x)
    (eJ : JointResidualLimits.OneSidedExtension J x) :
    Nonempty (JointResidualLimits.OneSidedExtension (fun w => A w - J w) x) := by
  refine ⟨{ value := fun w => eA.value w - eJ.value w
            domain := eA.domain ∩ eJ.domain
            isOpen := eA.isOpen.inter eJ.isOpen
            mem := ⟨eA.mem, eJ.mem⟩
            smooth := (eA.smooth.mono inter_subset_left).sub (eJ.smooth.mono inter_subset_right)
            agrees := ?_ }⟩
  intro w hw
  dsimp only
  rw [eA.agrees ⟨hw.1.1, hw.2⟩, eJ.agrees ⟨hw.1.2, hw.2⟩]

theorem extension_add {A J : VelocityField} {x : Space}
    (eA : JointResidualLimits.OneSidedExtension A x)
    (eJ : JointResidualLimits.OneSidedExtension J x) :
    Nonempty (JointResidualLimits.OneSidedExtension (fun w => A w + J w) x) := by
  refine ⟨{ value := fun w => eA.value w + eJ.value w
            domain := eA.domain ∩ eJ.domain
            isOpen := eA.isOpen.inter eJ.isOpen
            mem := ⟨eA.mem, eJ.mem⟩
            smooth := (eA.smooth.mono inter_subset_left).add (eJ.smooth.mono inter_subset_right)
            agrees := ?_ }⟩
  intro w hw
  dsimp only
  rw [eA.agrees ⟨hw.1.1, hw.2⟩, eJ.agrees ⟨hw.1.2, hw.2⟩]

theorem extension_curl {A : VelocityField} {x : Space}
    (eA : JointResidualLimits.OneSidedExtension A x) :
    Nonempty (JointResidualLimits.OneSidedExtension (SpatialCurl.spatialCurl A) x) := by
  refine ⟨{ value := SpatialCurl.spatialCurl eA.value
            domain := eA.domain
            isOpen := eA.isOpen
            mem := eA.mem
            smooth := ?_
            agrees := ?_ }⟩
  · intro w hw
    exact (SpatialCurl.contDiffAt_spatialCurl
      (eA.smooth.contDiffAt (eA.isOpen.mem_nhds hw)) (by simp)).contDiffWithinAt
  · intro w hw
    have hnear : eA.value =ᶠ[𝓝 w] A := by
      filter_upwards [(eA.isOpen.inter (SpacetimeEndpoint.openPast_isOpen 1)).mem_nhds hw]
        with z hz
      exact eA.agrees hz
    exact SolenoidalDiagonal.spatialCurl_eq_of_eventuallyEq hnear

theorem removedPotential_awayExtensions : JointResidualLimits.AwayExtensions removedPotential :=
  LocalHeatExterior.axialPart_awayExtensions
    (TailGaugePotential.finalPotential_awayExtensions ActualPrimary.certificate
      ActualPrimary.modulation ActualPrimary.upper ActualCandidateConstruction.selectedBudget)

theorem awayExtensions {a : ℕ → ℕ}
    (eA : JointResidualLimits.AwayExtensions (LocalAngularGrowth.selectedPotential a))
    (eD : JointResidualLimits.AwayExtensions (LocalAngularGrowth.selectedDirect a)) :
    JointResidualLimits.AwayExtensions (potential a) ∧
      JointResidualLimits.AwayExtensions (direct a) := by
  constructor
  · intro x hx
    exact extension_sub (Classical.choice (eA x hx))
      (Classical.choice (removedPotential_awayExtensions x hx))
  · intro x hx
    exact extension_add (Classical.choice (eD x hx))
      (Classical.choice (extension_curl (Classical.choice (removedPotential_awayExtensions x hx))))

end NavierStokes.LocalPotentialRebundle

/-! Merged from `NavierStokes.LocalScaleGeometry` (in a section, so its `open`s cannot leak). -/
section
/-!
# Spatial and temporal bounds in terms of the physical similarity scale

A bound on the similarity radius, together with a small physical scale,
forces the spacetime point to approach the singular point `(1, 0)`.
-/

noncomputable section

namespace NavierStokes.LocalScaleGeometry

open PhysicalWaveSum (physicalQ)

abbrev SpaceTime := ProblemStatement.SpaceTime

/-- The equation defining the physical similarity coordinate. -/
theorem physicalQ_equation {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (ht : w.1 < 1) :
    physicalQ h w - (w.2 2) ^ 2 * physicalQ h w ^ (2 * h) = 1 - w.1 := by
  exact (SimilarityCoordinates.coordinateQ_spec (by linarith) (by linarith)
    (p := (1 - w.1, w.2 2)) (sub_pos.mpr ht)).2

/-- The time distance to the terminal time is bounded by the scale. -/
theorem time_dist_le {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (ht : w.1 < 1) : |w.1 - 1| ≤ physicalQ h w := by
  have he := physicalQ_equation hh hh1 ht
  have hq := PhysicalWaveSum.physicalQ_pos hh hh1 ht
  have hp : 0 ≤ (w.2 2) ^ 2 * physicalQ h w ^ (2 * h) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hq.le _)
  rw [abs_of_neg (sub_neg.mpr ht)]
  linarith

/-- The axial coordinate shrinks with a positive power of the scale. -/
theorem axial_sq_le {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (ht : w.1 < 1) :
    (w.2 2) ^ 2 ≤ physicalQ h w ^ (1 - 2 * h) := by
  have he := physicalQ_equation hh hh1 ht
  have hq := PhysicalWaveSum.physicalQ_pos hh hh1 ht
  have hp := Real.rpow_pos_of_pos hq (2 * h)
  have hproduct : physicalQ h w ^ (2 * h) * physicalQ h w ^ (1 - 2 * h) =
      physicalQ h w := by
    rw [← Real.rpow_add hq, show 2 * h + (1 - 2 * h) = 1 by ring, Real.rpow_one]
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [hproduct]
  linarith

/-- Bounded similarity radius and vanishing scale force the spatial norm
to vanish. No sign assumption on the radius bound is needed here. -/
theorem spatial_norm_sq_le {h X1 : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (ht : w.1 < 1)
    (hX : AxisymmetricFields.radialEnergy w.2 / physicalQ h w ≤ X1) :
    ‖w.2‖ ^ 2 ≤ 2 * X1 * physicalQ h w + physicalQ h w ^ (1 - 2 * h) := by
  have hq := PhysicalWaveSum.physicalQ_pos hh hh1 ht
  have hr := (div_le_iff₀ hq).mp hX
  have hz := axial_sq_le hh hh1 ht
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  dsimp only [AxisymmetricFields.radialEnergy] at hr
  nlinarith

end NavierStokes.LocalScaleGeometry
end

/-! Merged from `NavierStokes.LocalScheduleWitness` (in a section, so its `open`s cannot leak). -/
section
/-!
# Endpoint extensions for every admissible diagonal schedule

All statements retain the supplied schedule. This allows the local paper
construction to select a schedule with extra quantitative residual bounds
without losing the endpoint extension and global candidate conclusions.
-/

noncomputable section

namespace NavierStokes.LocalScheduleWitness

open Set Filter ProblemStatement ActualCandidateAssembly
open CorrectionInitialization.ActualPrimary
open JointResidualLimits (OneSidedExtension AwayExtensions)
open scoped Topology ContDiff

/-- The literal potential sum for the fixed selected stage sequence. -/
def potentialSum (a : ℕ → ℕ) : VelocityField := NavierStokes.LocalAngularGrowth.selectedPotential a
/-- The literal direct angular sum for the fixed selected stage sequence. -/
def directSum (a : ℕ → ℕ) : VelocityField := NavierStokes.LocalAngularGrowth.selectedDirect a
/-- The literal pressure sum for the fixed selected stage sequence. -/
def pressureSum (a : ℕ → ℕ) : PressureField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
    selectedPressureStages

/-- The standard schedule obligations for the selected actual stage fields. -/
abbrev Selected (a : ℕ → ℕ) : Prop :=
  MixedCandidateWitness.SelectedSchedule h
    (ActualCandidateConstruction.qbig ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold)
    selectedPotentialStages selectedDirectStages selectedPressureStages a

/-- Every admissible schedule preserves the three away-from-origin endpoint
extensions; no reselection of the supplied schedule occurs. -/
theorem awayExtensions_of_schedule (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) {a : ℕ → ℕ}
    (ha : MixedCandidateWitness.SelectedSchedule h (ActualCandidateConstruction.qbig B N0)
      (potentialStages B N0 hN) (directStages B N0 hN) (pressureStages B N0 hN) a) :
    AwayExtensions (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
      (PhysicalWaveSum.physicalQ h) (potentialStages B N0 hN)) ∧
    AwayExtensions (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
      (PhysicalWaveSum.physicalQ h) (directStages B N0 hN)) ∧
    AwayExtensions (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
      (PhysicalWaveSum.physicalQ h) (pressureStages B N0 hN)) := by
  obtain ⟨_, hap, _, ham, hat, hgap, _, _⟩ := ha
  have hqbig := ActualCandidateConstruction.qbig_pos B N0
  have ha0 : 0 < (a 0 : ℝ) := by exact_mod_cast hap 0
  have hamin (j : ℕ) : (a 0 : ℝ) ≤ (a j : ℝ) := by
    exact_mod_cast ham.monotone (Nat.zero_le j)
  have hA0 : ∀ x : Space, x ≠ 0 → x 2 = 0 →
      Nonempty (OneSidedExtension (potentialStages B N0 hN 0) x) := by
    intro x hx hxz
    exact MixedDiagonalExtensions.initial_add_extension outgoing.data.h_pos
      outgoing.data.h_lt_half hqbig (initialPotential_support B N0) hx hxz
      (Classical.choice (TailGaugePotential.finalPotential_awayExtensions
        certificate modulation upper B x hx))
  have hP0 : ∀ x : Space, x ≠ 0 → x 2 = 0 →
      Nonempty (OneSidedExtension (pressureStages B N0 hN 0) x) := by
    intro x hx hxz
    exact MixedDiagonalExtensions.initial_add_extension outgoing.data.h_pos
      outgoing.data.h_lt_half hqbig (initialPressure_support B N0) hx hxz
      (Classical.choice ((SlowBaseEndpoint.final_fields_awayExtensions
        certificate modulation upper B).2 x hx))
  have hB0 : ∀ x : Space, x ≠ 0 → x 2 = 0 →
      Nonempty (OneSidedExtension (directStages B N0 hN 0) x) := by
    intro x hx hxz
    exact MixedDiagonalExtensions.extension_of_eventually_zero
      ((directStages_support B N0 hN 0).eventually_zero outgoing.data.h_pos
        outgoing.data.h_lt_half hqbig hx hxz)
  have hAsupport (j : ℕ) (hj : j ≠ 0) :
      MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
        (ActualCandidateConstruction.qbig B N0) (potentialStages B N0 hN j) := by
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => exact positivePotential_support B N0 hN j
  have hPsupport (j : ℕ) (hj : j ≠ 0) :
      MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
        (ActualCandidateConstruction.qbig B N0) (pressureStages B N0 hN j) := by
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => exact positivePressure_support B N0 hN j
  exact ⟨MixedDiagonalExtensions.diagonal_awayExtensions_local outgoing.data.h_pos
      outgoing.data.h_lt_half hqbig hat ha0 hamin (hgap 0) hAsupport hA0
      (endpoints B N0 hN).potential,
    MixedDiagonalExtensions.diagonal_awayExtensions_local outgoing.data.h_pos
      outgoing.data.h_lt_half hqbig hat ha0 hamin (hgap 0)
      (fun j _ => directStages_support B N0 hN j) hB0 (endpoints B N0 hN).direct,
    MixedDiagonalExtensions.diagonal_awayExtensions_local outgoing.data.h_pos
      outgoing.data.h_lt_half hqbig hat ha0 hamin (hgap 0) hPsupport hP0
      (endpoints B N0 hN).pressure⟩

/-- The three endpoint extensions for any schedule of the selected stages. -/
theorem selected_awayExtensions {a : ℕ → ℕ} (ha : Selected a) :
    AwayExtensions (potentialSum a) ∧ AwayExtensions (directSum a) ∧
      AwayExtensions (pressureSum a) :=
  awayExtensions_of_schedule ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry ha

/-- The original axial blowup mechanism holds for the same supplied schedule. -/
theorem selected_origin_blowup {a : ℕ → ℕ} (ha : Selected a) :
    Tendsto (fun t : ℝ => ‖MixedPeriodicAssembly.velocity
      (potentialSum a) (directSum a) (t, 0)‖) (𝓝[<] (1 : ℝ)) atTop := by
  obtain ⟨_, _, _, _, hat, _, _, _⟩ := ha
  exact GermCandidateAssembly.origin_blowup certificate modulation upper
    ActualCandidateConstruction.selectedBudget
    (ActualCandidateConstruction.qbig_pos ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold)
    (initialPotential ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold)
    (positivePotential ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry)
    (directData ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry)
    (initialPotential_axisZeroOn ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold)
    (positivePotential_axisZeroOn ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry) hat

/-- The prescribed schedule supports the complete smooth forcing assembly,
with its actual three sums retained in the output. -/
theorem selected_periodic_candidate {a : ℕ → ℕ} (ha : Selected a) :
    ∃ forcing : VelocityField,
      CandidateProperties
        (TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity
          (potentialSum a) (directSum a)))
        (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure (pressureSum a)))
        forcing ∧ ContDiff ℝ ∞ forcing := by
  have he := selected_awayExtensions ha
  have haxis := selected_origin_blowup ha
  obtain ⟨_, hap, _, ham, hat, hgap, hs, hz⟩ := ha
  have ha0 : 0 < (a 0 : ℝ) := by exact_mod_cast hap 0
  have hamin (j : ℕ) : (a 0 : ℝ) ≤ (a j : ℝ) := by
    exact_mod_cast ham.monotone (Nat.zero_le j)
  have hcut := LocalAngularDiagonal.spatialCut_angularSum_divergence
    outgoing.data.h_pos outgoing.data.h_lt_half
    (directData ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry)
    hat ha0 hamin (hgap 0)
  obtain ⟨forcing, hc, hf, _⟩ := MixedPeriodicAssembly.exists_candidate_force
    (hs.potential.mono (fun _ hx => hx.1)) (hs.direct.mono (fun _ hx => hx.1))
    (hs.pressure.mono (fun _ hx => hx.1)) hcut hz he.1 he.2.1 he.2.2 haxis
  exact ⟨forcing, hc, hf⟩

/-- A full whole-space candidate, including a single kinetic-energy bound,
can be assembled from any selected schedule of these same actual sums. -/
theorem selected_compact_candidate {a : ℕ → ℕ} (ha : Selected a) :
    ∃ forcing : VelocityField,
      NavierStokesR3.ProblemStatement.CandidateProperties 1
        (R3CompactCandidate.velocity (potentialSum a) (directSum a))
        (R3CompactCandidate.pressure (pressureSum a)) forcing
        SpatialLocalization.supportCylinder := by
  obtain ⟨forcing, hc, hf⟩ := selected_periodic_candidate ha
  exact ⟨_, NavierStokesR3.ActualCandidate.of_localized_fields hc hf⟩

end NavierStokes.LocalScheduleWitness
end

/-! Merged from `NavierStokes.LocalResidualFlatness` (in a section, so its `open`s cannot leak). -/
section
/-!
# All quantitative residual orders for one actual diagonal schedule

The schedule is chosen once from the genuine finite-stage estimates, retaining
the three cut bounds. Those same bounds imply every derivative and every
nonnegative power of the physical scale for the raw mixed residual. The
existential choice is outside both derivative-order and decay-order quantifiers.
-/

noncomputable section

namespace NavierStokes.LocalResidualFlatness

open Set Filter ProblemStatement DiagonalResidual MixedCandidateAssembly
open scoped Topology ContDiff

/-- All orders of quantitative flatness of the actual unlocalized mixed
Navier--Stokes residual at the singular spacetime point. -/
def AllResidualJetRates (h : ℝ) (A B : ℕ → VelocityField) (P : ℕ → PressureField)
    (a : ℕ → ℕ) : Prop :=
  ∀ m : ℕ, ∀ r : ℝ, 0 ≤ r →
    JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)))
      (PhysicalWaveSum.physicalQ h)
      (MixedDiagonalResidual.residual (fun j => (a j : ℝ))
        (PhysicalWaveSum.physicalQ h) A B P) m r

theorem allResidualJetRates_of_cutBounds {h qbig : ℝ}
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (E : StageEstimates h qbig A B P) (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : 0 < qbig) {a : ℕ → ℕ} (ha : Tendsto (fun j => (a j : ℝ)) atTop atTop)
    (hb : MixedDiagonalSchedule.ThreeCutBounds a h A B P (fun j => E.gain j / 2)
      (MixedDiagonalSchedule.commonLoss E.potentialLoss E.directLoss E.pressureLoss)
      PhysicalWaveSum.preterminal) : AllResidualJetRates h A B P a := by
  let U := PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig
  have hU : IsOpen U := PhysicalWaveSum.preterminal_open.inter
    (CutStageEstimates.physicalSublevel_open hh hh1 qbig)
  have hUp : U ⊆ PhysicalWaveSum.preterminal := inter_subset_left
  have hqzero := AnnularEndpoint.physicalQ_tendsto_zero hh hh1 (x := (0 : Space)) rfl
  have hlU : ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)), z ∈ U := by
    filter_upwards [self_mem_nhdsWithin, hqzero.eventually (gt_mem_nhds hqbig)] with z hz hqz
    exact ⟨hz.1, hz.1, hqz⟩
  have hlq : ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)),
      0 < PhysicalWaveSum.physicalQ h z ∧ PhysicalWaveSum.physicalQ h z ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      hqzero.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with z hz hqz
    exact ⟨PhysicalWaveSum.physicalQ_pos hh hh1 hz.1, hqz.le⟩
  have hhalfmono : Monotone (fun j => E.gain j / 2) := by
    intro i j hij
    exact div_le_div_of_nonneg_right (E.gain_mono hij) (by norm_num)
  have hhalftop : Tendsto (fun j => E.gain j / 2) atTop atTop := by
    apply tendsto_atTop.2
    intro r
    filter_upwards [E.gain_top.eventually (eventually_ge_atTop (2 * r))] with j hj
    linarith
  have hqpos : ∀ z ∈ U, 0 < PhysicalWaveSum.physicalQ h z :=
    fun z hz => PhysicalWaveSum.physicalQ_pos hh hh1 (hUp hz)
  have hq : ContDiffOn ℝ ∞ (PhysicalWaveSum.physicalQ h) U :=
    fun z hz => (PhysicalWaveSum.physicalQ_smoothAt hh hh1 (hUp hz)).contDiffWithinAt
  have hres (J m : ℕ) :
      JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space))) (PhysicalWaveSum.physicalQ h)
        (fun z => navierStokesResidual (MixedDiagonalResidual.uncutVelocity A B J)
          (DiagonalJetBounds.uncutPrefix P (J + 1)) z.1 z.2)
        m (E.gain J / 2 - E.residualLoss m) := by
    have hn : 0 ≤ E.gain J := E.gain_zero.trans (E.gain_mono (Nat.zero_le J))
    exact (E.finite_residual J m).weaken hlq (by linarith)
  intro m r hr
  exact MixedDiagonalResidual.residual_jetRate ha hU hqpos hq
    (fun j => (E.potential_smooth j).mono inter_subset_right)
    (fun j => (E.direct_smooth j).mono inter_subset_right)
    (fun j => (E.pressure_smooth j).mono inter_subset_right) hhalfmono hhalftop
    (fun j hj m hm z hz => hb.potential j hj m hm z hz.1)
    (fun j hj m hm z hz => hb.direct j hj m hm z hz.1)
    (fun j hj m hm z hz => hb.pressure j hj m hm z hz.1)
    hlU hqzero E.finite_background hres m r hr

/-- One schedule simultaneously has smooth sums, all three cut bounds,
vanishing endpoint jets, and every quantitative residual rate. -/
theorem exists_schedule_all_jetRates {h qbig : ℝ}
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (E : StageEstimates h qbig A B P) (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : 0 < qbig) :
    ∃ a : ℕ → ℕ,
      MixedCandidateWitness.SelectedSchedule h qbig A B P a ∧
      MixedDiagonalSchedule.ThreeCutBounds a h A B P (fun j => E.gain j / 2)
        (MixedDiagonalSchedule.commonLoss E.potentialLoss E.directLoss E.pressureLoss)
        PhysicalWaveSum.preterminal ∧
      AllResidualJetRates h A B P a := by
  have hS : ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)),
      z ∈ PhysicalWaveSum.preterminal := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hz.1
  obtain ⟨a, hal, hap, had, ham, hat, hrecip, hb, hs, hz⟩ :=
    MixedDiagonalResidual.exists_physical_schedule_residual_zero hh hh1 hqbig
      PhysicalWaveSum.preterminal_open (Subset.refl _) hS
      E.potential_smooth E.direct_smooth E.pressure_smooth
      E.gain E.potentialLoss E.directLoss E.pressureLoss E.backgroundLoss E.residualLoss
      E.potentialConstant E.directConstant E.pressureConstant E.potentialLog E.directLog E.pressureLog
      E.potential_bound E.direct_bound E.pressure_bound
      E.gain_zero E.gain_pos E.gain_mono E.gain_top E.finite_background E.finite_residual 1
  exact ⟨a, ⟨hal, hap, had, ham, hat, hrecip, hs, hz⟩, hb,
    allResidualJetRates_of_cutBounds E hh hh1 hqbig hat hb⟩

/-- The actual finite-stage estimates with the repository's fixed budget and
geometric threshold, before any schedule information is discarded. -/
def selectedEstimates :=
  ActualCandidateAssembly.estimates ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry

/-- Closed all-order flatness for one common actual schedule. No raw-stage,
finite-stage, smoothness, or rate assumption remains. -/
theorem selected_schedule :
    ∃ a : ℕ → ℕ,
      MixedCandidateWitness.SelectedSchedule CorrectionInitialization.ActualPrimary.h
        ActualCandidateConstruction.selectedQbig ActualCandidateAssembly.selectedPotentialStages
        ActualCandidateAssembly.selectedDirectStages ActualCandidateAssembly.selectedPressureStages a ∧
      MixedDiagonalSchedule.ThreeCutBounds a CorrectionInitialization.ActualPrimary.h
        ActualCandidateAssembly.selectedPotentialStages ActualCandidateAssembly.selectedDirectStages
        ActualCandidateAssembly.selectedPressureStages (fun j => selectedEstimates.gain j / 2)
        (MixedDiagonalSchedule.commonLoss selectedEstimates.potentialLoss selectedEstimates.directLoss
          selectedEstimates.pressureLoss) PhysicalWaveSum.preterminal ∧
      AllResidualJetRates CorrectionInitialization.ActualPrimary.h
        ActualCandidateAssembly.selectedPotentialStages ActualCandidateAssembly.selectedDirectStages
        ActualCandidateAssembly.selectedPressureStages a :=
  exists_schedule_all_jetRates selectedEstimates
    CorrectionInitialization.ActualPrimary.outgoing.data.h_pos
    CorrectionInitialization.ActualPrimary.outgoing.data.h_lt_half
    (ActualCandidateConstruction.qbig_pos _ _)

end NavierStokes.LocalResidualFlatness
end

/-! Merged from `NavierStokes.LocalJetBounds` (in a section, so its `open`s cannot leak). -/
section
/-!
# Uniform local jet bounds up to the terminal slice

Actual smooth extensions at each nonsingular terminal point provide compatible
limits of every derivative. Compactness turns those local bounds into one bound
on any compact spacetime set avoiding the singular point.
-/

noncomputable section

open Set Filter Bornology
open scoped Topology ContDiff

namespace NavierStokes.LocalJetBounds

open ProblemStatement
open JointResidualLimits (AwayExtensions)

/-- A limit at each point of a compact set bounds the function on the
approaching part of that set. The boundary values need not have been assigned
to the original function. -/
theorem isBounded_image_of_compact_limits {X V : Type*} [TopologicalSpace X]
    [PseudoMetricSpace V] {K S : Set X} {f : X → V} (hK : IsCompact K)
    (hf : ∀ x ∈ K, ∃ y : V, Tendsto f (𝓝[S] x) (𝓝 y)) :
    IsBounded (f '' (K ∩ S)) := by
  have hd : Disjoint (𝓝ˢ K ⊓ 𝓟 S) (comap f (cobounded V)) := by
    rw [disjoint_assoc, inf_comm, hK.disjoint_nhdsSet_left]
    intro x hx
    obtain ⟨y, hy⟩ := hf x hx
    exact disjoint_left_comm.2 <|
      tendsto_comap.disjoint (Metric.disjoint_cobounded_nhds y) hy
  obtain ⟨U, ⟨hUo, hKU⟩, t, ht, hUt⟩ :=
    ((((hasBasis_nhdsSet K).inf_principal S)).disjoint_iff
      ((basis_sets _).comap f)).1 hd
  have hb : IsBounded (f '' (U ∩ S)) := by
    apply (isBounded_compl_iff.2 ht).subset
    rwa [image_subset_iff, preimage_compl, subset_compl_iff_disjoint_right]
  exact hb.subset (image_mono (inter_subset_inter_left S hKU))

/-- Smoothness in the past and actual one-sided extensions give every
derivative a finite limit at each nonsingular point of the closed past. -/
theorem jet_has_limit {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : SpaceTime → V} (hf : ContDiffOn ℝ ∞ f (SpacetimeEndpoint.openPast 1))
    (he : AwayExtensions f) {w : SpaceTime} (ht : w.1 ≤ 1)
    (hw : w ≠ (1, (0 : Space))) (n : ℕ) :
    ∃ L, Tendsto (iteratedFDeriv ℝ n f) (𝓝[SpacetimeEndpoint.openPast 1] w) (𝓝 L) := by
  by_cases hp : w.1 < 1
  · have hc := hf.contDiffAt ((SpacetimeEndpoint.openPast_isOpen 1).mem_nhds
      (show w ∈ SpacetimeEndpoint.openPast 1 from ⟨hp, mem_univ _⟩))
    have hj : ContDiffAt ℝ 0 (iteratedFDeriv ℝ n f) w :=
      hc.iteratedFDeriv_right (by exact_mod_cast (le_top : 0 + (n : ℕ∞) ≤ ⊤))
    exact ⟨_, hj.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩
  · have ht1 : w.1 = 1 := le_antisymm ht (le_of_not_gt hp)
    have hx : w.2 ≠ 0 := by
      intro hx
      exact hw (Prod.ext ht1 hx)
    obtain ⟨e⟩ := he w.2 hx
    have hw1 : w = (1, w.2) := Prod.ext ht1 rfl
    rw [hw1]
    exact ⟨_, e.jet_tendsto n⟩

/-- Uniform bounds for every Cartesian derivative on compact subsets of the
closed past that avoid the singular point, including approach from `t < 1`. -/
theorem uniform_jets_on_compact {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : SpaceTime → V} (hf : ContDiffOn ℝ ∞ f (SpacetimeEndpoint.openPast 1))
    (he : AwayExtensions f) {K : Set SpaceTime} (hK : IsCompact K)
    (hKt : ∀ w ∈ K, w.1 ≤ 1) (hK0 : (1, (0 : Space)) ∉ K) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, w.1 < 1 → ‖iteratedFDeriv ℝ n f w‖ ≤ C := by
  have hb := isBounded_image_of_compact_limits hK (fun w hw =>
    jet_has_limit hf he (hKt w hw) (fun heq => hK0 (heq ▸ hw)) n)
  obtain ⟨C, hC, hbound⟩ := hb.exists_pos_norm_le
  exact ⟨C, hC, fun w hw ht => hbound _ ⟨w, ⟨hw, ht, mem_univ _⟩, rfl⟩⟩

/-- The exact compact-spatial, positive-scale-strip bounds of the local
theorem. The bound remains valid as the terminal slice is approached. -/
theorem uniform_jets_on_scale_strip {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : SpaceTime → V} (hf : ContDiffOn ℝ ∞ f (SpacetimeEndpoint.openPast 1))
    (he : AwayExtensions f) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {K : Set Space} (hK : IsCompact K) {c c' : ℝ} (hc : 0 < c) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : SpaceTime, w.1 < 1 → w.2 ∈ K →
      c ≤ PhysicalWaveSum.physicalQ h w → PhysicalWaveSum.physicalQ h w ≤ c' →
      ‖iteratedFDeriv ℝ n f w‖ ≤ C := by
  let S : Set SpaceTime := {w | w.1 < 1 ∧ w.2 ∈ K ∧
    c ≤ PhysicalWaveSum.physicalQ h w ∧ PhysicalWaveSum.physicalQ h w ≤ c'}
  have hsub : S ⊆ Icc (1 - c') 1 ×ˢ K := by
    intro w hw
    have ht := LocalScaleGeometry.time_dist_le hh hh1 hw.1
    rw [abs_of_neg (sub_neg.mpr hw.1)] at ht
    exact ⟨⟨by linarith [hw.2.2.2], hw.1.le⟩, hw.2.1⟩
  have hclosedSub : closure S ⊆ Icc (1 - c') 1 ×ˢ K :=
    closure_minimal hsub (isClosed_Icc.prod hK.isClosed)
  have hcompact : IsCompact (closure S) :=
    (isCompact_Icc.prod hK).of_isClosed_subset isClosed_closure hclosedSub
  have hzero : (1, (0 : Space)) ∉ closure S := by
    have hq := (AnnularEndpoint.physicalQ_tendsto_zero hh hh1
      (x := (0 : Space)) rfl).eventually (gt_mem_nhds hc)
    obtain ⟨U, hU, hUp⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hq
    intro hcl
    obtain ⟨w, hw, hs⟩ := mem_closure_iff_nhds.mp hcl U hU
    have hlt := hUp ⟨hw, hs.1, mem_univ _⟩
    exact (not_lt_of_ge hs.2.2.1) hlt
  obtain ⟨C, hC, hb⟩ := uniform_jets_on_compact hf he hcompact
    (fun w hw => (hclosedSub hw).1.2) hzero n
  exact ⟨C, hC, fun w ht hx hlow hhigh =>
    hb w (subset_closure ⟨ht, hx, hlow, hhigh⟩) ht⟩

end NavierStokes.LocalJetBounds
end

/-! Merged from `NavierStokes.LocalScaleApproach`. -/
/-!
# Uniform small-scale bounds at bounded similarity radius

The physical similarity scale controls distance to the singular point whenever
`X = radialEnergy / q` remains bounded. Consequently a jet estimate in the
ordinary punctured spacetime neighborhood gives a bound uniform over every
fixed finite range of `X`, for all sufficiently small positive scales.
-/

noncomputable section

namespace NavierStokes.LocalScaleApproach

open Set Filter ProblemStatement
open scoped Topology

/-- An explicit majorant for spacetime distance in the similarity region. -/
def approachMajorant (h X q : ℝ) : ℝ :=
  q + Real.sqrt (2 * X * q + q ^ (1 - 2 * h))

theorem approachMajorant_continuous {h : ℝ} (hh1 : h < 1 / 2) (X : ℝ) :
    Continuous (approachMajorant h X) := by
  have hexp : 0 ≤ 1 - 2 * h := by linarith
  exact continuous_id.add
    (((continuous_const.mul continuous_id).add (Real.continuous_rpow_const hexp)).sqrt)

@[simp] theorem approachMajorant_zero {h : ℝ} (hh1 : h < 1 / 2) (X : ℝ) :
    approachMajorant h X 0 = 0 := by
  have hexp : 1 - 2 * h ≠ 0 := by linarith
  simp [approachMajorant, Real.zero_rpow hexp]

/-- Bounded similarity radius and a small scale force a point into any given
ordinary neighborhood of `(1,0)`. -/
theorem small_scale_mem_nhds {h X : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hX : 0 ≤ X) {U : Set SpaceTime} (hU : U ∈ 𝓝 ((1 : ℝ), (0 : Space))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : SpaceTime, w.1 < 1 →
      PhysicalWaveSum.physicalQ h w < δ →
      AxisymmetricFields.radialEnergy w.2 / PhysicalWaveSum.physicalQ h w ≤ X →
      w ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hmajor : ∀ᶠ q : ℝ in 𝓝 0, approachMajorant h X q < ε := by
    have hm := (approachMajorant_continuous hh1 X).tendsto 0
    rw [approachMajorant_zero hh1 X] at hm
    exact hm.eventually (gt_mem_nhds hε)
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhds_iff.mp hmajor
  refine ⟨δ, hδ, ?_⟩
  intro w ht hq hXw
  have hqpos := PhysicalWaveSum.physicalQ_pos hh hh1 ht
  have hnear : approachMajorant h X (PhysicalWaveSum.physicalQ h w) < ε :=
    hsmall (by simpa only [Metric.mem_ball, dist_zero_right,
      Real.norm_of_nonneg hqpos.le] using hq)
  have hspace := LocalScaleGeometry.spatial_norm_sq_le hh hh1 ht hXw
  have htime := LocalScaleGeometry.time_dist_le hh hh1 ht
  have hnorm : ‖w.2‖ ≤
      Real.sqrt (2 * X * PhysicalWaveSum.physicalQ h w +
        PhysicalWaveSum.physicalQ h w ^ (1 - 2 * h)) := by
    apply (Real.le_sqrt (norm_nonneg _) _).mpr hspace
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hX) hqpos.le)
      (Real.rpow_nonneg hqpos.le _)
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq]
  have hqle : PhysicalWaveSum.physicalQ h w ≤
      approachMajorant h X (PhysicalWaveSum.physicalQ h w) :=
    le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hsle : Real.sqrt (2 * X * PhysicalWaveSum.physicalQ h w +
      PhysicalWaveSum.physicalQ h w ^ (1 - 2 * h)) ≤
      approachMajorant h X (PhysicalWaveSum.physicalQ h w) :=
    le_add_of_nonneg_left hqpos.le
  apply max_lt
  · simpa only [Real.dist_eq] using htime.trans_lt (hqle.trans_lt hnear)
  · simpa only [dist_zero_right] using hnorm.trans_lt (hsle.trans_lt hnear)

/-- Any eventual property at the singular point holds uniformly for bounded
similarity radius once the physical scale is sufficiently small. -/
theorem uniform_small_scale_of_eventually {h X : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hX : 0 ≤ X) {P : SpaceTime → Prop}
    (hP : ∀ᶠ w in 𝓝[SpacetimeEndpoint.openPast 1] ((1 : ℝ), (0 : Space)), P w) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : SpaceTime, w.1 < 1 →
      PhysicalWaveSum.physicalQ h w < δ →
      AxisymmetricFields.radialEnergy w.2 / PhysicalWaveSum.physicalQ h w ≤ X →
      P w := by
  obtain ⟨U, hU, hx, hUP⟩ := mem_nhdsWithin.mp hP
  obtain ⟨δ, hδ, hd⟩ := small_scale_mem_nhds hh hh1 hX (hU.mem_nhds hx)
  exact ⟨δ, hδ, fun w ht hq hXw => hUP ⟨hd w ht hq hXw, ht, mem_univ _⟩⟩

/-- A joint spacetime jet rate gives the exact uniform small-`q` estimate on
every finite similarity-radius range stated in the paper's local theorem. -/
theorem jetRate_uniform_small_scale {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : SpaceTime → V} {m : ℕ} {r : ℝ}
    (hrate : DiagonalResidual.JetRate
      (𝓝[SpacetimeEndpoint.openPast 1] ((1 : ℝ), (0 : Space)))
      (PhysicalWaveSum.physicalQ h) f m r) :
    ∀ X : ℝ, 0 ≤ X → ∃ C : ℝ, 0 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ w : SpaceTime, w.1 < 1 → PhysicalWaveSum.physicalQ h w < δ →
        AxisymmetricFields.radialEnergy w.2 / PhysicalWaveSum.physicalQ h w ≤ X →
        ‖iteratedFDeriv ℝ m f w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ r := by
  intro X hX
  obtain ⟨C, hC, hb⟩ := hrate
  obtain ⟨δ, hδ, hd⟩ := uniform_small_scale_of_eventually hh hh1 hX hb
  exact ⟨C, hC, δ, hδ, hd⟩

end NavierStokes.LocalScaleApproach


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

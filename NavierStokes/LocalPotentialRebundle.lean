import NavierStokes.LocalAngularGrowth
import NavierStokes.TailGaugePotential

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

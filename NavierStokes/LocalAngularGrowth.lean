import NavierStokes.R3.ActualCandidate
import NavierStokes.ActualExteriorPrefix
import NavierStokes.BaseAngularGrowth

/-!
# Angular growth of the selected solution in the inner core

All correction stages vanish on the inner complement of the active annulus.
Consequently the actual diagonal solution retains the slow base's quantitative
angular asymptotic along an inward-moving radial ray.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.LocalAngularGrowth

open ProblemStatement CorrectionInitialization

def rawVelocity (A D : ℕ → VelocityField) (a : ℕ → ℝ) : VelocityField :=
  MixedPeriodicAssembly.velocity
    (SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ ActualPrimary.h) A)
    (SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ ActualPrimary.h) D)

/-- On either component of the complement of the correction annulus, the
whole diagonal velocity agrees with the same actual slow base once the
zeroth cutoff is on its plateau. -/
theorem rawVelocity_eq_base {B Nr : ℕ} {A D : ℕ → VelocityField}
    {P : ℕ → PressureField} (H : ActualExteriorPrefix.ExteriorStages B Nr A D P)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {w : SpaceTime}
    (hw : w ∈ ActualExteriorPrefix.exteriorDomain Nr)
    (hsmall : |a 0 * PhysicalWaveSum.physicalQ ActualPrimary.h w| < 1 / 2) :
    rawVelocity A D a w =
      FinalSlowBase.velocity ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B w := by
  have ht := hw.1.1
  have hq := (PhysicalWaveSum.physicalQ_smoothAt
    ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half ht).continuousAt
  have hpos := PhysicalWaveSum.physicalQ_pos
    ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half ht
  have hzero : ∀ j : ℕ, j ≠ 0 → A j =ᶠ[𝓝 w] fun _ => 0 := by
    intro j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    exact ActualExteriorPrefix.eqOn_exterior_germ (H.potential_succ k) hw
  have hcurl := AxisPreservation.velocitySum_eq_first ha hq hpos hzero hsmall
  have hbase := SolenoidalDiagonal.spatialCurl_eq_of_eventuallyEq
    (ActualExteriorPrefix.eqOn_exterior_germ H.potential_zero hw)
  have hD : SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ ActualPrimary.h) D w = 0 := by
    have hz (j : ℕ) : D j w = 0 := H.direct_zero j hw
    simp only [SolenoidalDiagonal.potentialSum, SolenoidalDiagonal.cutStage, hz,
      smul_zero, tsum_zero]
  change SolenoidalDiagonal.velocitySum a (PhysicalWaveSum.physicalQ ActualPrimary.h) A w +
    SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ ActualPrimary.h) D w = _
  rw [hD, add_zero, hcurl, hbase]
  exact TailGaugePotential.finalPotential_sameCurl ActualPrimary.certificate
    ActualPrimary.modulation ActualPrimary.upper B ht


def innerRadius : ℝ := NominalConeAssembly.activeLeft ActualPrimary.nominal / 2

theorem innerRadius_pos : 0 < innerRadius :=
  half_pos (NominalConeAssembly.activeLeft_pos ActualPrimary.nominal)

theorem innerRadius_lt_left : innerRadius < NominalConeAssembly.activeLeft ActualPrimary.nominal :=
  half_lt_self (NominalConeAssembly.activeLeft_pos ActualPrimary.nominal)

/-- One positive time interval satisfies every cutoff and correction-support
condition needed along the fixed inner ray. -/
theorem exists_ray_interval (a : ℕ → ℝ) (Nr : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ τ : ℝ, 0 < τ → τ < δ →
      (1 - τ, BaseAngularGrowth.ray innerRadius τ) ∈ ActualExteriorPrefix.exteriorDomain Nr ∧
      |a 0 * PhysicalWaveSum.physicalQ ActualPrimary.h
        (1 - τ, BaseAngularGrowth.ray innerRadius τ)| < 1 / 2 ∧
      3 / 4 ≤ 1 - τ ∧ BaseAngularGrowth.ray innerRadius τ ∈ SpatialLocalization.plateau := by
  let δ : ℝ := min (1 / 8) (min (ChartScales.Q Nr)
    (min ((1 / 2) / (|a 0| + 1)) ((1 / 32) / (2 * innerRadius + 1))))
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min (by norm_num) (lt_min (ChartScales.Q_pos Nr)
      (lt_min (div_pos (by norm_num) (by positivity))
        (div_pos (by norm_num) (by linarith [innerRadius_pos]))))
  have hδt : δ ≤ 1 / 8 := min_le_left _ _
  have hδq : δ ≤ ChartScales.Q Nr := (min_le_right _ _).trans (min_le_left _ _)
  have hδa : δ ≤ (1 / 2) / (|a 0| + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδx : δ ≤ (1 / 32) / (2 * innerRadius + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ, hδ, hδt.trans (by norm_num), ?_⟩
  intro τ hτ hτδ
  have hq : PhysicalWaveSum.physicalQ ActualPrimary.h
      (1 - τ, BaseAngularGrowth.ray innerRadius τ) = τ :=
    BaseAngularGrowth.physicalQ_ray ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half hτ
  have hchart := BaseAngularGrowth.cartesianChart_ray ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half innerRadius_pos.le hτ
  have ht : τ < 1 / 8 := hτδ.trans_le hδt
  have haτ : τ * (|a 0| + 1) < 1 / 2 :=
    (lt_div_iff₀ (by positivity)).mp (hτδ.trans_le hδa)
  have hxτ : τ * (2 * innerRadius + 1) < 1 / 32 :=
    (lt_div_iff₀ (by linarith [innerRadius_pos])).mp (hτδ.trans_le hδx)
  refine ⟨?_, ?_, by linarith, ?_⟩
  · apply ActualExteriorPrefix.mem_exteriorDomain.mpr
    refine ⟨by change 1 - τ < 1; linarith, ?_, ?_⟩
    · rw [hq]
      exact hτδ.trans_le hδq
    · intro hactive
      change (SlowBorelBase.cartesianChart ActualPrimary.h
        (1 - τ, BaseAngularGrowth.ray innerRadius τ)).2.1 ∈
          Icc (NominalConeAssembly.activeLeft ActualPrimary.nominal)
            (NominalConeAssembly.activeRight ActualPrimary.nominal) at hactive
      rw [hchart] at hactive
      exact (not_le_of_gt innerRadius_lt_left) hactive.1
  · rw [hq, abs_mul, abs_of_pos hτ]
    nlinarith
  · change SpatialLocalization.radialSquare (BaseAngularGrowth.ray innerRadius τ) < 1 / 32 ∧
      |BaseAngularGrowth.ray innerRadius τ 2| < 1 / 8
    constructor
    · simp only [SpatialLocalization.radialSquare, BaseAngularGrowth.ray_apply_zero,
        BaseAngularGrowth.ray_apply_one, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, add_zero]
      rw [Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num) innerRadius_pos.le) hτ.le)]
      nlinarith
    · simp only [BaseAngularGrowth.ray_apply_two, abs_zero]
      norm_num

def selectedPotential (a : ℕ → ℕ) : VelocityField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
    (PhysicalWaveSum.physicalQ ActualPrimary.h) ActualCandidateAssembly.selectedPotentialStages

def selectedDirect (a : ℕ → ℕ) : VelocityField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
    (PhysicalWaveSum.physicalQ ActualPrimary.h) ActualCandidateAssembly.selectedDirectStages

def selectedVelocity (a : ℕ → ℕ) : VelocityField :=
  R3CompactCandidate.velocity (selectedPotential a) (selectedDirect a)


theorem innerRadius_le_boxRadius : innerRadius ≤
    FinalSlowBase.boxRadius ActualPrimary.nominal ActualPrimary.upper := by
  have hord : NominalConeAssembly.activeLeft ActualPrimary.nominal <
      NominalConeAssembly.activeRight ActualPrimary.nominal :=
    (Real.log_lt_log_iff (NominalConeAssembly.activeLeft_pos ActualPrimary.nominal)
      (FinalSlowBase.terminal_pos ActualPrimary.nominal)).mp
      (LeadingStressWeights.edges_ordered ActualPrimary.nominal)
  exact innerRadius_lt_left.le.trans (hord.le.trans (le_max_right _ _))

/-- The error form of `uθ = τ⁻ᴬ (e₀ + O(τ^(2h)))` at one fixed radius
in the inner core. The exponent, radius and coefficient are
the ones belonging to the actual selected profile. -/
def AngularGrowth (u : VelocityField) : Prop :=
  ∃ e₀ C δ : ℝ, 0 < e₀ ∧ 0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧
    ∀ τ : ℝ, 0 < τ → τ < δ →
      |τ ^ CoordinateAlgebra.A ActualPrimary.h *
        u (1 - τ, BaseAngularGrowth.ray innerRadius τ) 1 - e₀| ≤
          C * τ ^ (2 * ActualPrimary.h)

/-- The selected local velocity before the spatial and initial-time cutoffs. -/
def selectedRawVelocity (a : ℕ → ℕ) : VelocityField :=
  MixedPeriodicAssembly.velocity (selectedPotential a) (selectedDirect a)

/-- The quantitative angular estimate already holds for the local fields. -/
theorem selectedRawVelocity_angularGrowth {a : ℕ → ℕ}
    (ha : Tendsto (fun j => (a j : ℝ)) atTop atTop) :
    AngularGrowth (selectedRawVelocity a) := by
  obtain ⟨δ, hδ, hδ1, hconditions⟩ := exists_ray_interval (fun j => (a j : ℝ))
    (ActualCandidateConstruction.residualBand ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold)
  obtain ⟨C, hC, hb⟩ := BaseAngularGrowth.normalized_velocity_ray_bound
    ActualPrimary.certificate ActualPrimary.modulation ActualPrimary.upper
    ActualCandidateConstruction.selectedBudget innerRadius_pos innerRadius_le_boxRadius
  refine ⟨BaseAngularGrowth.leadingAmplitude ActualPrimary.modulation innerRadius, C, δ,
    BaseAngularGrowth.leadingAmplitude_pos ActualPrimary.modulation innerRadius_pos,
    hC, hδ, hδ1, ?_⟩
  intro τ hτ hτδ
  obtain ⟨hw, hsmall, _, _⟩ := hconditions τ hτ hτδ
  have heq : selectedRawVelocity a (1 - τ, BaseAngularGrowth.ray innerRadius τ) =
      FinalSlowBase.velocity ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper ActualCandidateConstruction.selectedBudget
        (1 - τ, BaseAngularGrowth.ray innerRadius τ) :=
    rawVelocity_eq_base
      (ActualCandidateAssembly.exteriorStages ActualCandidateConstruction.selectedBudget
        ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry)
      ha hw hsmall
  rw [heq]
  exact hb τ hτ (hτδ.le.trans hδ1)


theorem selected_exponent_small : 0 < ActualPrimary.h ∧ ActualPrimary.h < 1 / 100 := by
  refine ⟨ActualPrimary.outgoing.data.h_pos, ?_⟩
  have hsmall := ActualPrimary.nominal.axis.small.h_le
  linarith


end NavierStokes.LocalAngularGrowth

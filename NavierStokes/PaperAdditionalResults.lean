import NavierStokes.SquaredPartition
import Mathlib.Data.Set.Card
import NavierStokes.SlotColoring
import Mathlib.Analysis.Normed.Group.Bounded
import NavierStokes.PhysicalWaveSum
import NavierStokes.TorusCoverDegree
import NavierStokes.MeanLocalDefectBounds
import NavierStokes.AxisSeries
import NavierStokes.AxisInverseFactors
import NavierStokes.NaturalAxisJointAnalytic
import NavierStokes.NaturalExitBounds
import NavierStokes.OutgoingCone
import NavierStokes.ReferenceBounds
import NavierStokes.ReferenceUniformStocks
import NavierStokes.NaturalAxisRange
import NavierStokes.AppendixHeatResults
import NavierStokes.TerminalEdgeFactor
import NavierStokes.ParametricFlatFactor
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import NavierStokes.UniformCone
import NavierStokes.SeedHandbackJets
import NavierStokes.SmoothExponentialMomentMatrix
import NavierStokes.RegularSingularIntegral
import NavierStokes.PositiveAxisDifferential
import NavierStokes.LocalPaperHeat
import NavierStokes.R3.Theorem
import NavierStokes.R3.H3MaximalLifespan
import NavierStokes.GenericSummationRealization
import NavierStokes.GenericSupportLocalSummation
import NavierStokes.ClosedIntervalMomentRepair
import NavierStokes.UniformQuadraticBranch
import NavierStokes.ModulatedProfileJetRates
import NavierStokes.TrueConeLoop
import Mathlib.Topology.MetricSpace.Thickening
import NavierStokes.WholeDomainBaseBounds
import NavierStokes.WholeDomainInitializationBounds
import NavierStokes.SharpPhysicalLogBounds
import NavierStokes.MixedFiniteBackground
import NavierStokes.SharpParticularStageBounds
import NavierStokes.ParticularOneSided


/-! Merged from `NavierStokes.AxisRootPressureBounds`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/

/-! Merged from `NavierStokes.AppendixJoiningResults`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# Additional literal bounds in the axis and joining appendices
-/

noncomputable section

namespace NavierStokes.AppendixJoiningResults

open Set
open scoped ContDiff
open NaturalAxisCoefficients NaturalProfile ProfileHistories ReferenceBounds




/-- The real denominator remains positive on the existing enlarged window
even under the larger `h ≤ .01` range of the current manuscript. -/
theorem axis_L_lower_bound_window {h η : ℝ} (hh0 : 0 ≤ h) (hh : h ≤ 1 / 100)
    (hη : η ∈ window.interval) : (4879 / 5000 : ℝ) ≤ NaturalAxisData.L h η := by
  have he : η ∈ Icc (-11 / 10 : ℝ) (11 / 10) := hη
  have hs : η ^ 2 ≤ 121 / 100 := by nlinarith [he.1, he.2]
  have hm := mul_nonneg hh0 (sub_nonneg.mpr hs)
  unfold NaturalAxisData.L
  nlinarith


end NavierStokes.AppendixJoiningResults


end


/-! Merged from `NavierStokes.FlatPrimitivePaper`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! The flat primitive lemma with coefficients specified only near a compact
parameter rectangle. The factor includes the manuscript's explicit `1/2`. -/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokes.FlatPrimitivePaper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]



end NavierStokes.FlatPrimitivePaper


end


/-! Merged from `NavierStokes.OutgoingNegativeSlopeCone`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # The admissible cone starts during the negative-slope transition

The literal schedule has negative logarithmic slope immediately after
`dropLength + 1`. Its actual radial cone coefficient is then greater than
two. Combining this identity with the already constructed relaxed cone
gives the missing transition interval, with the same profile and radius.
-/

noncomputable section

open Set
open scoped Topology

namespace NavierStokes.OutgoingNegativeSlopeCone

open OutgoingSchedule OutgoingTail OutgoingCone
open UniformAngularReset (ResetWitness)
open OutgoingEntranceCone (coneA)

theorem sigma_pos {x : ℝ} (hx : 0 < x) : 0 < sigma x :=
  div_pos (FlatCutoff.edge_pos 1 hx) (sigma_denom_pos x)

/-- This is the sign of the prescribed smooth schedule itself, not an
assumed inequality for a free slope function. -/
theorem slope_neg_iff (c : Parameters) (y : ℝ) :
    slope c.dropLength c.lam y < 0 ↔ c.dropLength + 1 < y := by
  constructor
  · intro hneg
    by_contra hy
    have hy' : y ≤ c.dropLength + 1 := le_of_not_gt hy
    have hstep : sigma (y - (c.dropLength + 1)) = 0 := sigma_zero (by linarith)
    have hnonneg : 0 ≤ (3 / 5 : ℝ) * (1 - sigma y) :=
      mul_nonneg (by norm_num) (sub_nonneg.mpr (sigma_le_one y))
    simp only [OutgoingSchedule.slope, hstep, mul_zero, sub_zero] at hneg
    exact (not_lt_of_ge hnonneg) hneg
  · intro hy
    have hy1 : 1 ≤ y := by linarith [c.dropLength_pos]
    have hstep : 0 < sigma (y - (c.dropLength + 1)) := sigma_pos (by linarith)
    simp only [OutgoingSchedule.slope, sigma_one hy1, sub_self, mul_zero, zero_sub]
    exact neg_neg_of_pos (mul_pos c.lam_pos hstep)


theorem coneA_gt_two_of_negative_slope {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y : ℝ} (hy : y < d.core.endpoint) (eta : ℝ)
    (hneg : slope d.core.dropLength d.core.lam y < 0) : 2 < coneA w (y, eta) := by
  rw [OutgoingEntranceCone.coneA_before w hy]
  dsimp only [OutgoingEntranceCone.radialA]
  linarith

/-- No shear estimate is added: the existing normalized radial identity
already dominates the radial coefficient for every actual shear value. -/
theorem true_of_relaxed_negative_slope {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (Amp : ℝ → ℝ) {XR y eta : ℝ}
    (hrelaxed : RelaxedAt w Amp XR (y, eta)) (hy : y < d.core.endpoint)
    (hneg : slope d.core.dropLength d.core.lam y < 0) :
    TrueAt w Amp XR (y, eta) :=
  ⟨hrelaxed, normalV_gt_two_of_radial w Amp (y, eta)
    (coneA_gt_two_of_negative_slope w hy eta hneg)⟩

def trueWindowFromTransition (d : TailData) : Set (ℝ × ℝ) :=
  Ioc (d.core.dropLength + 1) (cleanEnd d) ×ˢ Icc (-1) 1

/-- Every constructed clean cone already satisfies the full paper clause:
the admissible cone begins as soon as the incoming transition slope is
negative, one unit before the constant-slope interval begins. -/
theorem true_from_transition {d : TailData} {K XR left : ℝ}
    {w : ResetWitness d K} (h : CleanOutgoingCone w XR left) (hleft : left ≤ 0) :
    ∀ p ∈ trueWindowFromTransition d,
      TrueAt w (CorrectedPulseAmplitude.amplitude d w.coefficients) XR p := by
  rintro ⟨y, eta⟩ hp
  by_cases hy : d.core.holdStart ≤ y
  · exact h.true_from_hold (y, eta) ⟨⟨hy, hp.1.2⟩, hp.2⟩
  · have hneg : slope d.core.dropLength d.core.lam y < 0 :=
      (slope_neg_iff d.core y).mpr hp.1.1
    have hy0 : 0 < y := by linarith [d.core.dropLength_pos, hp.1.1]
    have hyend : y < d.core.endpoint := by
      have hh := d.core.pulseStart_ge_hold
      have hpulse := d.core.pulseLength_pos
      dsimp only [Parameters.endpoint]
      linarith
    exact true_of_relaxed_negative_slope w _
      (h.relaxed (y, eta) ⟨⟨hleft.trans hy0.le, hp.1.2⟩, hp.2⟩) hyend hneg


structure FullCleanOutgoingCone {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (XR left : ℝ) : Prop extends CleanOutgoingCone w XR left where
  true_from_transition : ∀ p ∈ trueWindowFromTransition d,
    TrueAt w (CorrectedPulseAmplitude.amplitude d w.coefficients) XR p




end NavierStokes.OutgoingNegativeSlopeCone


end


/-! Merged from `NavierStokes.LabelCounting`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# Quantitative counts of slow-grid labels

The boxes here use the actual normalized spacing `S_n⁻³` and the actual
`SlotColoring.Label` indices. The radius factor is arbitrary and fixed, so
the counting bounds include every fixed-factor enlargement.
-/

/-! Merged from `NavierStokes.LabelCountingFinite`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

noncomputable section

namespace NavierStokes.LabelCountingFinite

open SlotColoring
open scoped BigOperators

def gridCandidates (c : Grid) (K : Fin 3 → ℕ) : Finset Grid :=
  Fintype.piFinset (fun j => Finset.Icc (c j - (K j : ℤ)) (c j + (K j : ℤ)))

def labelCandidates (n : ℕ) (c : Grid) (K : Fin 3 → ℕ) : Finset Label :=
  ((gridCandidates c K).product (Finset.univ : Finset Bool)).image (fun gs => (n, gs))








/-- Five consecutive integer indices include every natural band at distance
at most one from a real logarithmic coordinate. -/
def bandCandidates (c : ℝ) : Finset ℕ :=
  (Finset.Icc (⌊c⌋ - 2) (⌊c⌋ + 2)).image Int.toNat






end NavierStokes.LabelCountingFinite


end


noncomputable section

namespace NavierStokes.LabelCounting

open Set
open scoped BigOperators
open SlotColoring SquaredPartition

/-- A closed slow-coordinate grid box with an arbitrary enlargement factor. -/
def normalizedBox (A : ℝ) (L : Label) : Set Position :=
  {x | ∀ j, |x j - nativeSpacing L.1 * (L.2.1 j : ℝ)| ≤ A * nativeSpacing L.1}

/-- Both signs are counted separately, exactly as in the manuscript. -/
def relevantLabels (n : ℕ) (A : ℝ) (B : Set Position) : Set Label :=
  {L | L.1 = n ∧ (normalizedBox A L ∩ B).Nonempty}






/-- A normalized radial slice; the two transverse coordinates are arbitrary. -/
def radialSlice (I : Set ℝ) (Z T : ℝ) : Set Position :=
  {x | x 0 ∈ I ∧ x 1 = Z ∧ x 2 = T}







/-- Labels whose genuine closed dyadic band and enlarged slow box contain
the point. Each band uses its own physical-to-normalized chart. -/
def pointwiseLabels (D A q : ℝ) (x : Position) : Set Label :=
  {L | 1 ≤ L.1 ∧ q ∈ tsupport (dyadicMask (L.1 : ℤ)) ∧
    slowCoordinates D L.1 x ∈ normalizedBox A L}








end NavierStokes.LabelCounting


end


/-! Merged from `NavierStokes.ReferenceEndpointRate`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # The literal linear joining-width estimate at the actual held endpoint -/

noncomputable section

namespace NavierStokes.ReferenceEndpointRate

open Set Filter ProfileHistories ReferencePath NaturalProfile NaturalAxisCoefficients
open ReferenceUniformStocks ReferenceUniformJets TransitionRamp ClosedIntervalJetAlgebra StressActivation
open scoped Topology ContDiff

variable {h j σ Λ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hΛ : 0 < Λ) (hP0 : ContDiff ℝ ∞ P0)
    (hs : NaturalAxisRange.Parameters h j)

/-- The same stock-driven continuation, on the full printed numerical range. -/
def reference (q : Choice d Λ) : StockReference parameterInterval where
  exponent := h
  radius0 := (q.input hΛ).endpoint
  radius0_pos := (q.input hΛ).endpoint_pos
  domain := (q.input hΛ).radialDomain
  profiles := q.profiles hΛ hP0
  log_mem := fun y _ hη => StressActivation.FromReference.log_radius_mem (q.input hΛ) y hη
  f_pos := fun y _ hη => (q.input hΛ).refF_pos q.δ
    (StressActivation.FromReference.log_radius_mem (q.input hΛ) y hη)
    (mul_pos (q.input hΛ).endpoint_pos (Real.exp_pos _)).le
  L_ne_zero := fun η hη => (lt_of_lt_of_le (by norm_num : (0:ℝ)<4879/5000)
    (AppendixJoiningResults.axis_L_lower_bound_window hs.h_pos.le hs.h_le
      ⟨hη.1.le,hη.2.le⟩)).ne'


theorem reference_radius (q : Choice d Λ) :
    (reference d hΛ hP0 hs q).radius0 = 4/Λ := rfl















end NavierStokes.ReferenceEndpointRate


end


/-! Merged from `NavierStokes.WholeDomainPhysicalStageTheorem`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section


/-! Merged from `NavierStokes.WholeDomainPrefixBounds`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

noncomputable section

namespace NavierStokes.WholeDomainStageBounds

open Set Function Filter ProblemStatement PhysicalWaveSum SharpGluedStageBounds
open scoped Topology ContDiff BigOperators

/-- The loss is selected before the length of the finite prefix. -/
def prefixLoss (initial positive : ℕ → ℝ) (m : ℕ) : ℝ := max (initial m) (positive m)

section Prefix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {h qbig : ℝ} {F : ℕ → SpaceTime → V} {gain initial positive : ℕ → ℝ}


end Prefix


end NavierStokes.WholeDomainStageBounds


end

noncomputable section

namespace NavierStokes.WholeDomainStageBounds

open Set Function Filter ProblemStatement PhysicalWaveSum SharpGluedStageBounds
open CorrectionInitialization.ActualPrimary ActualCandidateAssembly
open scoped Topology ContDiff BigOperators

/-- One derivative loss controls both finite fields. It contains no
finite-stage index and is chosen on the original fixed construction. -/
noncomputable def finiteLoss (B N0 : ℕ) (m : ℕ) : ℝ :=
  max
    (prefixLoss (initialVelocityLoss B N0 ActualBaseVelocityBounds.heatLoss)
      (SharpPhysicalCarrier.physicalLoss h) m)
    (prefixLoss (initialPressureTotalLoss B N0 ActualBasePressureBounds.pressureLoss)
      (SharpPhysicalCarrier.physicalLoss h) m)







noncomputable def paperLoss (B N0 : ℕ) (m : ℕ) : ℝ :=
  max (finiteLoss B N0 m) (ActualCycleResidualBounds.fixedLoss m)


/-- A stage-independent loss for all derivatives through the specified order. -/
noncomputable def paperJetLoss (B N0 : ℕ) (m : ℕ) : ℝ :=
  ∑ k : Fin (m+1), |paperLoss B N0 k.val|






end NavierStokes.WholeDomainStageBounds


end


/-! Merged from `NavierStokes.SeedConePaper`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# The compact large-lag assertion of the seed cone lemma

The coordinates here are the literal coordinates in `seed:cone-coordinates`.
The threshold is positive, includes its endpoint, and is common to every
point of the compact set, even when the shear magnitude crosses two.
-/

noncomputable section

open Set

namespace NavierStokes.SeedConePaper

/-- The squared shear parameter in the manuscript. -/
def shearMagnitude (a b : ℝ) : ℝ := a * (1 + (-b / a) ^ 2)

/-- The component of the stress in the unnormalized shear direction. -/
def parallelStress (a b p₁ p₂ : ℝ) : ℝ := p₁ + (-b / a) * p₂

/-- The component of the stress in the orthogonal unnormalized direction. -/
def transverseStress (a b p₁ p₂ : ℝ) : ℝ := p₂ - (-b / a) * p₁

/-- The two relaxed inequalities, including the positive radial shear. -/
def RelaxedCone (a b p₁ p₂ : ℝ) : Prop :=
  0 < a ∧ 2 < parallelStress a b p₁ p₂ ∧
    shearMagnitude a b < ConeAlgebra.coneBound
      (parallelStress a b p₁ p₂) (transverseStress a b p₁ p₂)

/-- The relaxed cone with the additional lower bound required by the waves. -/
def AdmissibleCone (a b p₁ p₂ : ℝ) : Prop :=
  RelaxedCone a b p₁ p₂ ∧ 2 < shearMagnitude a b




end NavierStokes.SeedConePaper


end


/-! Merged from `NavierStokes.AxisModelBounds`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# The numerical bounds for the axis comparison profile

The profile in `axis:model-series` is an actual convergent series.  The
following bounds retain the rational lower bound in `axis:model-positive`,
including its stated decimal consequence, on the whole interval `[0, 4.1]`.
-/

noncomputable section

namespace NavierStokes.AxisModelBounds

/-- The comparison function `f₀` in the axis construction. -/
def model (z : ℝ) : ℝ := AxisSeries.profile 1 z






end NavierStokes.AxisModelBounds


end


/-! Merged from `NavierStokes.PaperLocalization`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# Localization of the same fields as the local theorem

The local construction and the compact whole-space candidate below use one
diagonal schedule. Their velocity and pressure agree on a fixed neighborhood
of the origin for every sufficiently late presingular time, as required by
`global:localization`.
-/

noncomputable section

namespace NavierStokes.PaperLocalization

open Set Filter ProblemStatement
open scoped ContDiff



end NavierStokes.PaperLocalization


end


/-! Merged from `NavierStokes.TrueConeLoopPaper`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! Compact loop data specified on a neighborhood of the closed parameter
set suffice for the loop construction and its uniform cone margin. -/

noncomputable section

open Set
open scoped ContDiff

namespace NavierStokes.TrueConeLoopPaper

open TrueConeLoop SmoothLoop LoopMoments LoopVariance ConeAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]



end NavierStokes.TrueConeLoopPaper


end


/-! Merged from `NavierStokes.ParameterizedMomentRepair`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

noncomputable section

namespace NavierStokes.ParameterizedMomentRepair

open Set
open scoped ContDiff

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


open ClosedIntervalCk ClosedIntervalMomentRepair


end NavierStokes.ParameterizedMomentRepair


end


/-! Merged from `NavierStokes.TerminalEdgePaper`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! The lower weighted estimate for the actual terminal stress. -/

noncomputable section

open Set

namespace NavierStokes.TerminalEdgePaper

open TerminalEdgeFactor OutgoingTail


end NavierStokes.TerminalEdgePaper


end

section

/-! # Pressure-scaled positivity at the actual natural-axis root -/

noncomputable section

namespace NavierStokes.AxisRootPressureBounds

open Set NaturalAxisData



end NavierStokes.AxisRootPressureBounds


end

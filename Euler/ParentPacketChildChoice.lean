import Euler.ParentParticleInverse
import Euler.ParentPacketJoinedInput
import Euler.PacketInitializedChildBounds

/-! An actual parent and its common source budgets produce a packet
whose composed particle map is a new parent, with a genuine inverse and
the source H⁶ label bound k^80. The correction and the two global errors
are the same ones used to construct that particle map. -/

noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set Filter InnerProductSpace EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketCorrectionScalar EulerPacketSourceFrequency EulerAllOrderDriftCorrection
  EulerLiftedGradientSpace EulerGraphInvariantFlow EulerPhysicalGraphFlowBounds
  EulerPacketPrimaryFactorization EulerGraphPressurePotential EulerPeriodicProfile
  EulerSobolevGevreyOperators EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerGevrey EulerMeanClassicalWordBounds EulerPacketParentLabelBounds
  EulerPacketTerminalDatum

variable {A : Parent} (L : LabelData A) (I : ParticleInverse A) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < A.T)


variable (J : JoinedInputs (A.meanData H) (A.transverseData m hm R S hS) τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT))
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ S) (α : ℝ) (hα : 0 < α)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)



end EulerParentPacketFrames.LabelData

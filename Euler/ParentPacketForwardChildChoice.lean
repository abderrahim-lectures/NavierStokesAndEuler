import Euler.ParentParticleInverse
import Euler.ParentPacketForwardInput
import Euler.PacketForwardInitializedChildShear

/-! The first, zero-history packet produces an actual next parent with
the H⁶ label bound k^80, a continuous two-sided inverse, and the same
correction and global shear/Hessian estimates used in its construction. -/

noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set Filter InnerProductSpace EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketCorrectionScalar EulerPacketSourceFrequency EulerAllOrderDriftCorrection
  EulerLiftedGradientSpace EulerGraphInvariantFlow EulerPhysicalGraphFlowBounds
  EulerPacketForwardFactorization EulerGraphPressurePotential EulerPeriodicProfile
  EulerSobolevGevreyOperators EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerGevrey EulerMeanClassicalWordBounds EulerPacketParentLabelBounds
  EulerPacketTerminalDatum

variable {A : Parent} (L : LabelData A) (I : ParticleInverse A) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S)


variable (J : ForwardInputs (A.meanData H) (A.transverseData m hm R S hS))
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ S) (α : ℝ) (hα : 0 < α)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)



end EulerParentPacketFrames.LabelData

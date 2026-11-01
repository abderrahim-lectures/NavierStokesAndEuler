import Euler.PacketExactGlobalShear
import Euler.PacketExactPressureError
import Euler.PacketInitializedHessianChoice

/-! Both global identities in source (20) for one actual exact packet.
The velocity and canonical scalar pressure have uniform O(1/k) errors. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set Filter Finset InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerSpatialCutoffs EulerTransversePacketProvider EulerPacketCylinderField
  EulerPacketProfileRecursion EulerPacketTimeProfile EulerPacketCoarseMajorant
  EulerPacketCorrectionScalar EulerPacketSourceFrequency EulerLiftedGradientSpace
  EulerPacketPrimaryFactorization EulerPacketInverseFlowGevrey EulerGevrey
  EulerGraphPressurePotential EulerPeriodicProfile
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T=D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  {Rm : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (Cagree : SourceCoefficientAgreement M D)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t, ContDiff ℝ ∞ (X t))
  (hF : ∀ t x, fderiv ℝ (X t) x = D.F.field t x)
  (hXY : ∀ t x, X t (Y t x)=x)
  (hY : Continuous (Function.uncurry Y))
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det=1)

include hδ1 hα L NB LM hX hF hXY hY hdet


end EulerPacketTerminalDatum

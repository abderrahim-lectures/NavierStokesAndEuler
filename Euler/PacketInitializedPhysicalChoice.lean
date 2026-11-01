import Euler.PacketInitializedPointwiseChoice
import Euler.PacketPhysicalFrequencyBounds
import Euler.PacketContinuousInverse

/-! The actual initialized correction is smaller than every prescribed
inverse power in every fixed physical C^N norm, uniformly over the full
time interval. All coordinate-change costs are fixed by the parent data. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set Filter Finset EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketCorrectionScalar
  EulerPacketSourceFrequency EulerLiftedGradientSpace EulerCylinderSobolev
  EulerPacketPhysicalGevrey EulerPacketInverseFlowGevrey EulerGraphPressurePotential
  EulerCylinderPhysicalTensor EulerGevrey
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
  (Ξ Y : Icc (0 : ℝ) D.T → Space → Space)
  (hΞ : ∀ t, ContDiff ℝ ∞ (Ξ t))
  (hF : ∀ t x, fderiv ℝ (Ξ t) x = D.F.field t x)
  (hΞY : ∀ t x, Ξ t (Y t x)=x) (hY : Continuous (Function.uncurry Y))
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det=1)
  (R CF : ℝ) (hR : 0 ≤ R) (hCF : 0 ≤ CF)
  (hFb : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ CF*majorant R 0 n)


end EulerPacketTerminalDatum

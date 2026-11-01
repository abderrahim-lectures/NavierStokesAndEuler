import Euler.PacketForwardInitializedFlowAndShear
import Euler.PhysicalChildSourceBound

/-! One actual zero-history initialized correction simultaneously satisfies the
global shear/Hessian estimates and the source C*=10(s+2) child-label
bound. The child fields are constructed from the actual graph flow and
the parent displacement, velocity and acceleration. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set Filter InnerProductSpace EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketCorrectionScalar EulerPacketSourceFrequency EulerAllOrderDriftCorrection
  EulerLiftedGradientSpace EulerGraphInvariantFlow EulerPhysicalGraphFlowBounds
  EulerPacketForwardFactorization EulerGraphPressurePotential EulerPeriodicProfile
  EulerSobolevGevreyOperators EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerGevrey EulerMeanClassicalWordBounds EulerPacketParentLabelBounds EulerSobolevSourceExponent
  EulerSmoothBanachFlow
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hTime : M.T=D.T)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  {Rm : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (Cagree : SourceCoefficientAgreement M D)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t, ContDiff ℝ ∞ (X t))
  (hF : ∀ t x, fderiv ℝ (X t) x = D.F.field t x)
  (hXY : ∀ t x, X t (Y t x)=x) (hY : Continuous (Function.uncurry Y))
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det=1)
  (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
  (Dp Vp Wp : Icc (0 : ℝ) D.T → SmoothL2Field Space)
  (K : ℝ) (hK : 1 ≤ K)
  (hDp : ∀ t, HasLabelBound K (Dp t))
  (hVp : ∀ t, HasLabelBound K (Vp t))
  (hWp : ∀ t, HasLabelBound K (Wp t))

include hδ1 hα L NB LM hX hF hXY hY hdet hell1 hK hDp hVp hWp


end EulerPacketTerminalDatum

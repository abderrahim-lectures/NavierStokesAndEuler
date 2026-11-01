import Euler.CylinderTimeGradient
import Euler.PacketPotentialRegularity

/-! Actual one-sided time differentiation of the packet's spatial curl corrector. -/

noncomputable section

namespace EulerPacketPiola

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerTransportDerivatives EulerCylinderSmoothOrbit
  EulerLpCylinderTranslation EulerVolterraConvolution EulerLiftedWeakDerivative EulerMeanBoundary
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  (T : ℝ) (hT : 0 ≤ T) (p f : C(Icc (0 : ℝ) T,LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))
  (hd : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT p) (f t) (Icc (0 : ℝ) T) t)

include hd



end EulerPacketPiola

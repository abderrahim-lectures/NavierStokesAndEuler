import Euler.PhysicalGraphFlowBounds
import Euler.PacketGraphFlowFrequency

/-! The frequency estimates apply directly to the actual rescaled graph
flow fields, with arbitrarily small losses in the frequency exponent. -/

noncomputable section


namespace EulerPhysicalGraphFlowBounds

open Set Filter EulerLiftedGradientSpace EulerSmoothFlowGevrey
  EulerPacketGraphFlowFrequency EulerCylinderGraphGevrey
  EulerLpTranslation.SmoothL2Field

variable (P T : ℝ) [Fact (0 < P)]


end EulerPhysicalGraphFlowBounds

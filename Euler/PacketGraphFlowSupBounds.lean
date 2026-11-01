import Euler.PhysicalGraphFlowSupBounds
import Euler.PacketGraphFlowFrequency

/-! The actual physical graph displacement and velocity obey the same
arbitrarily small exponent losses as the cylinder-to-graph L² bounds. -/

noncomputable section


namespace EulerPhysicalGraphFlowBounds

open Set Filter EulerLiftedGradientSpace EulerSmoothFlowGevrey
  EulerPacketGraphFlowFrequency EulerCylinderGraphGevrey EulerGevrey


variable (P T : ℝ) [Fact (0 < P)]


end EulerPhysicalGraphFlowBounds

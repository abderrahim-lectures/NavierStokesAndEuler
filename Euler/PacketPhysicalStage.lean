import Euler.PacketMatrixContinuity
import Euler.PacketWithinRay
import Euler.PacketTangentInvariant

/-!
The physical ray and velocity equations, the actual parent rank-one
decomposition, and physical coefficient bounds imply relative amplification
for the scaled primary.  No scaled ODE, ray lower bound, or matrix-error
estimate is assumed.
-/

noncomputable section


namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  EulerPacketStage EulerPacketPerturbation InnerProductSpace ContinuousLinearMap


end EulerPacketMovingFrame

import Euler.PacketScaledVelocitySystem
import Euler.ClosedIntervalDerivativeExtension

/-!
The actual closed-interval packet equations feed the checked scalar
amplification theorem.  Endpoint derivatives are extended explicitly; only
the first two physical transport rows enter the comparison.
-/

noncomputable section


namespace EulerPacketMovingFrame

open Set EulerPacketRay EulerPacketStage EulerPacketPerturbation
  EulerClosedIntervalDerivativeExtension


end EulerPacketMovingFrame

import Euler.ParentPacketHessianSymmetry
import Euler.ParentPacketJoinedInput
import Euler.CylinderEndpointLabels

/-! Sharp physical low bounds give the actual center-history bounds used
in activation. These use the physical gradient and pressure Hessian;
they do not replace them by the high-order label envelope. -/

noncomputable section

namespace EulerParentPacketFrames.Parent

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerTransverseSourceCoefficientPath EulerTimeIntervalRestriction
open scoped ContDiff

variable (G : Parent)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)




end EulerParentPacketFrames.Parent

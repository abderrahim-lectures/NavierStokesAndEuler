import Euler.ParentEulerSobolev

/-! The physical gradient is continuous up to the endpoints in the
actual Sobolev class. Incompressibility therefore holds at time zero
and the final time as well as in the open Euler interval. -/

noncomputable section

namespace EulerParentPacketFrames.SobolevData

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSobolevBoundedField EulerMeanCoefficients
open scoped Topology

variable {A : Parent} {E : Evolution A} (S : SobolevData E)

include S



end EulerParentPacketFrames.SobolevData

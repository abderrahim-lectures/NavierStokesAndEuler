import NavierStokes.UniformQuadraticBranch
import NavierStokes.ClosedIntervalMomentRepair

noncomputable section

namespace NavierStokes.ParameterizedMomentRepair

open Set
open scoped ContDiff

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


open ClosedIntervalCk ClosedIntervalMomentRepair


end NavierStokes.ParameterizedMomentRepair

import NavierStokes.WithinPathFamily
import NavierStokes.JointODE

/-! # Joint ODE jets on closed parameter and pulse domains -/

noncomputable section

namespace NavierStokes.WithinJointODE

open Set Filter Function
open scoped Topology ContDiff

universe u

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {a b : ℝ}




end NavierStokes.WithinJointODE

namespace NavierStokes.WithinJetClosure

open Set Filter
open scoped Topology ContDiff

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]



end NavierStokes.WithinJetClosure

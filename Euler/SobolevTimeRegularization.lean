import Euler.TimeLpStrongOperators
import Euler.TimeLpMultiplier
import Euler.HeatRegularizedPaths

/-! Strong actual heat approximation and time-dependent operator commutators in Bochner Sobolev spaces. -/

noncomputable section

namespace EulerSobolevTimeRegularization

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerHeatRegularizedPaths EulerTimeLp
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]




end EulerSobolevTimeRegularization

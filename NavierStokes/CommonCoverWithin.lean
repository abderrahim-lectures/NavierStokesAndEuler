import NavierStokes.WithinJointODE
import NavierStokes.CommonCoverSolve
import NavierStokes.CommonCoverClass

/-! # Common-torus inverse at a one-sided slow endpoint

All inputs have genuine joint within regularity on the slow domain. The
actual copy and common-torus solves inherit it; an open continuation of the
source is not required.
-/

noncomputable section

namespace NavierStokes.CommonCoverSolve.LinearData

open Set Filter Function
open scoped Topology ContDiff
open TorusInverse

variable {P V E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ} (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)
  {U : Set P} (hU : Convex ℝ U) (hu : UniqueDiffOn ℝ U)
  (hA : ContDiffOn ℝ ∞ d.coefficient (U ×ˢ univ))
  (hB : ContDiffOn ℝ ∞ d.forcingMap (U ×ˢ univ))
  (hf : ContDiffOn ℝ ∞ d.source (U ×ˢ univ))

include hU hu hA hB hf


/-- The current copy argument with the unclamped endpoint-rescaled solve. -/
noncomputable def copySolveRepresentative (k : Frequency) (p : P × Plane) : E :=
  JointODE.reparamSolution a (d.coefficientAlong g k) (fun _ => 0)
    (d.forcingAlong g k) (p, (g.coordinates k p.2).2)








end NavierStokes.CommonCoverSolve.LinearData

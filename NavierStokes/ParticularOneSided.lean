import NavierStokes.WithinPathFamily
import NavierStokes.JointODE
import NavierStokes.CommonCoverSolve
import NavierStokes.CommonCoverClass
import NavierStokes.ParticularWaveBounds
import NavierStokes.GenericEndpointExtension

/-! # The slow-time-zero clause of the common-torus particular inverse

Uniform interior jets determine genuine closed-side smoothness. The actual
common-torus velocity and pressure inherit these one-sided jets, uniformly
on compact parameter sets. No analytic regularity or open extension of an
arbitrary source is required.
-/

/-! Merged from `NavierStokes.WithinJointODE`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

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


end


/-! Merged from `NavierStokes.CommonCoverWithin`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

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


end


/-! Merged from `NavierStokes.ParticularWithinPressure`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # One-sided jets of the actual particular velocity and pressure -/

noncomputable section

namespace NavierStokes.ParticularWaveBounds

open Set Filter Function
open scoped ContDiff Topology InnerProductSpace
open CommonCoverSolve TorusInverse

section Real

variable {P H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]



end Real

section Complex

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]


variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]



end Complex

end NavierStokes.ParticularWaveBounds


end


/-! Merged from `NavierStokes.ParticularWithinBounds`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # The particular inverse estimate at closed slow and pulse endpoints -/

noncomputable section

namespace NavierStokes.ParticularWaveBounds

open Set Function Filter
open scoped ContDiff Topology InnerProductSpace
open PrimaryPulseBounds

variable {Q H : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]


end NavierStokes.ParticularWaveBounds


end


noncomputable section

namespace NavierStokes.ParticularOneSided

open Set Filter
open scoped ContDiff Topology
open CommonCoverSolve TorusInverse ParticularWaveBounds

section InputTraces

variable {Y E : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


end InputTraces

section UniformJets

variable {Y E : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]



end UniformJets

section CommonTorus

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

def slowDomain (W : Set X) : Set (ℝ × X) := Ici (0 : ℝ) ×ˢ W
def positiveDomain (W : Set X) : Set (ℝ × X) := Ioi (0 : ℝ) ×ˢ W








end CommonTorus

end NavierStokes.ParticularOneSided

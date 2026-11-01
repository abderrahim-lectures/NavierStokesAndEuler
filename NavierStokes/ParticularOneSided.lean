import NavierStokes.ParticularWithinPressure
import NavierStokes.ParticularWithinBounds
import NavierStokes.GenericEndpointExtension

/-! # The slow-time-zero clause of the common-torus particular inverse

Uniform interior jets determine genuine closed-side smoothness. The actual
common-torus velocity and pressure inherit these one-sided jets, uniformly
on compact parameter sets. No analytic regularity or open extension of an
arbitrary source is required.
-/

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

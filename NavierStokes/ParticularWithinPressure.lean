import NavierStokes.CommonCoverWithin
import NavierStokes.ParticularWaveBounds

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

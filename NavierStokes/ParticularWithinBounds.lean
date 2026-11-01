import NavierStokes.WithinJointODE
import NavierStokes.ParticularWaveBounds

/-! # The particular inverse estimate at closed slow and pulse endpoints -/

noncomputable section

namespace NavierStokes.ParticularWaveBounds

open Set Function Filter
open scoped ContDiff Topology InnerProductSpace
open PrimaryPulseBounds

variable {Q H : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]


end NavierStokes.ParticularWaveBounds

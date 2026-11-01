import NavierStokes.GenericSolenoidalRealization

noncomputable section

namespace NavierStokes.GenericSolenoidalRealization

open Set Filter ProblemStatement AxisymmetricFields DirectAngularDiagonal
open scoped Topology ContDiff BigOperators

private def radialFactor (w : SpaceTime) (p : ProfilePoint) : ℝ :=
  Real.sqrt (p.2.1 / radialEnergy w.2)

/-- A local section of the cylindrical coordinate map through the given
off-axis Cartesian point, retaining its angular direction. -/
private def radialSection (w : SpaceTime) (p : ProfilePoint) : SpaceTime :=
  (p.1, AxisymmetricResidual.pack (radialFactor w p * w.2 0)
    (radialFactor w p * w.2 1) p.2.2)











end NavierStokes.GenericSolenoidalRealization

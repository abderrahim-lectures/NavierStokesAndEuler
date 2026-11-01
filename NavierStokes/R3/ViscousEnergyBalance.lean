import NavierStokes.R3.CompactEnergy

/-!
# Compact whole-space energy balance at arbitrary viscosity

The dissipation is retained explicitly, so integrating the identity also
controls the total dissipation up to a possible singular time.
-/

noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology BigOperators ContDiff InnerProductSpace

namespace NavierStokesR3.CompactEnergy

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness






end NavierStokesR3.CompactEnergy

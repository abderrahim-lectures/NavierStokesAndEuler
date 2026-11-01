import NavierStokes.R3.H3WeakStrong
import NavierStokes.R3.H3CandidateStrong
import NavierStokes.R3.H3PressureOrthogonality
import NavierStokes.R3.CompactComparisonBounds

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

namespace NavierStokesR3.H3Comparison

open ProblemStatement
open NavierStokes.ProblemStatement (pressureGradient spatialDerivative coordinateVector)
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness (slab spatial_smooth)





end NavierStokesR3.H3Comparison

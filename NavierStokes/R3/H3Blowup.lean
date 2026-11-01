import NavierStokes.R3.H3CompactCurve
import NavierStokes.R3.H3StrongSolution

/-! # Whole-space H³ blowup and the exclusion of H³ continuation

The obstruction is the actual Sobolev norm and its continuous topology. It
applies to weak H³ spatial fields, rather than a class requiring C∞ velocity.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace NavierStokesR3.H3Embedding

open ProblemStatement H3Comparison
open NavierStokes.PeriodicUniqueness (slab spatial_smooth)





end NavierStokesR3.H3Embedding

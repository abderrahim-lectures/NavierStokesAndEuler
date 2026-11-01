import NavierStokes.R3.H3PressureDistribution
import NavierStokes.R3.H3DivCurlFourier

/-! # Pressure cancellation for ordinary first-order Sobolev fields

The pressure is an arbitrary C¹ scalar function. Only its gradient must be
square integrable; no decay or growth condition is imposed on the pressure.
-/

noncomputable section

open Set Filter MeasureTheory LineDeriv
open scoped ContDiff Topology BigOperators LineDeriv

namespace NavierStokesR3.H3PressureOrthogonality

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open H3Comparison H3PressureDistribution

def complexComponent (i : Fin 3) : Space →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj i)

@[simp] theorem complexComponent_apply (i : Fin 3) (x : Space) :
    complexComponent i x = (x i : ℂ) := rfl






end NavierStokesR3.H3PressureOrthogonality

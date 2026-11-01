import NavierStokes.R3.ViscousEnergyBalance
import NavierStokes.R3.SpatialCauchySchwarz
import NavierStokes.R3.SharpEnergyBound
import NavierStokes.R3.ForceL2Norm
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Finite integrated dissipation up to the singular time

The time integrability statement is explicit: a totalized real integral is not
used as a substitute for finiteness of the dissipation. The energy balance is
first integrated on shorter closed time intervals, then an exhaustion proves
integrability on the entire half-open interval.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace NavierStokesR3.CompactEnergy

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicUniqueness









end NavierStokesR3.CompactEnergy

import NavierStokes.R3.WeakFourierUniqueness
import Mathlib.Analysis.Fourier.LpSpace

/-! # Orthogonality of square integrable divergence-free and curl-free fields -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators FourierTransform

namespace NavierStokesR3.H3DivCurlFourier

open ProblemStatement
open NavierStokes.ProblemStatement (coordinateVector)

abbrev ComplexL2 := Lp ℂ 2 (volume : Measure Space)
abbrev ComplexDistribution := TemperedDistribution Space ℂ

def coordinate (i : Fin 3) (ξ : Space) : ℂ := ξ i




def multiplier (i : Fin 3) (f : ComplexL2) : ComplexDistribution :=
  TemperedDistribution.smulLeftCLM ℂ (coordinate i) (Lp.toTemperedDistribution f)















end NavierStokesR3.H3DivCurlFourier

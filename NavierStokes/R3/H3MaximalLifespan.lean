import NavierStokes.R3.H3CandidateStrong
import NavierStokes.R3.H3Transport
import NavierStokes.R3.ComparisonGronwall
import NavierStokes.R3.H3StrongSolution
import NavierStokes.R3.H3PressureDistribution
import NavierStokes.R3.WeakFourierUniqueness
import Mathlib.Analysis.Fourier.LpSpace
import NavierStokes.R3.CompactComparisonBounds
import NavierStokes.R3.H3CompactCurve
import NavierStokes.R3.Theorem

/-! # Exact maximal classical H³ lifespan on ℝ³

The solution class uses genuine weak H³ jets with their L² topology, actual
L² time differentiation, and the same forcing and initial velocity. No
periodicity or pressure normalization is imposed on competing solutions.
-/

/-! Merged from `NavierStokes.R3.H3PressureOrthogonality`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Pressure cancellation for ordinary first-order Sobolev fields

The pressure is an arbitrary C¹ scalar function. Only its gradient must be
square integrable; no decay or growth condition is imposed on the pressure.
-/

/-! Merged from `NavierStokes.R3.H3DivCurlFourier`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

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


end


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


end


/-! Merged from `NavierStokes.R3.H3Energy`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Difference energy for ordinary H³ fields

The time derivative is a derivative in the L² Hilbert space. Spatial
integration by parts uses the actual weak derivative approximations.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

namespace NavierStokesR3.H3Comparison

open NavierStokes.ProblemStatement






end NavierStokesR3.H3Comparison


end


/-! Merged from `NavierStokes.R3.H3Blowup`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

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


end


/-! Merged from `NavierStokes.R3.H3CandidateUniqueness`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section


/-! Merged from `NavierStokes.R3.H3WeakStrong`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Weak–strong comparison in the ordinary H³ class -/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

namespace NavierStokesR3.H3Comparison

open ProblemStatement
open NavierStokes.ProblemStatement (pressureGradient)



end NavierStokesR3.H3Comparison


end

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

namespace NavierStokesR3.H3Comparison

open ProblemStatement
open NavierStokes.ProblemStatement (pressureGradient spatialDerivative coordinateVector)
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness (slab spatial_smooth)





end NavierStokesR3.H3Comparison


end


noncomputable section

open Set

namespace NavierStokesR3.H3Comparison

open ProblemStatement H3Embedding

def ClassicalH3Solution.restrict {ν T S : ℝ} {f u : VelocityField} {p : PressureField}
    {initial : Space → Space} (h : ClassicalH3Solution ν f initial T u p)
    (hS : 0 < S) (hST : S ≤ T) : ClassicalH3Solution ν f initial S u p where
  lifespan_pos := hS
  initial_velocity := h.initial_velocity
  on_shorter_interval := fun R hR => h.on_shorter_interval R ⟨hR.1, hR.2.trans_le hST⟩

def VelocityAgreesOn (T : ℝ) (u v : VelocityField) : Prop :=
  ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, u (t, x) = v (t, x)

def HasClassicalH3Extension (ν : ℝ) (f : VelocityField) (initial : Space → Space)
    (T : ℝ) (u : VelocityField) : Prop :=
  ∃ S : ℝ, ∃ v : VelocityField, ∃ q : PressureField,
    T < S ∧ Nonempty (ClassicalH3Solution ν f initial S v q) ∧ VelocityAgreesOn T u v

def IsMaximalClassicalH3Solution (ν : ℝ) (f : VelocityField) (initial : Space → Space)
    (T : ℝ) (u : VelocityField) (p : PressureField) : Prop :=
  Nonempty (ClassicalH3Solution ν f initial T u p) ∧ ¬HasClassicalH3Extension ν f initial T u

def admissibleH3Lifespans (ν : ℝ) (f : VelocityField) (initial : Space → Space) : Set ℝ :=
  {T | ∃ u : VelocityField, ∃ p : PressureField, Nonempty (ClassicalH3Solution ν f initial T u p)}








end NavierStokesR3.H3Comparison

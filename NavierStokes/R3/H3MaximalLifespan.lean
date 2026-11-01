import NavierStokes.R3.H3CandidateStrong
import NavierStokes.R3.H3CandidateUniqueness
import NavierStokes.R3.H3Blowup
import NavierStokes.R3.Theorem

/-! # Exact maximal classical H³ lifespan on ℝ³

The solution class uses genuine weak H³ jets with their L² topology, actual
L² time differentiation, and the same forcing and initial velocity. No
periodicity or pressure normalization is imposed on competing solutions.
-/

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

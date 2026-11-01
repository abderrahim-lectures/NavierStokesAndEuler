import NavierStokes.UniformCone

/-!
# The compact large-lag assertion of the seed cone lemma

The coordinates here are the literal coordinates in `seed:cone-coordinates`.
The threshold is positive, includes its endpoint, and is common to every
point of the compact set, even when the shear magnitude crosses two.
-/

noncomputable section

open Set

namespace NavierStokes.SeedConePaper

/-- The squared shear parameter in the manuscript. -/
def shearMagnitude (a b : ℝ) : ℝ := a * (1 + (-b / a) ^ 2)

/-- The component of the stress in the unnormalized shear direction. -/
def parallelStress (a b p₁ p₂ : ℝ) : ℝ := p₁ + (-b / a) * p₂

/-- The component of the stress in the orthogonal unnormalized direction. -/
def transverseStress (a b p₁ p₂ : ℝ) : ℝ := p₂ - (-b / a) * p₁

/-- The two relaxed inequalities, including the positive radial shear. -/
def RelaxedCone (a b p₁ p₂ : ℝ) : Prop :=
  0 < a ∧ 2 < parallelStress a b p₁ p₂ ∧
    shearMagnitude a b < ConeAlgebra.coneBound
      (parallelStress a b p₁ p₂) (transverseStress a b p₁ p₂)

/-- The relaxed cone with the additional lower bound required by the waves. -/
def AdmissibleCone (a b p₁ p₂ : ℝ) : Prop :=
  RelaxedCone a b p₁ p₂ ∧ 2 < shearMagnitude a b




end NavierStokes.SeedConePaper

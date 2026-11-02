import NavierStokes.R3.CompactSchwartz
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff

/-!
# Compact support approximation in Schwartz space

Compactly supported smooth tests are dense in Schwartz space, and a continuous
functional that vanishes on them vanishes on every test. Both are taken from the
library: `SchwartzMap.dense_hasCompactSupport` is TauCeti's, and the two
consequences below are closed-interval arguments on top of it. The earlier
version of this file reconstructed that density theorem from a cutoff family and
a seminorm estimate; nothing used the construction, and TauCeti proves the
statement for the same object.
-/

noncomputable section

open Set Filter

namespace NavierStokesR3.SchwartzCompactApproximation

open ProblemStatement

/-- Compactly supported smooth tests are dense in Schwartz space. -/
theorem dense_hasCompactSupport :
    Dense {ψ : SchwartzMap Space ℂ | HasCompactSupport (ψ : Space → ℂ)} :=
  SchwartzMap.dense_hasCompactSupport

/-- A continuous functional vanishing on compact tests vanishes on every Schwartz test. -/
theorem continuous_zero_of_compactSupport (F : SchwartzMap Space ℂ → ℂ)
    (hF : Continuous F)
    (hzero : ∀ ψ : SchwartzMap Space ℂ, HasCompactSupport (ψ : Space → ℂ) → F ψ = 0)
    (ψ : SchwartzMap Space ℂ) : F ψ = 0 := by
  have hclosed : IsClosed {φ : SchwartzMap Space ℂ | F φ = 0} :=
    isClosed_eq hF continuous_const
  have hsub : {φ : SchwartzMap Space ℂ | HasCompactSupport (φ : Space → ℂ)} ⊆
      {φ : SchwartzMap Space ℂ | F φ = 0} := fun φ hφ => hzero φ hφ
  have hmem : ψ ∈ closure {φ : SchwartzMap Space ℂ | HasCompactSupport (φ : Space → ℂ)} := by
    rw [dense_hasCompactSupport.closure_eq]
    exact mem_univ ψ
  exact hclosed.closure_subset_iff.2 hsub hmem

/-- The continuous linear form version of compact-test extension. -/
theorem eq_zero_of_compactSupport (F : SchwartzMap Space ℂ →L[ℂ] ℂ)
    (hzero : ∀ ψ : SchwartzMap Space ℂ, HasCompactSupport (ψ : Space → ℂ) → F ψ = 0)
    (ψ : SchwartzMap Space ℂ) : F ψ = 0 :=
  continuous_zero_of_compactSupport F F.continuous hzero ψ

/-- In particular, an identity tested after a continuous differential operator extends. -/
theorem comp_eq_zero_of_compactSupport
    (F : SchwartzMap Space ℂ →L[ℂ] ℂ)
    (L : SchwartzMap Space ℂ →L[ℂ] SchwartzMap Space ℂ)
    (hzero : ∀ ψ : SchwartzMap Space ℂ,
      HasCompactSupport (ψ : Space → ℂ) → F (L ψ) = 0)
    (ψ : SchwartzMap Space ℂ) : F (L ψ) = 0 :=
  eq_zero_of_compactSupport (F.comp L) hzero ψ

end NavierStokesR3.SchwartzCompactApproximation

import NavierStokes.ComparatorBridge

/-!
# Viscosity normalization for the whole-space comparator

This version retains the comparator's square integrability and uniform kinetic
energy bound. It makes no periodicity or compact-support assumption on a
hypothetical global solution.
-/

noncomputable section

namespace NavierStokes.ComparatorBridge

open Set MeasureTheory InnerProductSpace ProblemStatement
open scoped ContDiff Laplacian

theorem zero_initial_condition_decay :
    Comparator.InitialVelocityConditionDecay (fun _ : Space => (0 : Space)) := by
  refine ⟨⟨fun x => Comparator.divergence_const 0 x, contDiff_const⟩, ?_⟩
  intro m K
  exact ⟨0, by simp⟩

/-- A global whole-space solution in the original physical coordinates. -/
structure GlobalSolutionRn (f : VelocityField) (v : VelocityField) (p : PressureField) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ v futureDomain
  pressure_smooth : ContDiffOn ℝ ∞ p futureDomain
  initial_velocity : ∀ x : Space, v (0, x) = 0
  divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Space, spatialDivergence v t x = 0
  navier_stokes : ∀ t : ℝ, 0 < t → ∀ x : Space, navierStokesResidual v p t x = f (t, x)
  integrable : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Space => ‖v (t, x)‖) 2
  globally_bounded_energy : ∃ E : ℝ, ∀ t : ℝ, 0 ≤ t → (∫ x : Space, ‖v (t, x)‖ ^ 2) < E

theorem comparator_equation_Rn {ν : ℝ} {u₀ : Space → Space} {f v : Space → ℝ → Space}
    {p : Space → ℝ → ℝ}
    (h : Comparator.NavierStokesExistenceAndSmoothnessRn ν u₀ f v p)
    {t : ℝ} (ht : 0 < t) (x : Space) :
    temporalDerivative (fromComparator v) t x + advection (fromComparator v) t x -
      ν • spatialLaplacian (fromComparator v) t x +
      pressureGradient (fromComparator p) t x = f x t := by
  have hv := smooth_space_slice (fromComparator_smooth h.velocity_smooth) ht.le
  rw [temporalDerivative_eq _ ht, laplacian_eq _ _ _
    (hv.of_le (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2).le), gradient_eq]
  change derivWithin (v x) (Ici 0) t + fderiv ℝ (v · t) x (v x t) -
    ν • Δ (v · t) x + gradient (p · t) x = f x t
  rw [h.navier_stokes x t ht.le]
  abel


end NavierStokes.ComparatorBridge

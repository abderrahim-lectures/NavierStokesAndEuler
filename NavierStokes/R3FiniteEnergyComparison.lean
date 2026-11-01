import NavierStokes.R3.WholeSpaceUniqueness
import NavierStokes.R3CompactCandidate
import NavierStokes.ComparatorR3Bridge

/-!
# Comparison with the compact candidate on all of R³

The whole-space uniqueness proof is ported from the verified R³ development.
The competitor retains exactly the smoothness and finite-energy conditions
of the comparator. The candidate's compact support supplies the reference
solution's bounds on each closed interval before time one.
-/

noncomputable section

namespace NavierStokes.ComparatorBridge

open Set MeasureTheory ProblemStatement
open scoped ContDiff

theorem GlobalSolutionRn.uniformFiniteEnergy {f v : VelocityField} {q : PressureField}
    (h : GlobalSolutionRn f v q) (T : ℝ) :
    NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v := by
  obtain ⟨E, hE⟩ := h.globally_bounded_energy
  refine ⟨max 0 (E / 2), le_max_left _ _, ?_⟩
  intro t ht
  constructor
  · simpa only [NavierStokesR3.ProblemStatement.SquareIntegrableAtTime, norm_norm] using!
      (memLp_two_iff_integrable_sq_norm
        (h.integrable t ht.1).aestronglyMeasurable).mp (h.integrable t ht.1)
  · change (1 / 2 : ℝ) * (∫ x : Space, ‖v (t, x)‖ ^ 2) ≤ max 0 (E / 2)
    have hb := (hE t ht.1).le
    have hm := le_max_right 0 (E / 2)
    linarith


end NavierStokes.ComparatorBridge

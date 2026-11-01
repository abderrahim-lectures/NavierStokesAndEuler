import NavierStokes.LocalPaperHeat
import NavierStokes.R3.Theorem

/-!
# Localization of the same fields as the local theorem

The local construction and the compact whole-space candidate below use one
diagonal schedule. Their velocity and pressure agree on a fixed neighborhood
of the origin for every sufficiently late presingular time, as required by
`global:localization`.
-/

noncomputable section

namespace NavierStokes.PaperLocalization

open Set Filter ProblemStatement
open scoped ContDiff

theorem compact_pressure_eq_local (P : PressureField) {t : ℝ} (ht : 3 / 4 ≤ t)
    {x : Space} (hx : x ∈ SpatialLocalization.plateau) :
    R3CompactCandidate.pressure P (t, x) = P (t, x) := by
  rw [R3CompactCandidate.pressure, TimeLocalization.activatedPressure_eq_late _ ht]
  exact (SpatialLocalization.cutPressure_eventuallyEq P (z := (t, x)) hx).self_of_nhds


end NavierStokes.PaperLocalization

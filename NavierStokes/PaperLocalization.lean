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



end NavierStokes.PaperLocalization

import NavierStokes.WholeDomainPhysicalCompact
import NavierStokes.ActualCycleResidualBounds
import NavierStokes.PhysicalStageBounds
import NavierStokes.AnnularEndpoint

noncomputable section

namespace NavierStokes.WholeDomainStageBounds

open Set Filter Function ProblemStatement
open scoped Topology ContDiff BigOperators

open PhysicalWaveSum

section BaseResidual

open CorrectionInitialization CorrectionInitialization.ActualPrimary ActualCycleResidualBounds

private abbrev baseResidual (B : ℕ) : VelocityField :=
  PhysicalResidualJetBounds.residual (FinalSlowBase.velocity certificate modulation upper B)
    (FinalSlowBase.pressure certificate modulation upper B)

private def exteriorDomain : Set SpaceTime :=
  {w | w ∈ preterminal ∧ physicalQ h w ≤ 1 ∧ w ∉ active}






end BaseResidual

section ResidualAssembly

open ActualCycleResidualBounds PhysicalResidualJetBounds CorrectionInitialization



end ResidualAssembly

end NavierStokes.WholeDomainStageBounds

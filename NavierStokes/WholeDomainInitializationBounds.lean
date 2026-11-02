import NavierStokes.WholeDomainPhysicalCompact
import NavierStokes.ActualCycleResidualBounds
import NavierStokes.PhysicalStageBounds
import NavierStokes.AnnularEndpoint
import NavierStokes.ActualCandidateAssembly
import NavierStokes.SharpPhysicalLogBounds


/-! Merged from `NavierStokes.WholeDomainActualStageBounds`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/

/-! Merged from `NavierStokes.WholeDomainStageBounds`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

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


end

section

noncomputable section

namespace NavierStokes.WholeDomainStageBounds

open Set Function Filter ProblemStatement CorrectionInitialization
open CorrectionInitialization.ActualPrimary ActualCandidateAssembly PhysicalWaveSum
open scoped Topology ContDiff BigOperators

/-- One common scale for every finite stage and every derivative order. -/
noncomputable def commonQ (B N0 : ℕ) : ℝ :=
  ChartScales.Q (ActualCandidateConstruction.residualBand B N0)




noncomputable abbrev finiteVelocity (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (J : ℕ) : VelocityField :=
  MixedDiagonalResidual.uncutVelocity (potentialStages B N0 hN) (directStages B N0 hN) J

noncomputable abbrev finitePressure (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (J : ℕ) : PressureField :=
  DiagonalJetBounds.uncutPrefix (pressureStages B N0 hN) (J+1)


end NavierStokes.WholeDomainStageBounds


end

noncomputable section

namespace NavierStokes.WholeDomainStageBounds

open Set Function Filter ProblemStatement PhysicalWaveSum SharpGluedStageBounds
open CorrectionInitialization.ActualPrimary ActualCandidateAssembly
open scoped Topology ContDiff BigOperators

private noncomputable abbrev seedT (B N0 : ℕ) :=
  ActualPhysicalStageBounds.actualInitialTemporalInput B N0 (ActualCandidateConstruction.firstBand B N0)
    (ActualCandidateConstruction.firstBand_four B N0)
private noncomputable abbrev seedR (B N0 : ℕ) :=
  ActualPhysicalStageBounds.actualInitialRankInput B N0 (ActualCandidateConstruction.firstBand B N0)
    (ActualCandidateConstruction.firstBand_four B N0)
private noncomputable abbrev seedB (B N0 : ℕ) :=
  ActualPhysicalStageBounds.actualInitialAngularInput B N0 (ActualCandidateConstruction.firstBand B N0)
    (ActualCandidateConstruction.firstBand_four B N0)
private noncomputable abbrev seedP (B N0 : ℕ) :=
  ActualPhysicalStageBounds.actualInitialPressureInput B N0 (ActualCandidateConstruction.firstBand B N0)
    (ActualCandidateConstruction.firstBand_four B N0)

noncomputable def seedPotentialLoss (B N0 : ℕ) : ℕ → ℝ :=
  InitializedPhysicalBackground.seedPotentialLoss h (InitialPhysicalData.potentialWaveData B N0).alpha
    (InitialPhysicalData.potentialWaveData B N0).shift (min (seedT B N0).alpha (seedR B N0).alpha)

noncomputable def seedDirectLoss (B N0 : ℕ) : ℕ → ℝ :=
  InitializedPhysicalBackground.seedDirectLoss h (seedB B N0).alpha

noncomputable def seedPressureLoss (B N0 : ℕ) : ℕ → ℝ :=
  ActualPhysicalStageBounds.initialPressureLoss h (InitialPhysicalData.pressureWaveData B N0).alpha
    (InitialPhysicalData.pressureWaveData B N0).shift (seedP B N0).alpha




noncomputable def initialVelocityLoss (B N0 : ℕ) (base : ℕ → ℝ) (m : ℕ) : ℝ :=
  max (base m) (max (seedPotentialLoss B N0 (m+1)) (seedDirectLoss B N0 m))

noncomputable def initialPressureTotalLoss (B N0 : ℕ) (base : ℕ → ℝ) (m : ℕ) : ℝ :=
  max (base m) (seedPressureLoss B N0 m)



end NavierStokes.WholeDomainStageBounds

import NavierStokes.WholeDomainStageBounds
import NavierStokes.ActualCandidateAssembly

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

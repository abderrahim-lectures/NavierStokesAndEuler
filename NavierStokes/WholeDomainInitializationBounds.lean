import NavierStokes.WholeDomainActualStageBounds
import NavierStokes.SharpPhysicalLogBounds

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

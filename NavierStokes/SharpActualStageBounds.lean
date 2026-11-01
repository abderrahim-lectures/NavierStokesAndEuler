import NavierStokes.SharpGluedStageBounds
import NavierStokes.ActualCandidateAssembly

noncomputable section

namespace NavierStokes.SharpActualStageBounds

open Set Function Filter ProblemStatement PhysicalWaveSum SharpGluedStageBounds
open CorrectionInitialization.ActualPrimary ActualCandidateAssembly
open scoped Topology ContDiff BigOperators




theorem direct_bound (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j m : ℕ) :
    LogBound h (ActualCandidateConstruction.qbig B N0) (directStages B N0 hN (j+1)) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) :=
  (direct_printed_bound (runData B N0 hN) (meanCycleInput B N0 hN)
    (ActualCandidateConstruction.firstBand_four B N0) le_rfl j m).congr
      outgoing.data.h_pos outgoing.data.h_lt_half ((representations B N0 hN).direct_succ j)


end NavierStokes.SharpActualStageBounds

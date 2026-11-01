import NavierStokes.WholeDomainBaseBounds
import NavierStokes.WholeDomainInitializationBounds
import NavierStokes.WholeDomainPrefixBounds
import NavierStokes.SharpParticularStageBounds

noncomputable section

namespace NavierStokes.WholeDomainStageBounds

open Set Function Filter ProblemStatement PhysicalWaveSum SharpGluedStageBounds
open CorrectionInitialization.ActualPrimary ActualCandidateAssembly
open scoped Topology ContDiff BigOperators

/-- One derivative loss controls both finite fields. It contains no
finite-stage index and is chosen on the original fixed construction. -/
noncomputable def finiteLoss (B N0 : ℕ) (m : ℕ) : ℝ :=
  max
    (prefixLoss (initialVelocityLoss B N0 ActualBaseVelocityBounds.heatLoss)
      (SharpPhysicalCarrier.physicalLoss h) m)
    (prefixLoss (initialPressureTotalLoss B N0 ActualBasePressureBounds.pressureLoss)
      (SharpPhysicalCarrier.physicalLoss h) m)







noncomputable def paperLoss (B N0 : ℕ) (m : ℕ) : ℝ :=
  max (finiteLoss B N0 m) (ActualCycleResidualBounds.fixedLoss m)


/-- A stage-independent loss for all derivatives through the specified order. -/
noncomputable def paperJetLoss (B N0 : ℕ) (m : ℕ) : ℝ :=
  ∑ k : Fin (m+1), |paperLoss B N0 k.val|






end NavierStokes.WholeDomainStageBounds

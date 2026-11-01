import NavierStokes.SharpLogWeights

noncomputable section
namespace NavierStokes.SharpPhysicalLoss
open Set Function
open ProblemStatement PhysicalGraphBounds SharpPhysicalPhase SharpPhysicalCarrier
open scoped ContDiff

private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top




end NavierStokes.SharpPhysicalLoss

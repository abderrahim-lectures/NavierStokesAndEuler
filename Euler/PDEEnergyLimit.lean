import Euler.WeightedSobolevEnergy
import Euler.TimeLpPairing
import Euler.SobolevEnergyPaths

/-! The actual finite-Sobolev viscous PDE energy estimate passes to strong limits without a time derivative of a zero norm. -/

noncomputable section

namespace EulerPDEEnergyLimit

open MeasureTheory Set Real InnerProductSpace EulerLiftedGradientSpace EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerCylinderSobolevSpace EulerMetricHeatEnergy EulerFiniteMetricEnergy
  EulerWeightedSobolevEnergy EulerWeightedCylinderEnergy EulerSobolevMetricTransport
  EulerVolterraConvolution EulerTimeLp EulerTimeLpPairing EulerPacketWeights
open scoped Topology


variable (period : ℝ) [Fact (0 < period)]


end EulerPDEEnergyLimit

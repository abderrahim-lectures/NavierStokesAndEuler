import Euler.PacketPrimaryFactorization
import Euler.PacketPrimaryShearIdentity

/-! Exact rank-one primary shear throughout the joined history and forward
interval, obtained from the proved factorization of the actual primary. -/

noncomputable section

namespace EulerPacketPrimaryShear

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerGraphPullback EulerPacketNormalizedPrimary
  EulerTransversePacketProvider EulerPacketTerminalDatum EulerTransversePacketPrimary
  EulerSpatialCutoffs EulerPeriodicProfile EulerPacketPrimaryFactorization
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)

def fullWave (α k : ℝ) (t : Icc (0 : ℝ) D.T) (y : Space) : Space :=
  (α/k) • vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(y,k*⟪D.m₀,y⟫_ℝ))








end EulerPacketPrimaryShear

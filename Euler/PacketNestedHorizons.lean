import Euler.PacketBaseGuardScales
import Euler.PacketSourceScaleGuards

/-! The literal activation times and nested horizons in (38). The same
positive initial time interval is available to every finite packet state. -/

noncomputable section

namespace EulerPacketNestedHorizons

open Finset Real EulerScale EulerPacketScaleGeometry EulerPacketSourceScales
  EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerPacketSourceScaleGuards EulerPacketBaseGuardScales

def stepLength (J : ℕ) (X : ℝ) (a β : ℕ → ℝ) (n : ℕ) : ℝ :=
  scaleSequence J X (n+1)/sqrt (β n*a n*previousShear J X n)

def activationTime (J : ℕ) (X : ℝ) (a β : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, stepLength J X a β i

def horizonTime (J : ℕ) (X : ℝ) (a β : ℕ → ℝ) (n : ℕ) : ℝ :=
  activationTime J X a β n+2*timeWidth J X n

@[simp] theorem activationTime_zero (J : ℕ) (X : ℝ) (a β : ℕ → ℝ) :
    activationTime J X a β 0=0 := by simp [activationTime]


@[simp] theorem horizonTime_zero (J : ℕ) {X : ℝ} (hX : 0 < X) (a β : ℕ → ℝ) :
    horizonTime J X a β 0=baseHorizon J X := by
  rw [horizonTime,activationTime_zero,zero_add,baseHorizon_eq_timeWidth J hX]

variable (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 < X) (a β : ℕ → ℝ)
  (ha : ∀ n, 1/2 ≤ a n) (ha₂ : ∀ n, a n ≤ 2)
  (hβ : ∀ n, 1/2 ≤ β n*scaleSequence J X n^2)
  (hβ₂ : ∀ n, β n*scaleSequence J X n^2 ≤ 2)















end EulerPacketNestedHorizons

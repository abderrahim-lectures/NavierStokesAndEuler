import NavierStokes.SharpLogWeights

noncomputable section
namespace NavierStokes.SharpPhysicalLoss
open Set Function
open ProblemStatement PhysicalGraphBounds SharpPhysicalPhase SharpPhysicalCarrier
open scoped ContDiff

private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

/-- Physical rescaling and any derivative order up to the recovery order
fit the exact loss printed in the manuscript. -/
theorem rescale_with_common_loss {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h σ g e C : ℝ} (hh : 0 ≤ h) (hσ : -(2*CoordinateAlgebra.A h) ≤ σ) (hC : 0 ≤ C)
    (n m k : ℕ) (hkm : k ≤ m+1) {f : SpaceTime → E} {w : SpaceTime}
    (hf : ContDiffAt ℝ ∞ f w)
    (hb : ‖iteratedFDeriv ℝ k f w‖ ≤ C*ChartScales.Q n^(g-(k:ℝ)*derivativeCost h)*ChartScales.S n^e) :
    ‖iteratedFDeriv ℝ k (fun z => ChartScales.Q n^σ • f z) w‖ ≤
      C*ChartScales.Q n^(g-physicalLoss h m)*ChartScales.S n^e := by
  have hQ := ChartScales.Q_pos n
  have hS : 0 ≤ ChartScales.S n := sq_nonneg (n:ℝ)
  have hcost : 0 ≤ derivativeCost h := by unfold derivativeCost; linarith
  have hk : (k:ℝ) ≤ (m:ℝ)+1 := by exact_mod_cast hkm
  have hexp : g-physicalLoss h m ≤ σ+(g-(k:ℝ)*derivativeCost h) := by
    unfold physicalLoss
    nlinarith
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le (nat_le_infty k)), norm_smul,
    Real.norm_of_nonneg (Real.rpow_nonneg hQ.le _)]
  calc
    _ ≤ ChartScales.Q n^σ * (C*ChartScales.Q n^(g-(k:ℝ)*derivativeCost h)*ChartScales.S n^e) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hQ.le _)
    _ = C*ChartScales.Q n^(σ+(g-(k:ℝ)*derivativeCost h))*ChartScales.S n^e := by
      rw [Real.rpow_add hQ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hQ (ChartScales.Q_le_one n) hexp) hC)
      (Real.rpow_nonneg hS _)



end NavierStokes.SharpPhysicalLoss

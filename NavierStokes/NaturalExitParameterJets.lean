import NavierStokes.TransitionRamp
import NavierStokes.SharpPhaseJetAlgebra

noncomputable section

namespace NavierStokes.NaturalExitParameterJets

open Set NaturalProfile NaturalAxisCoefficients NaturalAxisBridge NaturalEntrance ReferencePath
open scoped ContDiff Topology

variable {h j σ : ℝ} {P0 : ℝ → ℝ} (d : AnalyticInputs h j σ P0)

def phi {Λ C : ℝ} (E : CoefficientProfile d Λ C) (Y η : ℝ) : ℝ :=
  AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1 (Y, η)

def u {Λ C : ℝ} (E : CoefficientProfile d Λ C) (Y η : ℝ) : ℝ :=
  AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.2 (Y, η)

def phiY {Λ C : ℝ} (E : CoefficientProfile d Λ C) (Y η : ℝ) : ℝ :=
  AxisEvaluation.mixedSeries window d.coefficients.epsilon E.coefficients.1 1 0 (Y, η)

def uY {Λ C : ℝ} (E : CoefficientProfile d Λ C) (Y η : ℝ) : ℝ :=
  AxisEvaluation.mixedSeries window d.coefficients.epsilon E.coefficients.2 1 0 (Y, η)

def scaledP1 {Λ C : ℝ} (E : CoefficientProfile d Λ C) (Y η : ℝ) : ℝ :=
  -2 * Y * (phiY d E Y η * (phi d E Y η)⁻¹)

def scaledNs {Λ C : ℝ} (E : CoefficientProfile d Λ C) (Y η : ℝ) : ℝ :=
  -2 * uY d E Y η

theorem radial_mem {Y : ℝ} (hY : Y ∈ Icc (0 : ℝ) (41 / 10)) :
    Y ∈ Ioo (-20 : ℝ) 20 := by constructor <;> linarith [hY.1, hY.2]


theorem mixed_smooth (A : AxisCoefficientSpace.AxisSpace window d.coefficients.epsilon)
    (k : ℕ) {Y : ℝ} (hY : Y ∈ Icc (0 : ℝ) (41 / 10)) :
    ContDiffOn ℝ ∞ (fun η => AxisEvaluation.mixedSeries window d.coefficients.epsilon A k 0 (Y, η))
      parameterInterval := by
  intro η hη
  have hp : (Y, η) ∈ AxisEvaluation.strip window 20 := ⟨radial_mem hY, hη⟩
  exact ((AxisEvaluation.mixedSeries_smooth window d.coefficients.epsilon_pos A k 0
    hp).comp η (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

theorem phi_smooth {Λ C : ℝ} (E : CoefficientProfile d Λ C) {Y : ℝ}
    (hY : Y ∈ Icc (0 : ℝ) (41 / 10)) : ContDiffOn ℝ ∞ (phi d E Y) parameterInterval := by
  change ContDiffOn ℝ ∞ (fun η => AxisEvaluation.profile window d.coefficients.epsilon
    E.coefficients.1 (Y, η)) parameterInterval
  simpa only [AxisEvaluation.mixedSeries_zero] using mixed_smooth d E.coefficients.1 0 hY

theorem phi_lower (hσ : 0 < σ) {Λ C : ℝ}
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    (E : CoefficientProfile d Λ C) {Y : ℝ} (hY : Y ∈ Icc (0 : ℝ) (41 / 10))
    {η : ℝ} (hη : η ∈ parameterInterval) : 1 / 8 < phi d E Y η :=
  coefficient_phi_lower d.coefficients hσ (profileErrorConstant_nonneg d) hscale
    E.coefficients E.norm_error hY.1 hY.2 hη



theorem inverse_smooth : ContDiffOn ℝ ∞ (fun x : ℝ => x⁻¹) (Ioi (0 : ℝ)) :=
  contDiffOn_id.inv (fun _ hx => ne_of_gt hx)






end NavierStokes.NaturalExitParameterJets

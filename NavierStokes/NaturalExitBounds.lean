import NavierStokes.TransitionRamp
import NavierStokes.SharpPhaseJetAlgebra


/-! Merged from `NavierStokes.NaturalExitParameterJets`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

noncomputable section

namespace NavierStokes.NaturalExitParameterJets

open Set NaturalProfile NaturalAxisCoefficients NaturalAxisBridge NaturalEntrance ReferencePath
open scoped ContDiff Topology

variable {h j σ : ℝ} {P0 : ℝ → ℝ} (d : AnalyticInputs h j σ P0)

def phi {Λ C : ℝ} (E : CoefficientProfile d Λ C) (Y η : ℝ) : ℝ :=
  AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1 (Y, η)

def u {Λ C : ℝ} (E : CoefficientProfile d Λ C) (Y η : ℝ) : ℝ :=
  AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.2 (Y, η)


def uY {Λ C : ℝ} (E : CoefficientProfile d Λ C) (Y η : ℝ) : ℝ :=
  AxisEvaluation.mixedSeries window d.coefficients.epsilon E.coefficients.2 1 0 (Y, η)



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


end

noncomputable section

namespace NavierStokes.NaturalExitBounds

open Set NaturalProfile NaturalAxisCoefficients NaturalAxisBridge NaturalEntrance
open scoped ContDiff Topology


variable {h j σ : ℝ} {P0 : ℝ → ℝ} (d : AnalyticInputs h j σ P0)

def lowerConstant : ℝ := 5 / (32 * profileBound d.coefficients)



/-- The complete quantitative natural-exit conclusions, with the parameter
jet constants kept outside the choices of scale and normalization. -/
structure Estimates {Λ C : ℝ} (E : EntranceProfile d Λ C) (B : ℕ → ℝ) : Prop where
  phi_lower : ∀ Y ∈ Icc (0 : ℝ) (41 / 10), ∀ η ∈ Icc (-1 : ℝ) 1,
    1 / 8 < E.profile.family.phi (Y, η)
  source_lower : ∀ p, rescalePoint Λ p ∈ entranceSet →
    (19 / 20 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 + 5 / 2 <
      Sq h E.profile.family.f E.profile.family.U E.profile.family.Ubar p
  p1_lower : ∀ X η, 0 < X → Λ * X ≤ 41 / 10 → η ∈ Icc (-1 : ℝ) 1 →
    lowerConstant d ≤ p1 E.profile.family.f (X, η) / X
  p1_positive_upper : ∀ X η, 0 < X → Λ * X ≤ 41 / 10 → η ∈ Icc (-1 : ℝ) 1 →
    0 < p1 E.profile.family.f (X, η) ∧ p1 E.profile.family.f (X, η) ≤ B 0
  ns_error : ∀ p, rescalePoint Λ p ∈ entranceSet →
    |ns E.profile.family.U p - NaturalAxisData.Z h j P0 p.2 / NaturalAxisData.L h p.2| ≤
      AxisEvaluation.jetBound d.coefficients.epsilon 5 1 0 * profileErrorConstant d / Λ
  cone_margin : ∀ η ∈ Icc (-1 : ℝ) 1,
    2 + 1 / 4 < coneSize E.profile.family.f E.profile.family.U (4 / Λ, η)
  parameter_jets : ∀ m X, Λ * X ∈ Icc (0 : ℝ) (41 / 10) → ∀ η ∈ Icc (-1 : ℝ) 1,
    |iteratedDeriv m (fun ξ => E.profile.family.phi (Λ * X, ξ)) η| ≤ B m ∧
    |iteratedDeriv m (fun ξ => Real.log (E.profile.family.phi (Λ * X, ξ))) η| ≤ B m ∧
    |iteratedDeriv m (fun ξ => E.profile.family.u (Λ * X, ξ)) η| ≤ B m ∧
    |iteratedDeriv m (fun ξ => p1 E.profile.family.f (X, ξ)) η| ≤ B m ∧
    |iteratedDeriv m (fun ξ => ns E.profile.family.U (X, ξ)) η| ≤ B m


/-- The bounds in the paper's original regular-integral coordinates. -/
theorem Estimates.regular_lag_bounds {Λ C : ℝ} {E : EntranceProfile d Λ C} {B : ℕ → ℝ}
    (H : Estimates d E B) (hsmall : NaturalAxisRange.Parameters h j) (hΛ : 0 < Λ)
    {X η : ℝ} (hX : 0 < X) (hY : X ≤ (41 / 10) / Λ) (hη : η ∈ Icc (-1 : ℝ) 1) :
    let Q := regularAngularLag h E.profile.family.f E.profile.family.U E.profile.family.Ubar (X, η)
    let N := regularAxialLag h E.profile.family.U E.profile.family.Ubar E.profile.family.Pi (X, η)
    lowerConstant d ≤ (X * Q / NaturalAxisData.L h η) / X ∧
    0 < X * Q / NaturalAxisData.L h η ∧ X * Q / NaturalAxisData.L h η ≤ B 0 ∧
    |N / NaturalAxisData.L h η - NaturalAxisData.Z h j P0 η / NaturalAxisData.L h η| ≤
      AxisEvaluation.jetBound d.coefficients.epsilon 5 1 0 * profileErrorConstant d / Λ := by
  dsimp only
  have hYX : Λ * X ≤ 41 / 10 := by
    simpa only [mul_comm] using (le_div_iff₀ hΛ).mp hY
  have hp : rescalePoint Λ (X, η) ∈ entranceSet :=
    ⟨⟨mul_nonneg hΛ.le hX.le, hYX⟩, hη⟩
  have he := (E.regular_lag_coordinates hsmall hΛ hp hX).1
  have hn : ns E.profile.family.U (X, η) =
      regularAxialLag h E.profile.family.U E.profile.family.Ubar E.profile.family.Pi (X, η) /
        NaturalAxisData.L h η := ns_eq_scaled_regularAxialLag E.profile.family.natural hΛ
      (entrance_mem_strip hp) hX.ne' (NaturalAxisRange.L_pos hsmall hη).ne'
  change p1 E.profile.family.f (X, η) = X * regularAngularLag h E.profile.family.f
    E.profile.family.U E.profile.family.Ubar (X, η) / NaturalAxisData.L h η at he
  rw [← he, ← hn]
  exact ⟨H.p1_lower X η hX hYX hη, (H.p1_positive_upper X η hX hYX hη).1,
    (H.p1_positive_upper X η hX hYX hη).2, H.ns_error (X, η) hp⟩


end NavierStokes.NaturalExitBounds

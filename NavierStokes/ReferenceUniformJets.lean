import NavierStokes.TransitionRamp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Uniform parameter jets of the actual reference continuation -/

noncomputable section

namespace NavierStokes.ReferenceUniformJets

open Set Filter MeasureTheory ProfileHistories ReferencePath
open scoped Topology ContDiff

abbrev etaJet := TransitionRamp.parameterJet

theorem etaJet_smooth (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) (n : ℕ) :
    ContDiffOn ℝ ∞ (etaJet n F) D.carrier := by
  induction n with
  | zero => exact hF
  | succ n ih => exact parameterPartial_smooth D ih

theorem etaJet_eq_iteratedDeriv (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) (n : ℕ) {p : Point} (hp : p ∈ D.carrier) :
    etaJet n F p = iteratedDeriv n (fun η => F (p.1, η)) p.2 := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have he : (fun η => etaJet n F (p.1, η)) =ᶠ[𝓝 p.2]
        iteratedDeriv n (fun η => F (p.1, η)) := by
      filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually
        (D.isOpen.mem_nhds hp)] with η hη
      exact ih hη
    change parameterPartial (etaJet n F) p = _
    rw [iteratedDeriv_succ]
    exact (parameterPartial_hasDerivAt D (etaJet_smooth D hF n) hp).deriv.symm.trans he.deriv_eq













section NaturalReference

open NaturalProfile NaturalAxisCoefficients TransitionRamp

variable {h j σ Λ : ℝ} {P0 : ℝ → ℝ} (d : AnalyticInputs h j σ P0)




noncomputable def normalizedReferenceLog {C : ℝ}
    (E : NaturalEntrance.CoefficientProfile d Λ C) (hΛ : 0 < Λ) (δ X η : ℝ) : ℝ :=
  Real.log C + Real.log ((Input.ofNatural hΛ E.family).refF δ (X, η))







end NaturalReference

end NavierStokes.ReferenceUniformJets

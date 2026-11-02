import NavierStokes.GenericTupleSupport
import NavierStokes.GenericSolenoidalRealization


/-! Merged from `NavierStokes.GenericAngularRecovery`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

noncomputable section

namespace NavierStokes.GenericSolenoidalRealization

open Set Filter ProblemStatement AxisymmetricFields DirectAngularDiagonal
open scoped Topology ContDiff BigOperators

private def radialFactor (w : SpaceTime) (p : ProfilePoint) : ℝ :=
  Real.sqrt (p.2.1 / radialEnergy w.2)

/-- A local section of the cylindrical coordinate map through the given
off-axis Cartesian point, retaining its angular direction. -/
private def radialSection (w : SpaceTime) (p : ProfilePoint) : SpaceTime :=
  (p.1, AxisymmetricResidual.pack (radialFactor w p * w.2 0)
    (radialFactor w p * w.2 1) p.2.2)











end NavierStokes.GenericSolenoidalRealization


end

noncomputable section

namespace NavierStokes.GenericTupleRealization

open Set Filter ProblemStatement GenericDifferentialPolynomial DiagonalResidual
open GenericRealizationBounds GenericRealization
open scoped Topology ContDiff BigOperators



/-- Full residual conclusion of `sum:realization`, including logarithmic
coefficient growth only on common factor supports and an arbitrary flat
finite-stage error. The realization and schedule are those of
`GenericTupleRealization.exists_realization`; no residual or support property
of the unknown infinite sum is an assumption. -/
theorem Result.flat_residual_of_raw_bounds {κ : Type*} {U : Set SpaceTime} {q : SpaceTime → ℝ}
    {u0 : VelocityField} {s0 : κ → PressureField} {A B : ℕ → VelocityField}
    {R : κ → ℕ → PressureField} {g L : ℕ → ℝ} {a : ℕ → ℕ}
    (H : Result U q u0 s0 A B R g L a) (hU : IsOpen U)
    (hqs : ContDiffOn ℝ ∞ q U) (hq : ∀ w ∈ U, 0 < q w ∧ q w ≤ 1)
    (hu0 : ContDiffOn ℝ ∞ u0 U) (hs0 : ∀ k, ContDiffOn ℝ ∞ (s0 k) U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (hR : ∀ k j, 1 ≤ j → ContDiffOn ℝ ∞ (R k j) U)
    (hgtop : Tendsto g atTop atTop) (P : SupportedPolynomial SpaceTime (Fin 3 ⊕ κ))
    (hconst : ContDiffOn ℝ ∞ P.constant U) (hc : ∀ t ∈ P.terms, ContDiffOn ℝ ∞ t.1 U)
    (region : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → Set SpaceTime)
    (Cc Pc Kc : ℕ → ℝ)
    (hcoeff : ∀ t ∈ P.terms, ∀ m x, x ∈ U → x ∈ region t →
      ‖iteratedFDeriv ℝ m t.1 x‖ ≤ Cc m * (1 + |Real.log (q x)|) ^ Pc m * q x ^ (-Kc m))
    (hrawsupport : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      FactorSupportAt (baseComponents u0 s0) (incrementComponents A B R) x t.2)
    (hcutsupport : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      FactorSupportAt (baseComponents u0 s0) (cutIncrementComponents (fun j => (a j : ℝ)) q A B R) x t.2)
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop atTop) (Cr Pr : ℕ → ℕ → ℝ) (Kr : ℕ → ℝ)
    (error : ℕ → ℕ → SpaceTime → ℝ)
    (hres : ∀ J m x, x ∈ U →
      ‖iteratedFDeriv ℝ m (P.eval (stageComponents u0 s0 A B R J)) x‖ ≤
        Cr J m * (1 + |Real.log (q x)|) ^ Pr J m * q x ^ (rho J - Kr m) + error J m x)
    (he : ∀ J m N, ∃ Ce : ℝ, 0 ≤ Ce ∧ ∀ x ∈ U, error J m x ≤ Ce * q x ^ (N : ℕ))
    (m : ℕ) (N : ℝ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ x ∈ U, 0 < q x → q x < δ →
      ‖iteratedFDeriv ℝ m (P.eval (components (fun j => (a j : ℝ)) q u0 s0 A B R)) x‖ ≤ C * q x ^ N := by
  have hlU := eventually_domain U q
  have hlq := hlU.mono fun w hw => hq w hw
  have hqzero := scale_tendsto U q
  have hcoeffRate : ∀ t ∈ P.terms, ∀ m,
      JetRate (scaleApproach U q ⊓ 𝓟 (region t)) q t.1 m (-(Kc m + 1)) := by
    intro t ht m
    have hregion : ∀ᶠ x in scaleApproach U q ⊓ 𝓟 (region t), x ∈ region t :=
      Filter.Eventually.filter_mono inf_le_right (by simp)
    have hb : ∀ᶠ x in scaleApproach U q ⊓ 𝓟 (region t),
        ‖iteratedFDeriv ℝ m t.1 x‖ ≤ Cc m * (1 + |Real.log (q x)|) ^ Pc m * q x ^ (-Kc m) := by
      filter_upwards [hlU.filter_mono inf_le_left, hregion] with x hx hr
      exact hcoeff t ht m x hx hr
    convert jetRate_of_log_bound ((hlq.filter_mono inf_le_left).mono fun _ hx => hx.1)
      (hqzero.mono_left inf_le_left) m (Cc m) (Pc m) (-Kc m) hb using 1
    ring
  have hresRate : ∀ J k, JetRate (scaleApproach U q) q
      (P.eval (stageComponents u0 s0 A B R J)) k (rho J - (Kr k + 1)) := by
    intro J k
    have herr : ∀ M : ℕ, ∃ Ce : ℝ, 0 ≤ Ce ∧
        ∀ᶠ x in scaleApproach U q, error J k x ≤ Ce * q x ^ M := by
      intro M
      obtain ⟨Ce, hCe, hb⟩ := he J k M
      exact ⟨Ce, hCe, hlU.mono fun x hx => hb x hx⟩
    convert jetRate_of_log_bound_add_flat hlq hqzero k (Cr J k) (Pr J k)
      (rho J - Kr k) (hlU.mono fun x hx => hres J k x hx) herr using 1
    ring
  exact H.flat_residual_of_factor_support hU hqs hq hu0 hs0 hA hB hR hgtop P hconst hc
    region (fun _ m => Kc m + 1) hcoeffRate hrawsupport hcutsupport rho hrho
    (fun m => Kr m + 1) hresRate m N

end NavierStokes.GenericTupleRealization

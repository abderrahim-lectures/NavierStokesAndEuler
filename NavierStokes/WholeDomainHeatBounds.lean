import NavierStokes.WholeDomainHeatGeometry

/-! # Whole-domain jet bounds for the actual exterior heat fields

The parabolic normalization uses the larger of the similarity scale and
physical radial energy. Its image lies in one compact annulus, even when
the original radial coordinate is unbounded.
-/

/-! Merged from `NavierStokes.WholeDomainHeatCompact`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Uniform heat jets on the normalized compact annulus -/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.WholeDomainHeatBounds

open ProblemStatement PhysicalWaveSum WholeDomainStageBounds

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def positiveRadius : Set SpaceTime := {w | 0 < AxisymmetricFields.radialEnergy w.2}

theorem positiveRadius_open : IsOpen positiveRadius :=
  isOpen_lt continuous_const
    ((AxisymmetricFields.contDiff_radialEnergy (n := ∞)).continuous.comp continuous_snd)

theorem closedHeat_mem_nhds {w : SpaceTime} (ht : w.1 < 1)
    (hs : 0 < AxisymmetricFields.radialEnergy w.2) :
    BaseExterior.closedCartesianHeatDomain ∈ 𝓝 w := by
  have hU : IsOpen {y : SpaceTime | y.1 < 1 ∧ 0 < AxisymmetricFields.radialEnergy y.2} :=
    (isOpen_lt continuous_fst continuous_const).inter positiveRadius_open
  exact Filter.mem_of_superset (hU.mem_nhds ⟨ht,hs⟩) (fun _ hy => ⟨hy.1.le,hy.2⟩)

theorem heat_smoothAt {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f BaseExterior.closedCartesianHeatDomain)
    {w : SpaceTime} (ht : w.1 < 1) (hs : 0 < AxisymmetricFields.radialEnergy w.2) :
    ContDiffAt ℝ ∞ f w := hf.contDiffAt (closedHeat_mem_nhds ht hs)

variable [CompleteSpace V]

theorem normalized_local_rate {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f BaseExterior.closedCartesianHeatDomain)
    {R : ℝ} (hR : 0 < R) (m : ℕ) {w : SpaceTime} (hw : w ∈ normalizedAnnulus R) :
    DiagonalResidual.JetRate (𝓝[normalizedAnnulus R ∩ preterminal] w)
      (fun _ => (1 : ℝ)) f m 0 := by
  have hs : 0 < AxisymmetricFields.radialEnergy w.2 := hR.trans_le hw.2.2.1
  by_cases ht : w.1 < 1
  · have hc : ContDiffAt ℝ 0 (iteratedFDeriv ℝ m f) w :=
      (heat_smoothAt hf ht hs).iteratedFDeriv_right
        (by exact_mod_cast (le_top : 0 + (m : ℕ∞) ≤ ⊤))
    exact rate_of_jet_limit (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      tendsto_const_nhds zero_lt_one 0
  · have ht1 : w.1 = 1 := le_antisymm hw.1.2 (le_of_not_gt ht)
    obtain ⟨U⟩ := SlowBaseEndpoint.oneSidedExtension_of_closed_local
      (f := f) (g := f) positiveRadius_open
      (show (1,w.2) ∈ positiveRadius by simpa [positiveRadius] using hs)
      (hf.mono (fun y hy => ⟨hy.2.1,hy.1⟩)) (fun _ _ => rfl)
    have hmono : 𝓝[normalizedAnnulus R ∩ preterminal] (1,w.2) ≤
        𝓝[SpacetimeEndpoint.openPast 1] (1,w.2) :=
      nhdsWithin_mono _ (fun _ hy => ⟨hy.2,mem_univ _⟩)
    have hew : w = (1,w.2) := Prod.ext ht1 rfl
    rw [hew]
    exact rate_of_jet_limit ((U.jet_tendsto m).mono_left hmono)
      tendsto_const_nhds zero_lt_one 0

theorem normalized_jet_bound {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f BaseExterior.closedCartesianHeatDomain)
    {R : ℝ} (hR : 0 < R) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ normalizedAnnulus R, w.1 < 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := compact_bound_of_local_rates
    (S := normalizedAnnulus R ∩ preterminal) (normalizedAnnulus_compact R)
    (fun _ _ => zero_lt_one) (fun _ hw => normalized_local_rate hf hR m hw)
  refine ⟨C,hC,fun w hw ht => ?_⟩
  simpa only [Real.rpow_zero,mul_one] using hb w ⟨hw,hw,ht⟩

end NavierStokes.WholeDomainHeatBounds


end


/-! Merged from `NavierStokes.WholeDomainHeatScaling`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Exact scaling identities for the physical heat velocity and pressure -/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.WholeDomainHeatBounds

open ProblemStatement PhysicalWaveSum


theorem rescale_heat_ratio (a : ℝ) (ha : 0 < a) (z : ℝ) {w : SpaceTime}
    (hs : 0 < AxisymmetricFields.radialEnergy w.2) :
    (1-(rescale a ha z w).1) / AxisymmetricFields.radialEnergy (rescale a ha z w).2 =
      (1-w.1) / AxisymmetricFields.radialEnergy w.2 := by
  rw [rescale_time, rescale_radialEnergy]
  field_simp
  ring



theorem heatPressure_rescale (C h a : ℝ) (ha : 0 < a) (z : ℝ) {w : SpaceTime}
    (hs : 0 < AxisymmetricFields.radialEnergy w.2) :
    BaseExterior.heatPressureField C h w =
      a ^ (-2*TerminalPressure.amplitudeExponent h) *
        BaseExterior.heatPressureField C h (rescale a ha z w) := by
  change BaseExterior.heatPressure C h (AxisymmetricFields.profilePoint w.1 w.2) =
    a ^ (-2*TerminalPressure.amplitudeExponent h) *
      BaseExterior.heatPressure C h (AxisymmetricFields.profilePoint
        (rescale a ha z w).1 (rescale a ha z w).2)
  rw [BaseExterior.heatPressure_formula C h hs,
    BaseExterior.heatPressure_formula C h (by
      change 0 < AxisymmetricFields.radialEnergy (rescale a ha z w).2
      rw [rescale_radialEnergy]; exact div_pos hs ha)]
  dsimp only [AxisymmetricFields.profilePoint]
  rw [rescale_heat_ratio a ha z hs, rescale_radialEnergy, Real.div_rpow hs.le ha.le]
  have hp : a ^ (-2*TerminalPressure.amplitudeExponent h) ≠ 0 :=
    (Real.rpow_pos_of_pos ha _).ne'
  field_simp

end NavierStokes.WholeDomainHeatBounds


end


noncomputable section

open Set Filter Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.WholeDomainHeatBounds

open ProblemStatement PhysicalWaveSum

def heatLoss (m : ℕ) : ℝ := 2*((m : ℝ)+1)

theorem heatLoss_nonneg (m : ℕ) : 0 ≤ heatLoss m := by unfold heatLoss; positivity

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem homogeneous_heat_bound {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f BaseExterior.closedCartesianHeatDomain)
    {b : ℝ} (hb : -2 ≤ b ∧ b ≤ 0)
    (hscale : ∀ (a : ℝ) (ha : 0 < a) (z : ℝ) (w : SpaceTime),
      0 < AxisymmetricFields.radialEnergy w.2 →
        f w = a ^ b • f (rescale a ha z w))
    {h R : ℝ} (hh : 0 < h) (hh1 : h < 1/2) (hR : 0 < R) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ preterminal, physicalQ h w ≤ 1 →
      R < (SlowBorelBase.cartesianChart h w).2.1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * physicalQ h w ^ (-heatLoss m) := by
  obtain ⟨C,hC,hCb⟩ := normalized_jet_bound hf (lt_min hR zero_lt_one) m
  refine ⟨C,hC,?_⟩
  intro w hw hq1 hX
  let q := physicalQ h w
  have hq : 0 < q := physicalQ_pos hh hh1 hw
  let a := max q (AxisymmetricFields.radialEnergy w.2)
  have ha : 0 < a := hq.trans_le (le_max_left _ _)
  have hqa : q ≤ a := le_max_left _ _
  have hs : 0 < AxisymmetricFields.radialEnergy w.2 := by
    change R < AxisymmetricFields.radialEnergy w.2 / q at hX
    exact (mul_pos hR hq).trans ((lt_div_iff₀ hq).mp hX)
  have hT := normalize_mem_annulus hh hh1 hR hw hX
  change rescale a ha (w.2 2) w ∈ normalizedAnnulus (min R 1) at hT
  have htp := rescale_past a ha (w.2 2) hw
  have hts : 0 < AxisymmetricFields.radialEnergy (rescale a ha (w.2 2) w).2 := by
    rw [rescale_radialEnergy]
    exact div_pos hs ha
  have hcomp : ContDiffAt ℝ ∞ (fun y => f (rescale a ha (w.2 2) y)) w :=
    (heat_smoothAt hf htp hts).comp w
      (((parabolicLinear a ha).contDiff.contDiffAt).add contDiffAt_const)
  have he : f =ᶠ[𝓝 w] (fun y => a^b • f (rescale a ha (w.2 2) y)) :=
    Filter.eventuallyEq_of_mem (positiveRadius_open.mem_nhds hs)
      (fun y hy => hscale a ha (w.2 2) y hy)
  rw [iteratedFDeriv_eq_of_eventuallyEq he m,
    iteratedFDeriv_const_smul_apply' (hcomp.of_le (nat_le_infty m)), norm_smul,
    Real.norm_of_nonneg (Real.rpow_nonneg ha.le b)]
  have hL := parabolicLinear_norm_le ha hq hqa hq1
  have hj : ‖iteratedFDeriv ℝ m (fun y => f (rescale a ha (w.2 2) y)) w‖ ≤
      C * (q⁻¹)^m := by
    exact (norm_iteratedFDeriv_affine_le (parabolicLinear a ha) (rescaleOffset a (w.2 2))
      f w m).trans (mul_le_mul (hCb _ hT htp)
        (pow_le_pow_left₀ (norm_nonneg _) hL m) (pow_nonneg (norm_nonneg _) m) hC)
  have hab : a^b ≤ q^b := Real.rpow_le_rpow_of_nonpos hq hqa hb.2
  calc
    a^b * ‖iteratedFDeriv ℝ m (fun y => f (rescale a ha (w.2 2) y)) w‖ ≤
        q^b * (C*(q⁻¹)^m) :=
      mul_le_mul hab hj (norm_nonneg _) (Real.rpow_nonneg hq.le b)
    _ = C*q^(b-(m : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_mul_natCast hq.le]
      rw [show (-1 : ℝ)*(m : ℝ) = -(m : ℝ) by ring]
      rw [show q^b * (C*q^(-(m : ℝ))) = C*(q^b*q^(-(m : ℝ))) by ring,
        ← Real.rpow_add hq]
      congr 2
    _ ≤ C*q^(-heatLoss m) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hq hq1 (by
        unfold heatLoss
        have hm : 0 ≤ (m : ℝ) := by positivity
        linarith [hb.1])) hC


/-- The canonical improper-integral pressure satisfies the same global
fixed-order bound; no bound on the radial coordinate is imposed. -/
theorem heat_pressure_bound (C : ℝ) {h R : ℝ}
    (hh : 0 < h) (hh1 : h < 1/2) (hR : 0 < R) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w ∈ preterminal, physicalQ h w ≤ 1 →
      R < (SlowBorelBase.cartesianChart h w).2.1 →
      ‖iteratedFDeriv ℝ m (BaseExterior.heatPressureField C h) w‖ ≤
        K * physicalQ h w ^ (-heatLoss m) := by
  exact homogeneous_heat_bound (BaseExterior.heatPressureField_contDiffOn_closed C hh)
    (by unfold TerminalPressure.amplitudeExponent; constructor <;> linarith)
    (fun a ha z _ hs => heatPressure_rescale C h a ha z hs) hh hh1 hR m

end NavierStokes.WholeDomainHeatBounds

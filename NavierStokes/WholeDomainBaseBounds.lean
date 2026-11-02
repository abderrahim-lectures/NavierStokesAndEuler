import NavierStokes.WholeDomainPhysicalCompact
import NavierStokes.SlowBaseEndpoint
import NavierStokes.ActualBaseVelocityBounds

/-! # Whole-domain bounds for the uncut, actual slow base -/
/-! Merged from `NavierStokes.WholeDomainHeatBounds` (in a section, so its `open`s cannot leak). -/
section
/-! # Whole-domain jet bounds for the actual exterior heat fields

The parabolic normalization uses the larger of the similarity scale and
physical radial energy. Its image lies in one compact annulus, even when
the original radial coordinate is unbounded.
-/
/-! Merged from `NavierStokes.WholeDomainHeatGeometry` (in a section, so its `open`s cannot leak). -/
section
/-! # Parabolic normalization of the entire exterior heat region -/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.WholeDomainHeatBounds

open ProblemStatement PhysicalWaveSum

def parabolicLinear (a : ℝ) (ha : 0 < a) : SpaceTime ≃L[ℝ] SpaceTime where
  toFun w := (a⁻¹ * w.1, (Real.sqrt a)⁻¹ • w.2)
  invFun w := (a * w.1, Real.sqrt a • w.2)
  left_inv w := by
    ext <;> simp [ha.ne', (Real.sqrt_pos.mpr ha).ne', smul_smul]
  right_inv w := by
    ext <;> simp [ha.ne', (Real.sqrt_pos.mpr ha).ne', smul_smul]
  map_add' u w := by ext <;> simp [mul_add, smul_add]
  map_smul' c w := by ext <;> simp [smul_smul, mul_assoc, mul_comm]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def rescaleOffset (a z : ℝ) : SpaceTime :=
  (1 - a⁻¹, -((Real.sqrt a)⁻¹ * z) • coordinateVector 2)

def rescale (a : ℝ) (ha : 0 < a) (z : ℝ) (w : SpaceTime) : SpaceTime :=
  parabolicLinear a ha w + rescaleOffset a z

@[simp] theorem rescale_time (a : ℝ) (ha : 0 < a) (z : ℝ) (w : SpaceTime) :
    (rescale a ha z w).1 = 1 - (1 - w.1) / a := by
  change a⁻¹ * w.1 + (1-a⁻¹) = _
  ring

@[simp] theorem rescale_space (a : ℝ) (ha : 0 < a) (z : ℝ) (w : SpaceTime) :
    (rescale a ha z w).2 = (Real.sqrt a)⁻¹ • (w.2 - z • coordinateVector 2) := by
  change (Real.sqrt a)⁻¹ • w.2 + -((Real.sqrt a)⁻¹ * z) • coordinateVector 2 = _
  simp [smul_smul, sub_eq_add_neg]

theorem rescale_past (a : ℝ) (ha : 0 < a) (z : ℝ) {w : SpaceTime} (hw : w.1 < 1) :
    (rescale a ha z w).1 < 1 := by
  rw [rescale_time]
  linarith [div_pos (sub_pos.mpr hw) ha]

theorem rescale_radialEnergy (a : ℝ) (ha : 0 < a) (z : ℝ) (w : SpaceTime) :
    AxisymmetricFields.radialEnergy (rescale a ha z w).2 =
      AxisymmetricFields.radialEnergy w.2 / a := by
  rw [rescale_space]
  simp only [AxisymmetricFields.radialEnergy, PiLp.smul_apply, PiLp.sub_apply,
    coordinateVector, PiLp.single_apply, Fin.isValue,
    show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    ite_false, smul_eq_mul, mul_zero, sub_zero]
  rw [mul_pow, mul_pow, inv_pow, Real.sq_sqrt ha.le]
  ring

theorem rescale_axial_zero (a : ℝ) (ha : 0 < a) (w : SpaceTime) :
    (rescale a ha (w.2 2) w).2 2 = 0 := by
  rw [rescale_space]
  simp [coordinateVector]

theorem parabolicLinear_norm_le {a q : ℝ} (ha : 0 < a) (hq : 0 < q)
    (hqa : q ≤ a) (hq1 : q ≤ 1) :
    ‖(parabolicLinear a ha).toContinuousLinearMap‖ ≤ q⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hq.le)
  intro w
  change ‖(a⁻¹ * w.1, (Real.sqrt a)⁻¹ • w.2)‖ ≤ q⁻¹ * ‖w‖
  rw [Prod.norm_def, max_le_iff, norm_mul, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr ha.le),
    Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg a))]
  have hai : a⁻¹ ≤ q⁻¹ := inv_le_inv₀ ha hq |>.mpr hqa
  have hsq : q ≤ Real.sqrt a := by
    apply (Real.le_sqrt hq.le ha.le).mpr
    nlinarith [sq_nonneg q]
  have hri : (Real.sqrt a)⁻¹ ≤ q⁻¹ :=
    (inv_le_inv₀ (Real.sqrt_pos.mpr ha) hq).mpr hsq
  constructor
  · exact mul_le_mul hai (norm_fst_le w) (norm_nonneg _) (inv_nonneg.mpr hq.le)
  · exact mul_le_mul hri (norm_snd_le w) (norm_nonneg _) (inv_nonneg.mpr hq.le)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Exact affine changes of variables lose only the norm of their linear
part, once for each derivative. This does not require global smoothness. -/
theorem norm_iteratedFDeriv_affine_le (L : SpaceTime ≃L[ℝ] SpaceTime)
    (c : SpaceTime) (f : SpaceTime → V) (w : SpaceTime) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f (L y + c)) w‖ ≤
      ‖iteratedFDeriv ℝ m f (L w + c)‖ * ‖L.toContinuousLinearMap‖ ^ m := by
  have he := L.iteratedFDerivWithin_comp_right (fun y => f (y+c))
    uniqueDiffOn_univ (mem_univ (L w)) m
  simp only [preimage_univ, iteratedFDerivWithin_univ] at he
  change iteratedFDeriv ℝ m (fun y => f (L y+c)) w = _ at he
  rw [he, iteratedFDeriv_comp_add_right]
  exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq (by simp)

def normalizedAnnulus (r : ℝ) : Set SpaceTime :=
  {w | w.1 ∈ Icc 0 1 ∧ w.2 2 = 0 ∧ AxisymmetricFields.radialEnergy w.2 ∈ Icc r 1}

theorem normalizedAnnulus_compact (r : ℝ) : IsCompact (normalizedAnnulus r) := by
  have hclosed : IsClosed (normalizedAnnulus r) := by
    have h1 : IsClosed {w : SpaceTime | w.1 ∈ Icc 0 1} :=
      isClosed_Icc.preimage continuous_fst
    have h2 : IsClosed {w : SpaceTime | w.2 2 = 0} :=
      isClosed_eq ((EuclideanSpace.proj 2).continuous.comp continuous_snd) continuous_const
    have h3 : IsClosed {w : SpaceTime | AxisymmetricFields.radialEnergy w.2 ∈ Icc r 1} :=
      isClosed_Icc.preimage
        ((AxisymmetricFields.contDiff_radialEnergy (n := ∞)).continuous.comp continuous_snd)
    exact h1.inter (h2.inter h3)
  apply (isCompact_closedBall (0 : SpaceTime) 3).of_isClosed_subset hclosed
  intro w hw
  have hs := EuclideanSpace.real_norm_sq_eq w.2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change ‖w.2‖ ^ 2 = w.2 0 ^ 2 + (w.2 1 ^ 2 + w.2 2 ^ 2) at hs
  have hrad := hw.2.2.2
  dsimp only [AxisymmetricFields.radialEnergy] at hrad
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
  constructor
  · rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hw.1.1], by linarith [hw.1.2]⟩
  · have hz := hw.2.1
    nlinarith [sq_nonneg ‖w.2‖]

theorem normalize_mem_annulus {h R : ℝ} (hh : 0 < h) (hh1 : h < 1/2)
    (hR : 0 < R) {w : SpaceTime} (hw : w.1 < 1)
    (hX : R < (SlowBorelBase.cartesianChart h w).2.1) :
    let a := max (physicalQ h w) (AxisymmetricFields.radialEnergy w.2)
    rescale a (lt_of_lt_of_le (physicalQ_pos hh hh1 hw) (le_max_left _ _)) (w.2 2) w ∈
      normalizedAnnulus (min R 1) := by
  intro a
  have hq := physicalQ_pos hh hh1 hw
  have ha : 0 < a := hq.trans_le (le_max_left _ _)
  have hs : 0 < AxisymmetricFields.radialEnergy w.2 := by
    change R < AxisymmetricFields.radialEnergy w.2 / physicalQ h w at hX
    exact (mul_pos hR hq).trans ((lt_div_iff₀ hq).mp hX)
  have hτ : 1-w.1 ≤ physicalQ h w := by
    have he := SimilarityCoordinates.coordinateQ_spec (by linarith : 0 < 2*h)
      (by linarith : 2*h < 1) (p := (1-w.1,w.2 2)) (sub_pos.mpr hw)
    have hn := mul_nonneg (sq_nonneg (w.2 2)) (Real.rpow_nonneg he.1.le (2*h))
    change 0 ≤ (w.2 2)^2 * physicalQ h w ^ (2*h) at hn
    have heq := he.2
    change physicalQ h w - (w.2 2)^2 * physicalQ h w ^ (2*h) = 1-w.1 at heq
    linarith
  refine ⟨?_, rescale_axial_zero a ha w, ?_⟩
  · rw [rescale_time]
    exact ⟨by linarith [(div_le_one ha).mpr (hτ.trans (le_max_left _ _))],
      by linarith [div_nonneg (sub_nonneg.mpr hw.le) ha.le]⟩
  · rw [rescale_radialEnergy]
    constructor
    · by_cases hqs : physicalQ h w ≤ AxisymmetricFields.radialEnergy w.2
      · rw [show a = AxisymmetricFields.radialEnergy w.2 from max_eq_right hqs,
          div_self hs.ne']
        exact min_le_right _ _
      · rw [show a = physicalQ h w from max_eq_left (le_of_not_ge hqs)]
        exact (min_le_left _ _).trans hX.le
    · exact (div_le_one ha).mpr (le_max_right _ _)

end NavierStokes.WholeDomainHeatBounds
end


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
end

/-! Merged from `NavierStokes.ActualBasePressureBounds` (in a section, so its `open`s cannot leak). -/
section
/-! Fixed polynomial losses for the actual slow pressure. -/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace NavierStokes.ActualBasePressureBounds

open ProblemStatement SlowBorelBase BaseResidual DiagonalResidual ActualBaseVelocityBounds

def pressureLoss (m : ℕ) : ℝ := 4 * ((m : ℝ) + 1)

theorem pressureLoss_nonneg (m : ℕ) : 0 ≤ pressureLoss m := by
  unfold pressureLoss
  positivity

theorem pressureLoss_controls_core {h : ℝ} (hh1 : h < 1 / 2) (m : ℕ) :
    -pressureLoss m ≤ -2 * CoordinateAlgebra.A h - 2 * m := by
  unfold pressureLoss CoordinateAlgebra.A
  have hm : 0 ≤ (m : ℝ) := by positivity
  linarith

section Actual

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)

theorem actual_bounded_rate (upper : ℝ) (B : ℕ) {l : Filter SpaceTime}
    (hl : l ≤ endpoint)
    (hbox : ∀ᶠ z in l, (cartesianChart F.data.h z).2.1 ≤ FinalSlowBase.boxRadius W upper)
    (m : ℕ) :
    FiniteJetRate l (PhysicalWaveSum.physicalQ F.data.h) (FinalSlowBase.pressure H v upper B)
      m (-2 * CoordinateAlgebra.A F.data.h - 2 * m) := by
  let A := boundedApproach F.data.h_pos F.data.h_lt_half hl (FinalSlowBase.boxRadius W upper) hbox
  have hp : ∀ᶠ z in l, z ∈ past := A.past.mono (fun _ hz => ⟨hz, mem_univ _⟩)
  have hq := A.positive_small F.data.h_pos F.data.h_lt_half
  have hd := FinalSlowBase.coefficients_smooth H v
  have ha := FinalSlowBase.scales_admissible H v upper B
  have hr := pressure_prefix_rate F.data.h_pos F.data.h_lt_half A hd ha m m (by omega)
  have hs := cartesian_prefix_growth F.data.h_pos F.data.h_lt_half A
    (bundleComponent_smooth hd W.axis.normalization 2) (-2 * CoordinateAlgebra.A F.data.h) m m
  have hr' := finiteRate_weaken hr hq (show -2 * CoordinateAlgebra.A F.data.h - 2 * m ≤
      F.data.h * ((m : ℝ) + 1) - 2 * CoordinateAlgebra.A F.data.h - 2 * m by
    have hm : 0 ≤ F.data.h * ((m : ℝ) + 1) := mul_nonneg F.data.h_pos.le (by positivity)
    linarith)
  have hs' := finiteRate_weaken hs hq (show -2 * CoordinateAlgebra.A F.data.h - 2 * m ≤
      -2 * CoordinateAlgebra.A F.data.h - m by
    have hm : 0 ≤ (m : ℝ) := by positivity
    linarith)
  have hps := cartesianUncutPrefix_smooth (b := -2 * CoordinateAlgebra.A F.data.h)
    F.data.h_pos F.data.h_lt_half
    (bundleComponent_smooth hd W.axis.normalization 2) m
  have hsum := finiteRate_add hr' hs' past_isOpen hp
    ((FinalSlowBase.pressure_smooth H v upper B).sub hps) hps
  simp only [prefixPressure, sub_add_cancel] at hsum
  exact hsum

theorem actual_leading_eq (upper : ℝ) (B : ℕ) :
    EqOn (FinalSlowBase.pressure H v upper B)
      (cartesianMonomial F.data.h (-2 * CoordinateAlgebra.A F.data.h)
        ((FinalSlowBase.coefficients H v).pressure 0))
      (BaseExterior.cartesianExterior F.data.h (AssembledSlowBase.nominalOuterX W)) := by
  intro z hz
  exact BaseExterior.exterior_pressure_eq_leading F.data.h_pos F.data.h_lt_half
    (actual_exterior_coefficients H v) hz

theorem actual_middle_rate (upper : ℝ) (B : ℕ) {l : Filter SpaceTime}
    (hl : l ≤ endpoint) {R : ℝ}
    (hR : ∀ᶠ z in l, (cartesianChart F.data.h z).2.1 ≤ R)
    (houter : ∀ᶠ z in l, AssembledSlowBase.nominalOuterX W < (cartesianChart F.data.h z).2.1)
    (m : ℕ) :
    FiniteJetRate l (PhysicalWaveSum.physicalQ F.data.h) (FinalSlowBase.pressure H v upper B)
      m (-2 * CoordinateAlgebra.A F.data.h - m) := by
  let A := boundedApproach F.data.h_pos F.data.h_lt_half hl R hR
  have hr := monomial_rate F.data.h_pos F.data.h_lt_half A
    ((FinalSlowBase.coefficients_smooth H v).pressure 0) (-2 * CoordinateAlgebra.A F.data.h) m
  exact finiteRate_congr_on hr
    (BaseExterior.cartesianExterior_isOpen F.data.h_pos F.data.h_lt_half _)
    ((endpoint_past.filter_mono hl).and houter) (actual_leading_eq H v upper B).symm

/-- Separate the finite coefficient region from the literal heat exterior.
The heat estimate is consumed at its actual exponent without changing the
Borel schedule or imposing a bound on similarity radius. -/
theorem pressure_rate_of_heat (upper : ℝ) (B m : ℕ)
    (hheat : ∀ (l : Filter SpaceTime), l ≤ endpoint →
      (∀ᶠ z in l, BaseExterior.nominalExteriorRadius W < (cartesianChart F.data.h z).2.1) →
      JetRate l (PhysicalWaveSum.physicalQ F.data.h)
        (BaseExterior.heatPressureField (BaseExterior.nominalHeatNormalization W) F.data.h)
        m (-pressureLoss m)) :
    JetRate endpoint (PhysicalWaveSum.physicalQ F.data.h) (FinalSlowBase.pressure H v upper B)
      m (-pressureLoss m) := by
  let S : Set SpaceTime := {z | (cartesianChart F.data.h z).2.1 ≤ FinalSlowBase.boxRadius W upper}
  have hq := endpoint_q_small F.data.h_pos F.data.h_lt_half
  apply rate_glue (S := S) (hq.mono (fun _ hz => hz.1))
  · have hr := actual_bounded_rate H v upper B
      (show endpoint ⊓ 𝓟 S ≤ endpoint from inf_le_left)
      (show ∀ᶠ z in endpoint ⊓ 𝓟 S,
        (cartesianChart F.data.h z).2.1 ≤ FinalSlowBase.boxRadius W upper from restricted_mem endpoint S) m
    exact (finiteRate_at hr le_rfl).weaken (hq.filter_mono inf_le_left)
      (pressureLoss_controls_core F.data.h_lt_half m)
  · let l := endpoint ⊓ 𝓟 Sᶜ
    have hl : l ≤ endpoint := inf_le_left
    have ho : ∀ᶠ z in l,
        AssembledSlowBase.nominalOuterX W < (cartesianChart F.data.h z).2.1 :=
      (restricted_mem endpoint Sᶜ).mono (fun _ hz =>
        (outer_lt_box (W := W) upper).trans (lt_of_not_ge hz))
    let T : Set SpaceTime := {z | (cartesianChart F.data.h z).2.1 ≤ BaseExterior.nominalExteriorRadius W}
    apply rate_glue (S := T) ((hq.filter_mono hl).mono (fun _ hz => hz.1))
    · have hr := actual_middle_rate H v upper B (show l ⊓ 𝓟 T ≤ endpoint from inf_le_left.trans hl)
        (show ∀ᶠ z in l ⊓ 𝓟 T,
          (cartesianChart F.data.h z).2.1 ≤ BaseExterior.nominalExteriorRadius W from restricted_mem l T)
        (ho.filter_mono inf_le_left) m
      apply (finiteRate_at hr le_rfl).weaken (hq.filter_mono (inf_le_left.trans hl))
      have hc := pressureLoss_controls_core F.data.h_lt_half m
      have hm : 0 ≤ (m : ℝ) := by positivity
      linarith
    · have hl' : l ⊓ 𝓟 Tᶜ ≤ endpoint := inf_le_left.trans hl
      have hR : ∀ᶠ z in l ⊓ 𝓟 Tᶜ,
          BaseExterior.nominalExteriorRadius W < (cartesianChart F.data.h z).2.1 :=
        (restricted_mem l Tᶜ).mono (fun _ hz => lt_of_not_ge hz)
      exact (hheat _ hl' hR).congr_on
        (BaseExterior.cartesianExterior_isOpen F.data.h_pos F.data.h_lt_half _)
        ((endpoint_past.filter_mono hl').and hR) (FinalSlowBase.exterior_fields_eq_heat H v upper B).2.symm

/-- The actual pressure has one fixed-order polynomial bound on the full
origin endpoint filter, including arbitrary similarity radii. -/
theorem pressure_rate (upper : ℝ) (B m : ℕ) :
    JetRate endpoint (PhysicalWaveSum.physicalQ F.data.h) (FinalSlowBase.pressure H v upper B)
      m (-pressureLoss m) := by
  apply pressure_rate_of_heat H v upper B m
  intro l hl hR
  obtain ⟨C, hC, hb⟩ := WholeDomainHeatBounds.heat_pressure_bound
    (BaseExterior.nominalHeatNormalization W) F.data.h_pos F.data.h_lt_half
    (BaseExterior.nominalExteriorRadius_pos W) m
  refine ⟨C, hC, ?_⟩
  filter_upwards [endpoint_past.filter_mono hl,
    (endpoint_q_small F.data.h_pos F.data.h_lt_half).filter_mono hl, hR] with w hw hq hRw
  exact (hb w hw hq.2 hRw).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hq.1 hq.2 (by
      unfold pressureLoss WholeDomainHeatBounds.heatLoss
      have hm : 0 ≤ (m : ℝ) := by positivity
      linarith)) hC)

end Actual

end NavierStokes.ActualBasePressureBounds
end


noncomputable section

open Set Filter Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.WholeDomainBaseBounds

open ProblemStatement PhysicalWaveSum WholeDomainStageBounds

def unitDomain (h : ℝ) : Set SpaceTime :=
  {w | w ∈ preterminal ∧ physicalQ h w ≤ 1}

theorem unitDomain_past (h : ℝ) : unitDomain h ⊆ SpacetimeEndpoint.openPast 1 :=
  fun _ hw => ⟨hw.1,mem_univ _⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem rate_of_jet_limit_of_small_scale {h L : ℝ} (hh : 0 < h) (hh1 : h < 1/2)
    (hL : 0 ≤ L) {f : SpaceTime → V} {m : ℕ} {w : SpaceTime}
    {J : SpaceTime [×m]→L[ℝ] V}
    (hJ : Tendsto (iteratedFDeriv ℝ m f) (𝓝[unitDomain h] w) (𝓝 J)) :
    DiagonalResidual.JetRate (𝓝[unitDomain h] w) (physicalQ h) f m (-L) := by
  refine ⟨‖J‖+1,by positivity,?_⟩
  have hb := hJ.norm.eventually (gt_mem_nhds (lt_add_one ‖J‖))
  filter_upwards [hb,self_mem_nhdsWithin] with y hy hyS
  have hq := physicalQ_pos hh hh1 hyS.1
  have hp : 1 ≤ physicalQ h y ^ (-L) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hq hyS.2 (neg_nonpos.mpr hL)
  exact hy.le.trans (le_mul_of_one_le_right (by positivity) hp)

theorem local_rate {h L : ℝ} (hh : 0 < h) (hh1 : h < 1/2) (hL : 0 ≤ L)
    {f : SpaceTime → V} (hf : ContDiffOn ℝ ∞ f (SpacetimeEndpoint.openPast 1))
    (ha : JointResidualLimits.AwayExtensions f) (m : ℕ)
    (ho : DiagonalResidual.JetRate ActualBaseVelocityBounds.endpoint (physicalQ h) f m (-L))
    (w : SpaceTime) :
    DiagonalResidual.JetRate (𝓝[unitDomain h] w) (physicalQ h) f m (-L) := by
  rcases w with ⟨t,x⟩
  rcases lt_trichotomy t 1 with ht | ht | ht
  · have hs := hf.contDiffAt ((SpacetimeEndpoint.openPast_isOpen 1).mem_nhds
      (show (t,x) ∈ SpacetimeEndpoint.openPast 1 from ⟨ht,mem_univ _⟩))
    have hj : ContDiffAt ℝ 0 (iteratedFDeriv ℝ m f) (t,x) :=
      hs.iteratedFDeriv_right (by exact_mod_cast (le_top : 0 + (m : ℕ∞) ≤ ⊤))
    exact rate_of_jet_limit_of_small_scale hh hh1 hL
      (hj.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  · subst t
    have hl : 𝓝[unitDomain h] (1,x) ≤ 𝓝[SpacetimeEndpoint.openPast 1] (1,x) :=
      nhdsWithin_mono _ (unitDomain_past h)
    by_cases hx : x = 0
    · subst x
      obtain ⟨C,hC,hb⟩ := ho
      exact ⟨C,hC,hb.filter_mono hl⟩
    · obtain ⟨U⟩ := ha x hx
      exact rate_of_jet_limit_of_small_scale hh hh1 hL ((U.jet_tendsto m).mono_left hl)
  · refine ⟨0,le_rfl,?_⟩
    have hn : {y : SpaceTime | 1 < y.1} ∈ 𝓝 (t,x) :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds ht
    filter_upwards [nhdsWithin_le_nhds hn,self_mem_nhdsWithin] with y hy hyS
    exact False.elim (not_lt_of_ge hy.le hyS.1)

theorem bound_of_origin_and_exterior {h L R : ℝ} (hh : 0 < h) (hh1 : h < 1/2)
    (hL : 0 ≤ L) (hR : 0 ≤ R) {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (SpacetimeEndpoint.openPast 1))
    (ha : JointResidualLimits.AwayExtensions f) (m : ℕ)
    (ho : DiagonalResidual.JetRate ActualBaseVelocityBounds.endpoint (physicalQ h) f m (-L))
    (he : ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ preterminal, physicalQ h w ≤ 1 →
      R < (SlowBorelBase.cartesianChart h w).2.1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * physicalQ h w ^ (-L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ preterminal, physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * physicalQ h w ^ (-L) := by
  let K := Metric.closedBall (0 : SpaceTime) (R+2)
  obtain ⟨A,hA,hAb⟩ := compact_bound_of_local_rates (S := unitDomain h)
    (isCompact_closedBall (0 : SpaceTime) (R+2))
    (fun _ hw => physicalQ_pos hh hh1 hw.1)
    (fun _ _ => local_rate hh hh1 hL hf ha m ho _)
  obtain ⟨B,hB,hBb⟩ := he
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  intro w hw hq
  by_cases hk : w ∈ K
  · exact (hAb w ⟨hk,hw,hq⟩).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB)
        (Real.rpow_nonneg (physicalQ_pos hh hh1 hw).le _))
  · have hX : R < (SlowBorelBase.cartesianChart h w).2.1 := by
      by_contra hX
      exact hk (in_compact_of_radial_bound hh hh1 hR hw hq (le_of_not_gt hX))
    exact (hBb w hw hq hX).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA)
        (Real.rpow_nonneg (physicalQ_pos hh hh1 hw).le _))

section Actual

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)


theorem pressure_bound (upper : ℝ) (B m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ preterminal, physicalQ F.data.h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (FinalSlowBase.pressure H v upper B) w‖ ≤
        C * physicalQ F.data.h w ^ (-ActualBasePressureBounds.pressureLoss m) := by
  apply bound_of_origin_and_exterior F.data.h_pos F.data.h_lt_half
    (ActualBasePressureBounds.pressureLoss_nonneg m) (BaseExterior.nominalExteriorRadius_pos W).le
    (FinalSlowBase.pressure_smooth H v upper B)
    (SlowBaseEndpoint.final_fields_awayExtensions H v upper B).2 m
    (ActualBasePressureBounds.pressure_rate H v upper B m)
  obtain ⟨C,hC,hb⟩ := WholeDomainHeatBounds.heat_pressure_bound
    (BaseExterior.nominalHeatNormalization W) F.data.h_pos F.data.h_lt_half
    (BaseExterior.nominalExteriorRadius_pos W) m
  refine ⟨C,hC,?_⟩
  intro w hw hq hX
  have he : FinalSlowBase.pressure H v upper B =ᶠ[𝓝 w]
      BaseExterior.heatPressureField (BaseExterior.nominalHeatNormalization W) F.data.h :=
    Filter.eventuallyEq_of_mem
      ((BaseExterior.cartesianExterior_isOpen F.data.h_pos F.data.h_lt_half _).mem_nhds ⟨hw,hX⟩)
      (FinalSlowBase.exterior_fields_eq_heat H v upper B).2
  rw [iteratedFDeriv_eq_of_eventuallyEq he m]
  refine (hb w hw hq hX).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (physicalQ_pos F.data.h_pos F.data.h_lt_half hw) hq ?_) hC)
  unfold WholeDomainHeatBounds.heatLoss ActualBasePressureBounds.pressureLoss
  have hm : 0 ≤ (m : ℝ) := by positivity
  linarith




end Actual

end NavierStokes.WholeDomainBaseBounds

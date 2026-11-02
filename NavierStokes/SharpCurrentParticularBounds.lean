import NavierStokes.ActualCurrentParticularBounds
import NavierStokes.SharpPhysicalLoss
import NavierStokes.LocalPhysicalCopyBounds
import NavierStokes.SharpPhaseJetAlgebra
import NavierStokes.CurrentParticularLabelBounds


/-! Merged from `NavierStokes.CurrentPhysicalRadialClosure`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
/-! Merged from `NavierStokes.SharpCurrentPhysicalPhase` (in a section, so its `open`s cannot leak). -/
section
/-! Merged from `NavierStokes.SharpCommonGraphJets`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/

/-! Merged from `NavierStokes.SharpGeometricModeJets`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

noncomputable section
namespace NavierStokes.SharpGeometricModeJets
open Set Function Filter LocalPhysicalCopyBounds
open scoped ContDiff Topology BigOperators

private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem smul_geometric {f : E → ℂ} {g : E → F}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) (k : ℕ)
    {A B D : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B) (hD : 0 ≤ D)
    (hfb : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f x‖ ≤ A*D^i)
    (hgb : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g x‖ ≤ B*D^i) :
    ‖iteratedFDeriv ℝ k (fun y => f y • g y) x‖ ≤ (2:ℝ)^k*A*B*D^k := by
  apply (norm_iteratedFDeriv_smul_le hf hg x (nat_le_infty k)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i:ℝ)*(A*D^i)*(B*D^(k-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfb i hik) (Nat.cast_nonneg _))
        (hgb (k-i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = (∑ i ∈ Finset.range (k+1), (k.choose i:ℝ))*(A*B*D^k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [show (k.choose i:ℝ)*(A*D^i)*(B*D^(k-i)) =
        (k.choose i:ℝ)*(A*B*(D^i*D^(k-i))) by ring,
        ← pow_add, Nat.add_sub_of_le hik]
    _ = _ := by
      have hc : (∑ i ∈ Finset.range (k+1), (k.choose i:ℝ)) = (2:ℝ)^k := by
        exact_mod_cast Nat.sum_range_choose k
      rw [hc]
      ring

theorem modulated [FiniteDimensional ℝ E]
    {a : E → F} {Φ : E → ℝ} {x : E}
    (ha : SmoothNear a x) (hΦ : SmoothNear Φ x) (m : ℕ)
    {A B D M c : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hD : 0 ≤ D)
    (hM : 1 ≤ M) (hc : |c| ≤ M)
    (hab : ∀ i ≤ m, ‖iteratedFDeriv ℝ i a x‖ ≤ A*D^i)
    (hΦb : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i Φ x‖ ≤ B*D^i) :
    ‖iteratedFDeriv ℝ m (fun y => PhysicalGraphBounds.character c (Φ y) • a y) x‖ ≤
      ((2:ℝ)^m*(m.factorial:ℝ)*M^m*B^m)*A*D^m := by
  obtain ⟨a',ha',hea⟩ := ha.exists_global_germ
  obtain ⟨Φ',hΦ',heΦ⟩ := hΦ.exists_global_germ
  have hprod : (fun y => PhysicalGraphBounds.character c (Φ y) • a y) =ᶠ[𝓝 x]
      (fun y => PhysicalGraphBounds.character c (Φ' y) • a' y) := by
    filter_upwards [hea,heΦ] with y hay hφy
    rw [hay,hφy]
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hprod m]
  have hBB := zero_le_one.trans hB
  have hMM := zero_le_one.trans hM
  have hb := SharpPhaseJetAlgebra.composition_geometric hΦ'
    (PhysicalGraphBounds.character_smooth c) x m
    (B := M^m) (D := B*D) (by positivity) (by positivity)
    (by
      intro i hi
      rw [PhysicalGraphBounds.norm_character_jet]
      exact (pow_le_pow_left₀ (abs_nonneg _) hc i).trans (pow_le_pow_right₀ hM hi))
    (by
      intro i hi him
      rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq heΦ i]
      apply (hΦb i hi him).trans
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [pow_one] using pow_le_pow_right₀ hB hi) (pow_nonneg hD _))
  have hcar : ∀ i ≤ m, ‖iteratedFDeriv ℝ i
      (PhysicalGraphBounds.character c ∘ Φ') x‖ ≤ ((m.factorial:ℝ)*M^m*B^m)*D^i := by
    intro i hi
    apply (hb i hi).trans
    rw [mul_pow]
    calc
      _ ≤ (m.factorial:ℝ)*M^m*(B^m*D^i) := by gcongr
      _ = _ := by ring
  have ham : ∀ i ≤ m, ‖iteratedFDeriv ℝ i a' x‖ ≤ A*D^i := by
    intro i hi
    rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hea i]
    exact hab i hi
  exact (smul_geometric ((PhysicalGraphBounds.character_smooth c).comp hΦ') ha' x m
    (by positivity) hA hD hcar ham).trans_eq (by ring)

end NavierStokes.SharpGeometricModeJets


end

section

noncomputable section
namespace NavierStokes.SharpCommonGraphJets
open Set Function Filter ProblemStatement
open PhysicalGraphBounds PhysicalWaveSum LocalPhysicalCopyBounds
open scoped ContDiff Topology

theorem common_jets {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h a b : ℝ} (hh : 0 ≤ h) (ha : 0 < a) (Δ m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ → ∀ w : SpaceTime,
      scaledRadial n w ∈ annulus a b → |w.1| ≤ 1 → ∀ f : PhysicalWaveSum.LiftPoint → E,
      SmoothNear f (commonLift h n d w) → ∀ A : ℝ, 0 ≤ A →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (commonLift h n d w)‖ ≤ A) →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (f ∘ commonLift h n d) w‖ ≤
        C * A * ChartScales.Q n ^ (-(k : ℝ)*(1+h)) := by
  obtain ⟨G,hG,hgraph⟩ := SharpGraphBounds.physicalLift_positive_jet_bound
    hh ha m
  let C := (m.factorial : ℝ)*G^m*coverBound Δ^m
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos m))
      (one_le_pow₀ hG)) (one_le_pow₀ (coverBound_ge_one Δ))
  refine ⟨C,hC,?_⟩
  intro n hn d hd w hw ht f hf A hA hfb k hkm
  have hQ := ChartScales.Q_pos n
  have hcover : 0 ≤ coverBound Δ := zero_le_one.trans (coverBound_ge_one Δ)
  obtain ⟨F,hF,he⟩ := hf.exists_global_germ
  have haxis := scaledRadial_ne_zero (annulus_axisFree ha hw)
  have he' := he.comp_tendsto (commonLift_smoothAt h n d haxis).continuousAt
  rw [iteratedFDeriv_eq_of_eventuallyEq he' k]
  have hFb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i (F ∘ downLift d) (physicalLift h n w)‖ ≤
      A*coverBound Δ^m := by
    apply downLift_jet_bound hF hd _ hA
    intro i hi
    change ‖iteratedFDeriv ℝ i F (commonLift h n d w)‖ ≤ A
    rw [← iteratedFDeriv_eq_of_eventuallyEq he i]
    exact hfb i hi
  let U : Set SpaceTime := {w | radialProjection w ≠ 0}
  have hU : IsOpen U := axisFree_open.preimage radialProjection.continuous
  have hb := SharpPhaseJetAlgebra.composition_geometric_on hU (physicalLift_smooth h n)
    (hF.comp (downLift d).contDiff) haxis m
    (B := A*coverBound Δ^m) (D := G*ChartScales.Q n^(-(1+h))) (by positivity) (by positivity)
    hFb (by
      intro i hi him
      apply (hgraph n hn w hw ht i hi him).trans
      rw [mul_pow, ← Real.rpow_mul_natCast (ChartScales.Q_pos n).le,
        show -(1+h)*(i:ℝ) = -(i:ℝ)*(1+h) by ring]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [pow_one] using pow_le_pow_right₀ hG hi) (by positivity)) k hkm
  apply hb.trans
  rw [mul_pow, ← Real.rpow_mul_natCast (ChartScales.Q_pos n).le]
  calc
    _ ≤ (m.factorial : ℝ)*(A*coverBound Δ^m)*(G^m*ChartScales.Q n^(-(1+h)*(k:ℝ))) := by
      gcongr
    _ = _ := by
      rw [show -(1+h)*(k:ℝ) = -(k:ℝ)*(1+h) by ring]
      dsimp [C]
      ring

end NavierStokes.SharpCommonGraphJets


end

noncomputable section
namespace NavierStokes.SharpCurrentPhysicalPhase
open Set Function Filter ProblemStatement CorrectionInitialization
open PhysicalGraphBounds PhysicalWaveSum LocalPhysicalCopyBounds
open scoped ContDiff Topology

abbrev Label (B N0 : ℕ) := ActualPrimaryBounds.SignedLabel B N0
abbrev Native := ActualParticularBackground.Native

abbrev h : ℝ := ActualPrimary.h

noncomputable def nativeMap (a : ℝ) (c : PolarCharts.Index) (n d : ℕ) : SpaceTime → Native :=
  CurrentPhysicalChartJets.chartMap a c ∘ commonLift h n d

noncomputable def fullMap (a : ℝ) (c : PolarCharts.Index) (n d : ℕ) :
    SpaceTime → ActualPrimary.FullPoint := ActualParticularBackground.nativeToFull ∘ nativeMap a c n d

theorem fullMap_angle (a : ℝ) (c : PolarCharts.Index) (n d : ℕ) (w : SpaceTime) :
    (fullMap a c n d w).2 = (PolarCharts.chart a c (scaledRadial n w)).2 := by
  change (PolarCharts.chart a c (liftXY (commonLift h n d w))).2 = _
  rw [CurrentPhysicalModeGerms.liftXY_common]

theorem slot_axial (l : Label B N0) (a : ℝ) (c : PolarCharts.Index) (n d : ℕ) (w : SpaceTime) :
    ActualPhaseJetBounds.nativeZ (ActualPrimaryBounds.slotLinear l n (fullMap a c n d w)) =
      ChartScales.Q (BaseChartJets.cellBand l.2) ^ (-CoordinateAlgebra.D h) * w.2 2 := by
  change PhysicalParticularWave.ratioPower (ChartScales.Q n)
    (ChartScales.Q (BaseChartJets.cellBand l.2)) (CoordinateAlgebra.D h) *
      (ChartScales.Q n ^ (-CoordinateAlgebra.D h) * w.2 2 + 0) = _
  rw [add_zero, ← mul_assoc, PhysicalParticularWave.ratioPower_cancel
    (ChartScales.Q_pos n) (ChartScales.Q_pos _)]

theorem phaseLinear_physical (l : Label B N0) (a : ℝ) (c : PolarCharts.Index)
    (n d : ℕ) (w : SpaceTime) :
    ActualPhaseJetBounds.phaseLinear l n (fullMap a c n d w) =
      (ActualPrimary.phases B N0 l.1).phase.p l.2 * (PolarCharts.chart a c (scaledRadial n w)).2 +
      (ActualPrimary.phases B N0 l.1).phase.pz l.2 *
        ChartScales.Q (BaseChartJets.cellBand l.2) ^ (-(1 / 2 : ℝ)) * w.2 2 := by
  simp only [ActualPhaseJetBounds.phaseLinear, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.comp_apply, smul_eq_mul,
    fullMap_angle, slot_axial]
  congr 1
  rw [div_eq_mul_inv, mul_assoc, ← mul_assoc
    (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand l.2))⁻¹]
  change _ * (((ChartScales.epsilon h _)⁻¹ * ChartScales.Q _ ^ (-CoordinateAlgebra.D h)) * _) = _
  rw [SharpPhysicalPhase.axial_scale]
  ring

theorem power_window (l : Label B N0) {n : ℕ} (hn : ActualPrimaryBounds.near l n) (s : ℝ) :
    ChartScales.Q (BaseChartJets.cellBand l.2) ^ s ≤
      ActualSignedGeometry.powerBound (-s) * ChartScales.Q n ^ s := by
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (ChartScales.Q_pos n) s)).mp
  have he := PhysicalParticularWave.ratioPower_neg_div (ChartScales.Q_pos n)
    (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) (-s)
  simp only [neg_neg] at he
  rw [he]
  exact ActualSignedGeometry.dyadic_ratioPower_le
    (ActualPrimaryBounds.near_distance hn).1 (ActualPrimaryBounds.near_distance hn).2 (-s)


private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

theorem smoothNear_comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} {g : E → F} {x : E} (hf : SmoothNear f (g x)) (hg : SmoothNear g x) :
    SmoothNear (f ∘ g) x := by
  obtain ⟨V,hV,hgx,hf⟩ := hf
  obtain ⟨U,hU,hx,hg⟩ := hg
  obtain ⟨W,hWV,hW,hxW⟩ := mem_nhds_iff.mp
    ((hg.contDiffAt (hU.mem_nhds hx)).continuousAt.preimage_mem_nhds (hV.mem_nhds hgx))
  refine ⟨U ∩ W,hU.inter hW,⟨hx,hxW⟩,?_⟩
  exact hf.comp (hg.mono inter_subset_left) (fun y hy => hWV hy.2)

theorem nativeMap_smoothNear {a : ℝ} (ha : 0 < a) (c : PolarCharts.Index) (n d : ℕ)
    {w : SpaceTime} (hw : radialProjection w ≠ 0) : SmoothNear (nativeMap a c n d) w := by
  let U : Set SpaceTime := {w | radialProjection w ≠ 0}
  have hU : IsOpen U := axisFree_open.preimage radialProjection.continuous
  refine ⟨U,hU,hw,?_⟩
  exact (CurrentPhysicalChartJets.chartMap_smooth ha c).comp_contDiffOn
    ((downLift d).contDiff.comp_contDiffOn (physicalLift_smooth h n))

theorem fullMap_smoothNear {a : ℝ} (ha : 0 < a) (c : PolarCharts.Index) (n d : ℕ)
    {w : SpaceTime} (hw : radialProjection w ≠ 0) : SmoothNear (fullMap a c n d) w := by
  obtain ⟨U,hU,hx,hs⟩ := nativeMap_smoothNear ha c n d hw
  exact ⟨U,hU,hx,ActualParticularBackground.nativeToFull.toContinuousLinearEquiv.contDiff.comp_contDiffOn hs⟩

theorem native_jets {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (ha : 0 < a) (Δ m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ → ∀ w : SpaceTime,
      scaledRadial n w ∈ annulus a b → |w.1| ≤ 1 → ∀ c : PolarCharts.Index,
      ∀ f : Native → E, SmoothNear f (nativeMap a c n d w) → ∀ A : ℝ, 0 ≤ A →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (nativeMap a c n d w)‖ ≤ A) →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (f ∘ nativeMap a c n d) w‖ ≤
        C*A*ChartScales.Q n^(-(k:ℝ)*(1+h)) := by
  obtain ⟨M,hM,hm⟩ := CurrentPhysicalChartJets.composition_jets (E := E) (b := b) ha m
  obtain ⟨C,hC,hc⟩ := SharpCommonGraphJets.common_jets (E := E) (b := b)
    ActualPrimary.outgoing.data.h_pos.le ha Δ m
  refine ⟨C*M,one_le_mul_of_one_le_of_one_le hC hM,?_⟩
  intro n hn d hd w hw ht c f hf A hA hfb k hk
  exact (hc n hn d hd w hw ht (f ∘ CurrentPhysicalChartJets.chartMap a c)
    (CurrentPhysicalChartJets.composition_smoothNear ha hf) (M*A) (by positivity)
    (hm c _ (PhysicalClassBounds.commonLift_mem_cylindricalDomain ha h n d w hw)
      f hf A hA hfb) k hk).trans_eq (by dsimp [h, ActualPrimary.h]; ring)

theorem full_jets {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (ha : 0 < a) (Δ m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ → ∀ w : SpaceTime,
      scaledRadial n w ∈ annulus a b → |w.1| ≤ 1 → ∀ c : PolarCharts.Index,
      ∀ f : ActualPrimary.FullPoint → E, SmoothNear f (fullMap a c n d w) → ∀ A : ℝ, 0 ≤ A →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (fullMap a c n d w)‖ ≤ A) →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (f ∘ fullMap a c n d) w‖ ≤
        C*A*ChartScales.Q n^(-(k:ℝ)*(1+h)) := by
  obtain ⟨C,hC,hc⟩ := native_jets (E := E) (b := b) ha Δ m
  refine ⟨C,hC,?_⟩
  intro n hn d hd w hw ht c f hf A hA hfb k hk
  have he : SmoothNear (f ∘ ActualParticularBackground.nativeToFull) (nativeMap a c n d w) := by
    obtain ⟨U,hU,hx,hs⟩ := hf
    exact ⟨_,hU.preimage ActualParticularBackground.nativeToFull.continuous,hx,
      hs.comp ActualParticularBackground.nativeToFull.toContinuousLinearEquiv.contDiff.contDiffOn
        (fun _ hy => hy)⟩
  apply hc n hn d hd w hw ht c (f ∘ ActualParticularBackground.nativeToFull) he A hA _ k hk
  intro i hi
  rw [show f ∘ ActualParticularBackground.nativeToFull =
    fun z => f (ActualParticularBackground.nativeToFull z) from rfl,
    StateReindex.norm_iteratedFDeriv_pull]
  exact hfb i hi

noncomputable def remainder (n : ℕ) (i : ActualPhaseJetBounds.CopyIndex B N0)
    (x : ActualPrimary.FullPoint) : ℝ := ActualPhaseJetBounds.nativeRemainder i.1
      ((ActualPrimaryBounds.fullCopy i.1 n i.2 x).1,(ActualPrimaryBounds.fullCopy i.1 n i.2 x).2.2)

theorem remainder_smoothNear {n : ℕ} {i : ActualPhaseJetBounds.CopyIndex B N0}
    {x : ActualPrimary.FullPoint} (hx : x ∈ ActualPhaseJetBounds.phaseCell n i) :
    SmoothNear (remainder n i) x := by
  let g : ActualPrimary.FullPoint → PhaseCalculus.Slow × ℝ := fun y =>
    ActualPrimaryBounds.slotLinear i.1 n y +
      ActualPrimaryBounds.slotOfNative (ActualPrimaryBounds.copyPoint i.1 n i.2 0)
  have hg : ContDiff ℝ ∞ g := (ActualPrimaryBounds.slotLinear i.1 n).contDiff.add contDiff_const
  have hxg : g x ∈ ActualPhaseJetBounds.jetDomain.carrier i.1 := by
    simpa only [g, ← ActualPrimaryBounds.slotCopy_affine] using ActualPhaseJetBounds.phaseCell_maps hx
  refine ⟨g ⁻¹' ActualPhaseJetBounds.jetDomain.carrier i.1,
    (ActualPhaseJetBounds.jetDomain.isOpen i.1).preimage hg.continuous,hxg,?_⟩
  have hb := (ActualPhaseJetBounds.nativeRemainder_polynomial.smooth i.1).comp
    (hg.contDiffOn (s := g ⁻¹' ActualPhaseJetBounds.jetDomain.carrier i.1)) (fun _ hy => hy)
  change ContDiffOn ℝ ∞ (remainder n i) (g ⁻¹' ActualPhaseJetBounds.jetDomain.carrier i.1)
  apply hb.congr
  intro y _
  dsimp [remainder, Function.comp_def, g]
  rw [← ActualPrimaryBounds.slotCopy_affine]

theorem localPhase_physical (n : ℕ) (i : ActualPhaseJetBounds.CopyIndex B N0)
    (a : ℝ) (c : PolarCharts.Index) (d : ℕ) (w : SpaceTime) :
    ActualPhaseJetBounds.localPhase n i (fullMap a c n d w) =
      (ActualPrimary.phases B N0 i.1.1).phase.p i.1.2 *
        (PolarCharts.chart a c (scaledRadial n w)).2 +
      ((ActualPrimary.phases B N0 i.1.1).phase.pz i.1.2 *
        ChartScales.Q (BaseChartJets.cellBand i.1.2)^(-(1/2:ℝ))*w.2 2 +
        ActualPhaseJetBounds.phaseOffset n i) + remainder n i (fullMap a c n d w) := by
  rw [ActualPhaseJetBounds.localPhase_decomposition,phaseLinear_physical]
  dsimp [remainder]
  ring

theorem localPhase_positive_jets {a b : ℝ} (ha : 0 < a) (Δ m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ c : PolarCharts.Index, ∀ i : ActualPhaseJetBounds.CopyIndex B N0, ∀ w : SpaceTime,
      scaledRadial n w ∈ annulus a b → |w.1| ≤ 1 →
      fullMap a c n d w ∈ ActualPhaseJetBounds.phaseCell n i →
      ∀ k, 1 ≤ k → k ≤ m →
      ‖iteratedFDeriv ℝ k (ActualPhaseJetBounds.localPhase n i ∘ fullMap a c n d) w‖ ≤
        C*ChartScales.S n^p*ChartScales.Q n^(-(k:ℝ)*(1+h)) := by
  obtain ⟨K,hK,hpolar⟩ := PolarCharts.chart_finiteJets_uniform ha b m
  obtain ⟨R,hR,p,hr⟩ := ActualPhaseJetBounds.polynomial_copy_bound
    (ActualPhaseJetBounds.nativeRemainder_polynomial (B := B) (N0 := N0)) m
  obtain ⟨D,hD,hd⟩ := full_jets (E := ℝ) (b := b) ha Δ m
  let M := ActualPhaseJetBounds.phaseSize B N0
  let W := ActualSignedGeometry.powerBound (1/2)
  have hM : 1 ≤ M := ActualPhaseJetBounds.one_le_phaseSize
  have hW : 1 ≤ W := ActualSignedGeometry.powerBound_one _
  let C := M*K+M*W+D*R
  have hC : 1 ≤ C := by
    have hMK := one_le_mul_of_one_le_of_one_le hM hK
    have hMW := one_le_mul_of_one_le_of_one_le hM hW
    have hDR := one_le_mul_of_one_le_of_one_le hD hR
    dsimp [C]
    linarith
  refine ⟨C,hC,p,?_⟩
  intro n hn d hd' c i w hw ht hi k hk hkm
  have hQ := ChartScales.Q_pos n
  have hS := PhysicalGraphBounds.S_ge_one (show 1 ≤ n by omega)
  have hSp : 1 ≤ ChartScales.S n^p := one_le_pow₀ hS
  have haxis := scaledRadial_ne_zero (annulus_axisFree ha hw)
  have hfull := fullMap_smoothNear ha c n d haxis
  have hrnear := smoothNear_comp (remainder_smoothNear hi) hfull
  have hpolars := (PolarCharts.chart_contDiff ha c).comp (scaledRadial n).contDiff
  have hangle : ‖iteratedFDeriv ℝ k
      (fun y => (ActualPrimary.phases B N0 i.1.1).phase.p i.1.2 *
        (PolarCharts.chart a c (scaledRadial n y)).2) w‖ ≤
      M*K*ChartScales.Q n^(-(k:ℝ)*(1+h)) := by
    have hangleSmooth : ContDiff ℝ ∞
        (fun y => (PolarCharts.chart a c (scaledRadial n y)).2) := hpolars.snd
    rw [norm_jet_const_mul hangleSmooth w ((ActualPrimary.phases B N0 i.1.1).phase.p i.1.2) k]
    have hp := SharpPhysicalPhase.polarMap_jets (PolarCharts.chart_contDiff ha c)
      ActualPrimary.outgoing.data.h_pos.le (zero_le_one.trans hK) n m w
      (fun j hj => hpolar c j hj _ hw.1) k hkm
    have hs := norm_jet_linear_comp hpolars (ContinuousLinearMap.snd ℝ ℝ ℝ) w k
    have hs' := hs.trans ((mul_le_mul (norm_sndCLM_le ℝ ℝ) hp (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    have hb := mul_le_mul (ActualPhaseJetBounds.phase_constants_bound i.1).1 hs'
      (norm_nonneg _) (zero_le_one.trans hM)
    apply hb.trans_eq
    rw [← Real.rpow_mul_natCast hQ.le]
    rw [show -(1+ActualPrimary.h)*(k:ℝ) = -(k:ℝ)*(1+h) by dsimp [h]; ring]
    ring
  let L : SpaceTime →L[ℝ] ℝ :=
    ((ActualPrimary.phases B N0 i.1.1).phase.pz i.1.2 *
      ChartScales.Q (BaseChartJets.cellBand i.1.2)^(-(1/2:ℝ))) • coordinateProjection 2
  have hlin : ‖iteratedFDeriv ℝ k (fun y => L y+ActualPhaseJetBounds.phaseOffset n i) w‖ ≤
      M*W*ChartScales.Q n^(-(k:ℝ)*(1+h)) := by
    apply (ActualPhaseJetBounds.norm_positive_jet_affine L _ w hk).trans
    have hL : ‖L‖ ≤ M*ChartScales.Q (BaseChartJets.cellBand i.1.2)^(-(1/2:ℝ)) := by
      dsimp [L]
      rw [norm_smul ((ActualPrimary.phases B N0 i.1.1).phase.pz i.1.2 *
        ChartScales.Q (BaseChartJets.cellBand i.1.2)^(-(1/2:ℝ)) : ℝ) (coordinateProjection 2)]
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos _) _)]
      exact (mul_le_mul (mul_le_mul_of_nonneg_right
        (ActualPhaseJetBounds.phase_constants_bound i.1).2.1 (Real.rpow_pos_of_pos (ChartScales.Q_pos _) _).le)
        ((show ‖coordinateProjection 2‖ ≤ 1 from by
          apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
          intro v
          exact (PiLp.norm_apply_le v.2 2).trans (by simpa only [one_mul] using norm_snd_le v))) (norm_nonneg _) (mul_nonneg (zero_le_one.trans hM) (Real.rpow_pos_of_pos (ChartScales.Q_pos _) _).le)).trans_eq (mul_one _)
    apply hL.trans
    calc
      _ ≤ M*(W*ChartScales.Q n^(-(1/2:ℝ))) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [neg_neg, W] using power_window i.1 hi.1 (-(1/2))) (zero_le_one.trans hM)
      _ ≤ M*(W*ChartScales.Q n^(-(k:ℝ)*(1+h))) := by
        apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hM)
        apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hW)
        apply Real.rpow_le_rpow_of_exponent_ge hQ (ChartScales.Q_le_one n)
        have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
        have hh : 0 ≤ h := ActualPrimary.outgoing.data.h_pos.le
        nlinarith
      _ = _ := by ring
  have hrem := hd n hn d hd' w hw ht c (remainder n i) (remainder_smoothNear hi)
    (R*ChartScales.S n^p) (by positivity) (hr n i _ hi) k hkm
  have he : ActualPhaseJetBounds.localPhase n i ∘ fullMap a c n d = fun y =>
      (ActualPrimary.phases B N0 i.1.1).phase.p i.1.2 *
        (PolarCharts.chart a c (scaledRadial n y)).2 +
      (L y + ActualPhaseJetBounds.phaseOffset n i) + remainder n i (fullMap a c n d y) :=
    funext (localPhase_physical n i a c d)
  have hangleSmooth : ContDiffAt ℝ k (fun y =>
      (ActualPrimary.phases B N0 i.1.1).phase.p i.1.2 *
        (PolarCharts.chart a c (scaledRadial n y)).2) w :=
    ((contDiff_const.mul hpolars.snd).contDiffAt).of_le (nat_le_infty k)
  have hlinearSmooth : ContDiffAt ℝ k (fun y => L y + ActualPhaseJetBounds.phaseOffset n i) w :=
    ((L.contDiff.add contDiff_const).contDiffAt).of_le (nat_le_infty k)
  have hremSmooth : ContDiffAt ℝ k (fun y => remainder n i (fullMap a c n d y)) w :=
    hrnear.contDiffAt.of_le (nat_le_infty k)
  rw [he, fun_iteratedFDeriv_add_apply (hangleSmooth.add hlinearSmooth) hremSmooth,
    fun_iteratedFDeriv_add_apply hangleSmooth hlinearSmooth]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) (le_refl _)).trans
  calc
    _ ≤ M*K*ChartScales.Q n^(-(k:ℝ)*(1+h)) + M*W*ChartScales.Q n^(-(k:ℝ)*(1+h)) +
        D*(R*ChartScales.S n^p)*ChartScales.Q n^(-(k:ℝ)*(1+h)) :=
      add_le_add (add_le_add hangle hlin) hrem
    _ ≤ (M*K*ChartScales.S n^p)*ChartScales.Q n^(-(k:ℝ)*(1+h)) +
        (M*W*ChartScales.S n^p)*ChartScales.Q n^(-(k:ℝ)*(1+h)) +
        D*(R*ChartScales.S n^p)*ChartScales.Q n^(-(k:ℝ)*(1+h)) := by
      apply add_le_add _ (le_refl _)
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right (by positivity : 0 ≤ M*K) hSp) (by positivity)
      · exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right (by positivity : 0 ≤ M*W) hSp) (by positivity)
    _ = _ := by dsimp [C]; ring


theorem weightedPhase_positive_jets {a b : ℝ} (ha : 0 < a) (Δ m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ c : PolarCharts.Index, ∀ i : ActualPhaseJetBounds.CopyIndex B N0, ∀ w : SpaceTime,
      scaledRadial n w ∈ annulus a b → |w.1| ≤ 1 →
      fullMap a c n d w ∈ ActualPhaseJetBounds.phaseCell n i →
      ∀ k, 1 ≤ k → k ≤ m →
      ‖iteratedFDeriv ℝ k (ActualCurrentCarrierJets.weightedPhase i.1 n ∘ nativeMap a c n d) w‖ ≤
        C*ChartScales.S n^p*ChartScales.Q n^(-(k:ℝ)*SharpPhysicalCarrier.derivativeCost h) := by
  obtain ⟨L,hL,p,hl⟩ := localPhase_positive_jets (B := B) (N0 := N0) (b := b) ha Δ m
  let W := ActualSignedGeometry.powerBound (h/2)
  have hW : 1 ≤ W := ActualSignedGeometry.powerBound_one _
  have hh : 0 ≤ h := ActualPrimary.outgoing.data.h_pos.le
  refine ⟨2*W*L,one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by norm_num) hW) hL,p,?_⟩
  intro n hn d hd c i w hw ht hi k hk hkm
  have hQ := ChartScales.Q_pos n
  have hS := PhysicalGraphBounds.S_ge_one (show 1 ≤ n by omega)
  have haxis := scaledRadial_ne_zero (annulus_axisFree ha hw)
  have hfull := fullMap_smoothNear ha c n d haxis
  have he := (ActualPhaseJetBounds.weightedPhase_germ hi).comp_tendsto hfull.contDiffAt.continuousAt
  change ‖iteratedFDeriv ℝ k (ActualPhaseJetBounds.weightedPhase i.1 n ∘ fullMap a c n d) w‖ ≤ _
  rw [iteratedFDeriv_eq_of_eventuallyEq he k]
  have hlocal := (ActualPhaseJetBounds.localPhase_smooth hi).comp w hfull.contDiffAt
  change ‖iteratedFDeriv ℝ k (fun y =>
    (ChartScales.carrier h (BaseChartJets.cellBand i.1.2):ℝ) •
      (ActualPhaseJetBounds.localPhase n i ∘ fullMap a c n d) y) w‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hlocal.of_le (nat_le_infty k)),
    norm_smul (ChartScales.carrier h (BaseChartJets.cellBand i.1.2):ℝ)
      (iteratedFDeriv ℝ k (ActualPhaseJetBounds.localPhase n i ∘ fullMap a c n d) w),
    Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hcar : (ChartScales.carrier h (BaseChartJets.cellBand i.1.2):ℝ) ≤
      2*W*ChartScales.Q n^(-h/2) := by
    apply (carrier_upper hh _).trans
    have hb := power_window i.1 hi.1 (-h/2)
    have he : -(-h/2) = h/2 := by ring
    rw [he] at hb
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (show (0:ℝ) ≤ 2 by norm_num)
  calc
    _ ≤ (2*W*ChartScales.Q n^(-h/2)) *
        (L*ChartScales.S n^p*ChartScales.Q n^(-(k:ℝ)*(1+h))) :=
      mul_le_mul hcar (hl n hn d hd c i w hw ht hi k hk hkm) (norm_nonneg _) (by positivity)
    _ = (2*W*L)*ChartScales.S n^p*ChartScales.Q n^(-h/2-(k:ℝ)*(1+h)) := by
      rw [show (2*W*ChartScales.Q n^(-h/2)) *
          (L*ChartScales.S n^p*ChartScales.Q n^(-(k:ℝ)*(1+h))) =
        (2*W*L)*ChartScales.S n^p*(ChartScales.Q n^(-h/2)*ChartScales.Q n^(-(k:ℝ)*(1+h))) by ring,
        ← Real.rpow_add hQ]
      congr 2
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_ge hQ (ChartScales.Q_le_one n)
      have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
      unfold SharpPhysicalCarrier.derivativeCost
      nlinarith

theorem weightedPhase_smoothNear {a : ℝ} (ha : 0 < a) (c : PolarCharts.Index) (n d : ℕ)
    {i : ActualPhaseJetBounds.CopyIndex B N0} {w : SpaceTime} (hw : radialProjection w ≠ 0)
    (hi : fullMap a c n d w ∈ ActualPhaseJetBounds.phaseCell n i) :
    SmoothNear (ActualCurrentCarrierJets.weightedPhase i.1 n ∘ nativeMap a c n d) w := by
  change SmoothNear (ActualPhaseJetBounds.weightedPhase i.1 n ∘ fullMap a c n d) w
  exact smoothNear_comp (ActualCurrentCarrierJets.full_weightedPhase_smoothNear hi)
    (fullMap_smoothNear ha c n d hw)

end NavierStokes.SharpCurrentPhysicalPhase
end

/-! Merged from `NavierStokes.SharpCurrentModeJets`. -/
noncomputable section
namespace NavierStokes.SharpCurrentModeJets
open Set Function Filter ProblemStatement CorrectionInitialization
open LocalPhysicalCopyBounds SharpCurrentPhysicalPhase
open scoped ContDiff Topology

private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

theorem commonLift_smoothNear (n d : ℕ) {w : SpaceTime}
    (hw : PhysicalGraphBounds.radialProjection w ≠ 0) :
    SmoothNear (PhysicalWaveSum.commonLift h n d) w :=
  ⟨_, PhysicalGraphBounds.axisFree_open.preimage PhysicalGraphBounds.radialProjection.continuous,
    hw, (PhysicalWaveSum.downLift d).contDiff.comp_contDiffOn (PhysicalGraphBounds.physicalLift_smooth h n)⟩

theorem lift_mode_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    {a b : ℝ} (ha : 0 < a) (Δ m : ℕ) (g A : ℝ) (e : ℕ) (hA : 0 ≤ A) (j : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ c : PolarCharts.Index, ∀ i : ActualPhaseJetBounds.CopyIndex B N0, ∀ w : SpaceTime,
      PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b → |w.1| ≤ 1 →
      fullMap a c n d w ∈ ActualPhaseJetBounds.phaseCell n i →
      ∀ f : PhysicalWaveSum.LiftPoint → E, SmoothNear f (PhysicalWaveSum.commonLift h n d w) →
      (∀ r ≤ m, ‖iteratedFDeriv ℝ r f (PhysicalWaveSum.commonLift h n d w)‖ ≤
        A*ChartScales.Q n^g*ChartScales.S n^e) →
      ‖iteratedFDeriv ℝ m (fun y => PhysicalGraphBounds.character (j:ℝ)
        (ActualCurrentCarrierJets.weightedPhase i.1 n (nativeMap a c n d y)) •
          f (PhysicalWaveSum.commonLift h n d y)) w‖ ≤
        C*ChartScales.Q n^(g-(m:ℝ)*SharpPhysicalCarrier.derivativeCost h)*ChartScales.S n^p := by
  obtain ⟨K,hK,hk⟩ := SharpCommonGraphJets.common_jets (E := E) (b := b)
    ActualPrimary.outgoing.data.h_pos.le ha Δ m
  obtain ⟨D,hD,p,hp⟩ := weightedPhase_positive_jets (B := B) (N0 := N0) (b := b) ha Δ m
  let M := 1+|(j:ℝ)|
  have hM : 1 ≤ M := le_add_of_nonneg_right (abs_nonneg _)
  let C := (2:ℝ)^m*(m.factorial:ℝ)*M^m*D^m*K*A
  refine ⟨C,by dsimp [C]; positivity,e+p*m,?_⟩
  intro n hn d hd c i w hw ht hi f hf hfb
  have hQ := ChartScales.Q_pos n
  have hS := PhysicalGraphBounds.S_ge_one (show 1 ≤ n by omega)
  have haxis := PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree ha hw)
  let V := ChartScales.Q n^(-SharpPhysicalCarrier.derivativeCost h)
  have hV : 0 ≤ V := (Real.rpow_pos_of_pos hQ _).le
  have hDb : 1 ≤ D*ChartScales.S n^p := one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ hS)
  have hfb' : ∀ r ≤ m, ‖iteratedFDeriv ℝ r (f ∘ PhysicalWaveSum.commonLift h n d) w‖ ≤
      (K*A*ChartScales.Q n^g*ChartScales.S n^e)*V^r := by
    intro r hr
    apply (hk n hn d hd w hw ht f hf _ (by positivity) hfb r hr).trans
    dsimp [V]
    rw [← Real.rpow_mul_natCast hQ.le]
    have hcost : -(SharpPhysicalCarrier.derivativeCost h)*(r:ℝ) ≤ -(r:ℝ)*(1+h) := by
      have hh : 0 ≤ h := ActualPrimary.outgoing.data.h_pos.le
      have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
      unfold SharpPhysicalCarrier.derivativeCost
      nlinarith
    calc
      _ ≤ K*(A*ChartScales.Q n^g*ChartScales.S n^e)*
          ChartScales.Q n^(-SharpPhysicalCarrier.derivativeCost h*(r:ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hQ (ChartScales.Q_le_one n) hcost)
          (by positivity)
      _ = _ := by ring
  have hph : ∀ r, 1 ≤ r → r ≤ m →
      ‖iteratedFDeriv ℝ r (ActualCurrentCarrierJets.weightedPhase i.1 n ∘ nativeMap a c n d) w‖ ≤
        (D*ChartScales.S n^p)*V^r := by
    intro r hr hrm
    apply (hp n hn d hd c i w hw ht hi r hr hrm).trans_eq
    dsimp [V]
    rw [← Real.rpow_mul_natCast hQ.le]
    congr 2
    ring
  have hb := SharpGeometricModeJets.modulated (c := (j:ℝ))
    (smoothNear_comp hf (commonLift_smoothNear n d haxis))
    (weightedPhase_smoothNear ha c n d haxis hi) m
    (by positivity) hDb hV hM (by dsimp [M]; linarith [abs_nonneg (j:ℝ)]) hfb' hph
  apply hb.trans_eq
  dsimp [V,C]
  rw [mul_pow, ← pow_mul, pow_add, ← Real.rpow_mul_natCast hQ.le,
    Real.rpow_sub hQ]
  have hpow : ChartScales.Q n^(-SharpPhysicalCarrier.derivativeCost h*(m:ℝ)) =
      (ChartScales.Q n^((m:ℝ)*SharpPhysicalCarrier.derivativeCost h))⁻¹ := by
    rw [← Real.rpow_neg hQ.le]
    congr 1
    ring
  rw [hpow]
  ring

theorem native_mode_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    {a b : ℝ} (ha : 0 < a) (Δ m : ℕ) (g A : ℝ) (e : ℕ) (hA : 0 ≤ A) (j : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ c : PolarCharts.Index, ∀ i : ActualPhaseJetBounds.CopyIndex B N0, ∀ w : SpaceTime,
      PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b → |w.1| ≤ 1 →
      fullMap a c n d w ∈ ActualPhaseJetBounds.phaseCell n i →
      ∀ f : Native → E, SmoothNear f (nativeMap a c n d w) →
      (∀ r ≤ m, ‖iteratedFDeriv ℝ r f (nativeMap a c n d w)‖ ≤
        A*ChartScales.Q n^g*ChartScales.S n^e) →
      ‖iteratedFDeriv ℝ m (fun y => PhysicalGraphBounds.character (j:ℝ)
        (ActualCurrentCarrierJets.weightedPhase i.1 n (nativeMap a c n d y)) •
          f (nativeMap a c n d y)) w‖ ≤
        C*ChartScales.Q n^(g-(m:ℝ)*SharpPhysicalCarrier.derivativeCost h)*ChartScales.S n^p := by
  obtain ⟨M,hM,hm⟩ := CurrentPhysicalChartJets.composition_jets (E := E) (b := b) ha m
  obtain ⟨C,hC,p,hc⟩ := lift_mode_bound (E := E) (B := B) (N0 := N0) (b := b)
    ha Δ m g (M*A) e (by positivity) j
  refine ⟨C,hC,p,?_⟩
  intro n hn d hd c i w hw ht hi f hf hfb
  have hQ := ChartScales.Q_pos n
  have hS := PhysicalGraphBounds.S_ge_one (show 1 ≤ n by omega)
  apply hc n hn d hd c i w hw ht hi (f ∘ CurrentPhysicalChartJets.chartMap a c)
    (CurrentPhysicalChartJets.composition_smoothNear ha hf)
  intro r hr
  exact (hm c _ (PhysicalClassBounds.commonLift_mem_cylindricalDomain ha h n d w hw)
    f hf _ (by positivity) hfb r hr).trans_eq (by ring)

theorem rotated_mode_bound {a b : ℝ} (ha : 0 < a) (Δ m : ℕ)
    (g A : ℝ) (e : ℕ) (hA : 0 ≤ A) (j : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ c : PolarCharts.Index, ∀ i : ActualPhaseJetBounds.CopyIndex B N0, ∀ w : SpaceTime,
      PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b → |w.1| ≤ 1 →
      fullMap a c n d w ∈ ActualPhaseJetBounds.phaseCell n i →
      ∀ f : Native → HarmonicCalculus.ComplexVector, SmoothNear f (nativeMap a c n d w) →
      (∀ r ≤ m, ‖iteratedFDeriv ℝ r f (nativeMap a c n d w)‖ ≤
        A*ChartScales.Q n^g*ChartScales.S n^e) →
      ‖iteratedFDeriv ℝ m (fun y => PhysicalGraphBounds.character (j:ℝ)
        (ActualCurrentCarrierJets.weightedPhase i.1 n (nativeMap a c n d y)) •
          CurrentPhysicalChartJets.rotated a c f (PhysicalWaveSum.commonLift h n d y)) w‖ ≤
        C*ChartScales.Q n^(g-(m:ℝ)*SharpPhysicalCarrier.derivativeCost h)*ChartScales.S n^p := by
  obtain ⟨M,hM,hm⟩ := CurrentPhysicalChartJets.rotated_composition_jets (b := b) ha m
  obtain ⟨C,hC,p,hc⟩ := lift_mode_bound (E := HarmonicCalculus.ComplexVector)
    (B := B) (N0 := N0) (b := b) ha Δ m g (M*A) e (by positivity) j
  refine ⟨C,hC,p,?_⟩
  intro n hn d hd c i w hw ht hi f hf hfb
  have hQ := ChartScales.Q_pos n
  have hS := PhysicalGraphBounds.S_ge_one (show 1 ≤ n by omega)
  have hx := PhysicalClassBounds.commonLift_mem_cylindricalDomain ha h n d w hw
  apply hc n hn d hd c i w hw ht hi (CurrentPhysicalChartJets.rotated a c f)
    (CurrentPhysicalChartJets.rotated_smoothNear ha hx hf)
  intro r hr
  exact (hm c _ hx f hf _ (by positivity) hfb r hr).trans_eq (by ring)


theorem modulated_smoothNear {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    {a : E → F} {Φ : E → ℝ} {x : E} (ha : SmoothNear a x) (hΦ : SmoothNear Φ x) (c : ℝ) :
    SmoothNear (fun y => PhysicalGraphBounds.character c (Φ y) • a y) x := by
  obtain ⟨U,hU,hxU,ha⟩ := ha
  obtain ⟨V,hV,hxV,hΦ⟩ := hΦ
  exact ⟨U∩V,hU.inter hV,⟨hxU,hxV⟩,
    ((PhysicalGraphBounds.character_smooth c).comp_contDiffOn (hΦ.mono inter_subset_right)).smul
      (ha.mono inter_subset_left)⟩

theorem rotationMap_complex_smul (z : PhysicalGraphBounds.Plane)
    (v : HarmonicCalculus.ComplexVector) (c : ℂ) :
    CartesianCopySource.rotationMap z (c • v) = c • CartesianCopySource.rotationMap z v := by
  ext i
  fin_cases i <;> simp [CartesianCopySource.rotationMap_apply, Pi.smul_apply, Complex.real_smul] <;> ring

theorem rescaled_log_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (g degree A K : ℝ) (p : ℕ) (hA : 0 ≤ A) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ q : ℝ, 0 < q →
      q/2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2*q →
      ∀ w : SpaceTime, ∀ f : SpaceTime → E, SmoothNear f w →
      ‖iteratedFDeriv ℝ m f w‖ ≤ A*ChartScales.Q n^g*ChartScales.S n^p →
      ∀ L : E →L[ℝ] F, ‖L‖ ≤ K →
      ‖iteratedFDeriv ℝ m (fun y => ChartScales.Q n^(-degree) • L (f y)) w‖ ≤
        C*q^(g-degree)*(1+|Real.log q|)^P := by
  obtain ⟨D,hD,P,hd⟩ := SharpLogWeights.chart_weight_bound (g-degree) p
  refine ⟨K*A*D,by positivity,P,?_⟩
  intro n hn q hq hlo hhi w f hf hfb L hL
  have hQ := ChartScales.Q_pos n
  have hS := PhysicalGraphBounds.S_ge_one hn
  have hLf : ContDiffAt ℝ m (L ∘ f) w :=
    L.contDiff.contDiffAt.comp w (hf.contDiffAt.of_le (nat_le_infty m))
  change ‖iteratedFDeriv ℝ m (fun y => (ChartScales.Q n^(-degree):ℝ) • (L ∘ f) y) w‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' hLf,
    norm_smul (ChartScales.Q n^(-degree):ℝ) (iteratedFDeriv ℝ m (L ∘ f) w),
    Real.norm_of_nonneg (Real.rpow_pos_of_pos hQ _).le,
    L.iteratedFDeriv_comp_left (hf.contDiffAt.of_le (nat_le_infty m)) le_rfl]
  have hj := (L.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul hL hfb (norm_nonneg _) hK)
  apply (mul_le_mul_of_nonneg_left hj (Real.rpow_pos_of_pos hQ _).le).trans
  have he : ChartScales.Q n^(-degree)*ChartScales.Q n^g = ChartScales.Q n^(g-degree) := by
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  calc
    _ = (K*A)*(ChartScales.Q n^(g-degree)*ChartScales.S n^(p:ℝ)) := by
      rw [Real.rpow_natCast, ← he]
      ring
    _ ≤ (K*A)*(D*q^(g-degree)*(1+|Real.log q|)^P) :=
      mul_le_mul_of_nonneg_left (hd n hn q hq hlo hhi) (mul_nonneg hK hA)
    _ = _ := by ring

end NavierStokes.SharpCurrentModeJets

section

/-! Bounds on the open profile annulus extend to its closed edges while
the physical similarity scale and the dyadic band remain fixed. -/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.CurrentPhysicalRadialClosure

open ProblemStatement PhysicalWaveSum ActualCurrentWaveSupport

/-- Change only the transverse coordinates. -/
def radialScale (w : SpaceTime) (c : ℝ) : SpaceTime :=
  (w.1, c • w.2 + ((1 - c) * w.2 2) • EuclideanSpace.single 2 1)

theorem radialScale_continuous (w : SpaceTime) : Continuous (radialScale w) := by
  exact continuous_const.prodMk ((continuous_id.smul continuous_const).add
    (((continuous_const.sub continuous_id).mul continuous_const).smul continuous_const))

@[simp] theorem radialScale_one (w : SpaceTime) : radialScale w 1 = w := by
  simp [radialScale]

@[simp] theorem radialScale_time (w : SpaceTime) (c : ℝ) : (radialScale w c).1 = w.1 := rfl

@[simp] theorem radialScale_axial (w : SpaceTime) (c : ℝ) :
    (radialScale w c).2 2 = w.2 2 := by
  simp only [radialScale, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.single_apply, ite_eq_left, mul_one]
  ring

@[simp] theorem radialScale_q (h : ℝ) (w : SpaceTime) (c : ℝ) :
    physicalQ h (radialScale w c) = physicalQ h w := by
  simp only [physicalQ, SimilarityProfile.q, AxisymmetricFields.profilePoint,
    radialScale_time, radialScale_axial]

theorem radialScale_projection (w : SpaceTime) (c : ℝ) :
    PhysicalGraphBounds.radialProjection (radialScale w c) =
      c • PhysicalGraphBounds.radialProjection w := by
  ext <;> simp [PhysicalGraphBounds.radialProjection_apply, radialScale]

theorem radialScale_radius (h : ℝ) (w : SpaceTime) {c : ℝ} (hc : 0 < c) :
    profileRadius h (radialScale w c) = c * profileRadius h w := by
  simp only [profileRadius, AnnularEndpoint.radius, radialScale_projection,
    PolarCharts.radius_smul hc, radialScale_q]
  ring

/-- Every closed-annulus point is a limit of strict-annulus points in its
same physical-scale fiber, hence in the same open dyadic band. -/
theorem closed_mem_closure_fiber {h a b : ℝ} (ha : 0 < a) (hab : a < b)
    {n : ℕ} {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band h n)
    (hr : profileRadius h w ∈ Icc a b) :
    w ∈ closure {y : SpaceTime | y ∈ ValidDyadicBandCover.band h n ∧
      physicalQ h y = physicalQ h w ∧ profileRadius h y ∈ Ioo a b} := by
  have hR : 0 < profileRadius h w := ha.trans_le hr.1
  let g : ℝ → SpaceTime := fun r => radialScale w (r / profileRadius h w)
  have hg : Continuous g := (radialScale_continuous w).comp
    (continuous_id.div_const _)
  have he : g (profileRadius h w) = w := by
    simp only [g, div_self hR.ne', radialScale_one]
  have hmap : MapsTo g (Ioo a b) {y : SpaceTime |
      y ∈ ValidDyadicBandCover.band h n ∧ physicalQ h y = physicalQ h w ∧
        profileRadius h y ∈ Ioo a b} := by
    intro r hrr
    have hc : 0 < r / profileRadius h w := div_pos (ha.trans hrr.1) hR
    have hband : g r ∈ ValidDyadicBandCover.band h n := by
      simpa only [ValidDyadicBandCover.band, mem_ofPred_eq, preterminal, g,
        radialScale_time, radialScale_q] using hw
    refine ⟨hband, radialScale_q _ _ _, ?_⟩
    change profileRadius h (radialScale w (r / profileRadius h w)) ∈ Ioo a b
    rwa [radialScale_radius h w hc, div_mul_cancel₀ _ hR.ne']
  have hcl : g (profileRadius h w) ∈ closure (g '' Ioo a b) := by
    apply mem_closure_image hg.continuousAt
    rw [closure_Ioo hab.ne]
    exact hr
  rw [he] at hcl
  exact closure_mono hmap.image_subset hcl

/-- A bound depending arbitrarily on the physical scale extends to both
annulus edges. No continuity assumption on the scale bound is needed. -/
theorem jet_bound_on_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h a b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    {n : ℕ} {f : SpaceTime → E}
    (hf : ContDiffOn ℝ ∞ f (ValidDyadicBandCover.band h n))
    (m : ℕ) (bound : ℝ → ℝ) {qcap : ℝ}
    (hb : ∀ y ∈ ValidDyadicBandCover.band h n, physicalQ h y ≤ qcap →
      profileRadius h y ∈ Ioo a b → ‖iteratedFDeriv ℝ m f y‖ ≤ bound (physicalQ h y))
    {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band h n)
    (hq : physicalQ h w ≤ qcap) (hr : profileRadius h w ∈ Icc a b) :
    ‖iteratedFDeriv ℝ m f w‖ ≤ bound (physicalQ h w) := by
  apply LocalPhysicalCopyBounds.jet_bound_at_closure
    (hf.contDiffAt ((ValidDyadicBandCover.band_open hh hh1 n).mem_nhds hw))
    (closed_mem_closure_fiber ha hab hw hr) m
  intro y hy
  simpa only [hy.2.1] using hb y hy.1 (hy.2.1 ▸ hq) hy.2.2

end NavierStokes.CurrentPhysicalRadialClosure


end

noncomputable section

namespace NavierStokes.SharpCurrentParticularBounds

open Set Function Filter ProblemStatement CorrectionStep
open CorrectionInitialization ActualCurrentParticularBounds
open CorrectionInitialization.ActualPrimary (h outgoing nominal)
open LocalPhysicalCopyBounds SharpCurrentModeJets
open SharpCurrentPhysicalPhase (nativeMap fullMap smoothNear_comp weightedPhase_smoothNear nativeMap_smoothNear)
open scoped Topology ContDiff BigOperators

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (ActualInitialization.Index B N0)}

private theorem commonGap_bound (n : ℕ) :
    CurrentPhysicalModeGerms.commonGap n ≤ CommonWindow.gap h := by
  have hn := CommonWindow.native_le_index_add h outgoing.data.h_pos.le n
  unfold CurrentPhysicalModeGerms.commonGap
  omega

/-- The sharp bound first on the strict profile annulus, where the native
coefficient class is defined. The phase is used only on its actual copy cell. -/
theorem potential_mode_strict_bound (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℤ) (hj : j ≠ 0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ (l : Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, PhysicalWaveSum.physicalQ h w ≤ 1 →
      ActualCurrentWaveSupport.profileRadius h w ∈
        Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotentialMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (h * (σ + 1) - h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h) *
            (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ P := by
  let y := ActualCycleParameters.particularState x
  have hcar := ActualParticularCycleData.preservesCarriers H
  have hin := ActualParticularCycleData.native_inputSupport H
  have hsrc := ActualParticularCycleData.native_source_class H j hj
  have hf := actual_potential_coefficient_class y hcar hin hN j hj hsrc
  obtain ⟨A, hA, e, hab⟩ := (native_source_bounds hf).chart_bound m
  have hg : h * ((1 / 2 + σ) + 1 / 2) = h * (σ + 1) := by ring
  rw [hg] at hab
  obtain ⟨D, hD, p, hd⟩ := rotated_mode_bound (B := B) (N0 := N0)
    (b := CurrentModeGeometry.chartOuter) CurrentModeGeometry.chartInner_pos
    (CommonWindow.gap h) m (h * (σ + 1)) A e hA j
  obtain ⟨C, hC, P, hc⟩ := rescaled_log_bound (E := HarmonicCalculus.ComplexVector)
    (F := Space) m (h * (σ + 1) - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h)
    h D 3 p hD (by norm_num)
  refine ⟨C, hC, P, ?_⟩
  intro l n hn w hw hq hr
  have hqpos := PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1
  have hann := CurrentModeGeometry.scaledRadial_mem_annulus n hw ⟨hr.1.le, hr.2.le⟩
  let c := PhysicalWaveSum.chooseChart CurrentModeGeometry.chartInner (PhysicalGraphBounds.scaledRadial n w)
  let d := CurrentPhysicalModeGerms.commonGap n
  have hchart := PhysicalWaveSum.chooseChart_valid CurrentModeGeometry.chartInner_pos hann
  have hzD := CurrentModeGeometry.point_mem_nativeDomain n CurrentModeGeometry.chartInner_pos c hw hchart
  have hzR := CurrentModeGeometry.point_profileRadius n CurrentModeGeometry.chartInner_pos c hw.1 hchart
  have hz : nativeMap CurrentModeGeometry.chartInner c n d w ∈ nativeStrip.domain := by
    apply ActualCurrentParticularPhysical.nativeStrip_mem hzD
    rwa [hzR]
  have haxis := PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree CurrentModeGeometry.chartInner_pos hann)
  let f := potentialCoefficient y l j n
  let F : SpaceTime → HarmonicCalculus.ComplexVector := fun z =>
    PhysicalGraphBounds.character (j : ℝ) (ActualCurrentCarrierJets.weightedPhase l n
      (nativeMap CurrentModeGeometry.chartInner c n d z)) •
        CurrentPhysicalChartJets.rotated CurrentModeGeometry.chartInner c f (PhysicalWaveSum.commonLift h n d z)
  have hmode : ActualCurrentParticularPhysical.localPotentialMode y l j n =ᶠ[𝓝 w]
      (fun z => ChartScales.Q n ^ (-h) • CurrentPhysicalChartJets.realVectorCLM (F z)) := by
    have he := CurrentPhysicalModeGerms.localPotentialMode_germ y l j
      (ActualParticularStageControls.preserves_frequency hcar l) n CurrentModeGeometry.chartInner_pos c hchart
    filter_upwards [he] with z hz
    rw [hz, actual_nativePotential_eq_character y hcar]
    simp only [F, f, nativeMap, Function.comp_def, CurrentPhysicalChartJets.rotated,
      CurrentPhysicalChartJets.rotation, CurrentPhysicalChartJets.chartMap,
      CurrentPhysicalChartJets.realVectorCLM_apply, rotationMap_complex_smul]
    rfl
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hmode m]
  rcases common_control_or_zero y hin hN l j n hz with ⟨k, hk⟩ | hzero
  · have hi : fullMap CurrentModeGeometry.chartInner c n d w ∈ ActualPhaseJetBounds.phaseCell n (l,k) :=
      ActualParticularStageControls.controlPatch_subset_padded l n k hk
    have hnear : SmoothNear f (nativeMap CurrentModeGeometry.chartInner c n d w) :=
      ⟨_, nativeStrip.isOpen_domain, hz, hf.smooth l n⟩
    have hjets := hd n hn d (commonGap_bound n) c (l,k) w hann
      (PhysicalStageBounds.abs_time_le_one outgoing.data.h_pos outgoing.data.h_lt_half hw.1 hq)
      hi f hnear (hab l n hn _ hz)
    have hrot := CurrentPhysicalChartJets.rotated_smoothNear CurrentModeGeometry.chartInner_pos
      (PhysicalClassBounds.commonLift_mem_cylindricalDomain CurrentModeGeometry.chartInner_pos h n d w hann) hnear
    have hFn : SmoothNear F w := modulated_smoothNear
      (smoothNear_comp hrot (commonLift_smoothNear n d haxis))
      (weightedPhase_smoothNear CurrentModeGeometry.chartInner_pos c n d haxis hi) (j : ℝ)
    have he := hc n (by omega) _ hqpos (CurrentModeGeometry.band_q_comparison n hw).1
      (CurrentModeGeometry.band_q_comparison n hw).2 w F hFn hjets
      CurrentPhysicalChartJets.realVectorCLM CurrentPhysicalChartJets.norm_realVectorCLM_le
    have heq : h * (σ + 1) - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h - h =
        h * (σ + 1) - h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h := by ring
    simpa only [heq] using he
  · have h0 := hzero.1.comp_tendsto
      (nativeMap_smoothNear CurrentModeGeometry.chartInner_pos c n d haxis).contDiffAt.continuousAt
    have hF0 : F =ᶠ[𝓝 w] (fun _ => 0) := by
      filter_upwards [h0] with z hz
      simp only [F, CurrentPhysicalChartJets.rotated, f, nativeMap, Function.comp_def] at hz ⊢
      rw [hz, map_zero, smul_zero]
    have hscaled : (fun z => ChartScales.Q n ^ (-h) • CurrentPhysicalChartJets.realVectorCLM (F z))
        =ᶠ[𝓝 w] (fun _ => 0) := by
      filter_upwards [hF0] with z hz
      rw [hz, map_zero, smul_zero]
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hscaled m]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos hqpos _).le) (by positivity)

theorem pressure_mode_strict_bound (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℤ) (hj : j ≠ 0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ (l : Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, PhysicalWaveSum.physicalQ h w ≤ 1 →
      ActualCurrentWaveSupport.profileRadius h w ∈
        Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressureMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (h * (σ + 1) - 2 * CoordinateAlgebra.A h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h) *
            (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ P := by
  let y := ActualCycleParameters.particularState x
  have hcar := ActualParticularCycleData.preservesCarriers H
  have hin := ActualParticularCycleData.native_inputSupport H
  have hsrc := ActualParticularCycleData.native_source_class H j hj
  have hf := actual_pressure_coefficient_class y hcar hin hN j hj hsrc
  obtain ⟨A, hA, e, hab⟩ := (native_source_bounds hf).chart_bound m
  have hg : h * ((1 / 2 + σ) + 1 / 2) = h * (σ + 1) := by ring
  rw [hg] at hab
  obtain ⟨D, hD, p, hd⟩ := native_mode_bound (E := ℂ) (B := B) (N0 := N0)
    (b := CurrentModeGeometry.chartOuter) CurrentModeGeometry.chartInner_pos
    (CommonWindow.gap h) m (h * (σ + 1)) A e hA j
  obtain ⟨C, hC, P, hc⟩ := rescaled_log_bound (E := ℂ)
    (F := ℝ) m (h * (σ + 1) - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h)
    (2 * CoordinateAlgebra.A h) D 1 p hD zero_le_one
  refine ⟨C, hC, P, ?_⟩
  intro l n hn w hw hq hr
  have hqpos := PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1
  have hann := CurrentModeGeometry.scaledRadial_mem_annulus n hw ⟨hr.1.le, hr.2.le⟩
  let c := PhysicalWaveSum.chooseChart CurrentModeGeometry.chartInner (PhysicalGraphBounds.scaledRadial n w)
  let d := CurrentPhysicalModeGerms.commonGap n
  have hchart := PhysicalWaveSum.chooseChart_valid CurrentModeGeometry.chartInner_pos hann
  have hzD := CurrentModeGeometry.point_mem_nativeDomain n CurrentModeGeometry.chartInner_pos c hw hchart
  have hzR := CurrentModeGeometry.point_profileRadius n CurrentModeGeometry.chartInner_pos c hw.1 hchart
  have hz : nativeMap CurrentModeGeometry.chartInner c n d w ∈ nativeStrip.domain := by
    apply ActualCurrentParticularPhysical.nativeStrip_mem hzD
    rwa [hzR]
  have haxis := PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree CurrentModeGeometry.chartInner_pos hann)
  let f := (ActualParticularStageControls.data y l j).common.pressure n
  let F : SpaceTime → ℂ := fun z =>
    PhysicalGraphBounds.character (j : ℝ) (ActualCurrentCarrierJets.weightedPhase l n
      (nativeMap CurrentModeGeometry.chartInner c n d z)) •
        f (nativeMap CurrentModeGeometry.chartInner c n d z)
  have hmode : ActualCurrentParticularPhysical.localPressureMode y l j n =ᶠ[𝓝 w]
      (fun z => ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h)) • Complex.reCLM (F z)) := by
    have he := CurrentPhysicalModeGerms.localPressureMode_germ y l j
      (ActualParticularStageControls.preserves_frequency hcar l) n CurrentModeGeometry.chartInner_pos c hchart
    filter_upwards [he] with z hz
    rw [hz, actual_nativePressure_eq_character y hcar]
    simp only [F, f, nativeMap, Function.comp_def, CurrentPhysicalChartJets.chartMap,
      neg_mul, smul_eq_mul]
    rfl
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hmode m]
  rcases common_control_or_zero y hin hN l j n hz with ⟨k, hk⟩ | hzero
  · have hi : fullMap CurrentModeGeometry.chartInner c n d w ∈ ActualPhaseJetBounds.phaseCell n (l,k) :=
      ActualParticularStageControls.controlPatch_subset_padded l n k hk
    have hnear : SmoothNear f (nativeMap CurrentModeGeometry.chartInner c n d w) :=
      ⟨_, nativeStrip.isOpen_domain, hz, hf.smooth l n⟩
    have hjets := hd n hn d (commonGap_bound n) c (l,k) w hann
      (PhysicalStageBounds.abs_time_le_one outgoing.data.h_pos outgoing.data.h_lt_half hw.1 hq)
      hi f hnear (hab l n hn _ hz)
    have hFn : SmoothNear F w := modulated_smoothNear
      (smoothNear_comp hnear (nativeMap_smoothNear CurrentModeGeometry.chartInner_pos c n d haxis))
      (weightedPhase_smoothNear CurrentModeGeometry.chartInner_pos c n d haxis hi) (j : ℝ)
    have he := hc n (by omega) _ hqpos (CurrentModeGeometry.band_q_comparison n hw).1
      (CurrentModeGeometry.band_q_comparison n hw).2 w F hFn hjets
      Complex.reCLM (by
        apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro z
        simpa only [Complex.reCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_re_le_norm z)
    have heq : h * (σ + 1) - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h - 2 * CoordinateAlgebra.A h =
        h * (σ + 1) - 2 * CoordinateAlgebra.A h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h := by ring
    simpa only [heq] using he
  · have h0 := hzero.2.comp_tendsto
      (nativeMap_smoothNear CurrentModeGeometry.chartInner_pos c n d haxis).contDiffAt.continuousAt
    have hF0 : F =ᶠ[𝓝 w] (fun _ => 0) := by
      filter_upwards [h0] with z hz
      change PhysicalGraphBounds.character _ _ • f (nativeMap CurrentModeGeometry.chartInner c n d z) = 0
      change f (nativeMap CurrentModeGeometry.chartInner c n d z) = 0 at hz
      rw [hz, smul_zero]
    have hscaled : (fun z => ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h)) • Complex.reCLM (F z))
        =ᶠ[𝓝 w] (fun _ => 0) := by
      filter_upwards [hF0] with z hz
      rw [hz, map_zero, smul_zero]
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hscaled m]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos hqpos _).le) (by positivity)

/-- The full valid-band bound for the actual current potential mode. Closed
annulus edges follow by continuity in a fixed physical-scale fiber. -/
theorem current_potential_mode_bound (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℤ) (hj : j ≠ 0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ (l : Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotentialMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (h * (σ + 1) - h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h) *
            (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ P := by
  obtain ⟨C, hC, P, hb⟩ := potential_mode_strict_bound H hN j hj m
  refine ⟨C, hC, P, ?_⟩
  intro l n hn w hw hq
  by_cases hr : ActualCurrentWaveSupport.profileRadius h w ∈
      Icc (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)
  · exact CurrentPhysicalRadialClosure.jet_bound_on_closed outgoing.data.h_pos
      outgoing.data.h_lt_half (PrimaryTargetBounds.leftRadius_pos nominal)
      (PrimaryTargetBounds.radii_ordered nominal)
      (CurrentParticularLabelBounds.current_modes_contDiffOn H hN l j hj n).1 m
      (fun q => C * q ^ (h * (σ + 1) - h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h) *
        (1 + |Real.log q|) ^ P) (hb l n hn) hw hq hr
  · have hs := (ActualCurrentWaveSupport.current_mode_annulus hN
      (ActualCycleParameters.particularState x) l (H.inputSupport (l.2,l.1)) j 0).1
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq
      (hs.zero_germ outgoing.data.h_pos outgoing.data.h_lt_half (Nat.zero_le n) hw hr) m]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    have hqpos := PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1
    exact mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos hqpos _).le) (by positivity)

/-- The pressure estimate has its literal quadratic physical scale and the
same per-derivative loss as the potential estimate. -/
theorem current_pressure_mode_bound (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℤ) (hj : j ≠ 0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ (l : Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressureMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (h * (σ + 1) - 2 * CoordinateAlgebra.A h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h) *
            (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ P := by
  obtain ⟨C, hC, P, hb⟩ := pressure_mode_strict_bound H hN j hj m
  refine ⟨C, hC, P, ?_⟩
  intro l n hn w hw hq
  by_cases hr : ActualCurrentWaveSupport.profileRadius h w ∈
      Icc (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)
  · exact CurrentPhysicalRadialClosure.jet_bound_on_closed outgoing.data.h_pos
      outgoing.data.h_lt_half (PrimaryTargetBounds.leftRadius_pos nominal)
      (PrimaryTargetBounds.radii_ordered nominal)
      (CurrentParticularLabelBounds.current_modes_contDiffOn H hN l j hj n).2 m
      (fun q => C * q ^ (h * (σ + 1) - 2 * CoordinateAlgebra.A h -
        (m : ℝ) * SharpPhysicalCarrier.derivativeCost h) * (1 + |Real.log q|) ^ P)
      (hb l n hn) hw hq hr
  · have hs := (ActualCurrentWaveSupport.current_mode_annulus hN
      (ActualCycleParameters.particularState x) l (H.inputSupport (l.2,l.1)) j 0).2
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq
      (hs.zero_germ outgoing.data.h_pos outgoing.data.h_lt_half (Nat.zero_le n) hw hr) m]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    have hqpos := PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1
    exact mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos hqpos _).le) (by positivity)

end NavierStokes.SharpCurrentParticularBounds

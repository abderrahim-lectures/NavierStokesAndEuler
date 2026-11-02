import NavierStokes.GluedStageEstimates
import NavierStokes.SharpPhysicalLogBounds
import NavierStokes.PhysicalStageBounds
import NavierStokes.LocalPhysicalCopyBounds
import NavierStokes.SharpPhysicalLoss
import NavierStokes.ActualPhysicalStageBounds
import NavierStokes.LocalMeanPhysicalBounds

/-! Merged from `NavierStokes.SharpMeanStageBounds` (in a section, so its `open`s cannot leak). -/
/-! Merged from `NavierStokes.SharpMeanJetBounds` (in a section, so its `open`s cannot leak). -/
section
noncomputable section
namespace NavierStokes.SharpMeanJetBounds
open Set Function Filter ProblemStatement PhysicalWaveSum LocalPhysicalCopyBounds
open PhysicalMeanJetBounds LocalMeanPhysicalBounds
open scoped Topology ContDiff BigOperators

theorem common_stripped_log_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h a b : ℝ} (hh : 0 ≤ h) (_hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (Δ m : ℕ) (g e A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b → |w.1| ≤ 1 →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ f : LiftPoint → E, ContDiff ℝ ∞ f →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (commonLift h n d w)‖ ≤
        A * ChartScales.Q n ^ g * ChartScales.S n ^ e) →
      ‖iteratedFDeriv ℝ m (f ∘ commonLift h n d) w‖ ≤
        C*q^(g-(m:ℝ)*(1+h))*(1+|Real.log q|)^P := by
  have hcover : 0 ≤ coverBound Δ := zero_le_one.trans (coverBound_ge_one Δ)
  obtain ⟨K,hK,hgraph⟩ := SharpGraphBounds.graphRestriction_jet_bound (E := E) (b := b) hh ha m
  obtain ⟨D,hD,P,hweight⟩ := SharpLogWeights.chart_weight_bound (g-(m:ℝ)*(1+h)) e
  let A' := A*coverBound Δ^m
  have hA' : 0 ≤ A' := by dsimp [A']; positivity
  refine ⟨K*A'*D, by positivity, P, ?_⟩
  intro n hn d hd w hw ht q hq hlo hhi f hf hfb
  have hQ := ChartScales.Q_pos n
  have hS := ChartScales.S_pos (show 1 ≤ n by omega)
  have hjet : ∀ i ≤ m, ‖iteratedFDeriv ℝ i (f ∘ downLift d) (PhysicalGraphBounds.physicalLift h n w)‖ ≤
      A'*ChartScales.Q n^g*ChartScales.S n^e := by
    intro i hi
    exact (downLift_jet_bound hf hd (PhysicalGraphBounds.physicalLift h n w)
      (B := A*ChartScales.Q n^g*ChartScales.S n^e) (by positivity) hfb i hi).trans_eq (by dsimp [A']; ring)
  have hb := hgraph n hn w hw ht (f ∘ downLift d) (hf.comp (downLift d).contDiff)
    _ (by positivity) hjet
  apply hb.trans
  have hpow : ChartScales.Q n^g*ChartScales.Q n^(-(m:ℝ)*(1+h)) = ChartScales.Q n^(g-(m:ℝ)*(1+h)) := by
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  calc
    _ = (K*A')*(ChartScales.Q n^(g-(m:ℝ)*(1+h))*ChartScales.S n^e) := by
      rw [← hpow]
      ring
    _ ≤ (K*A')*(D*q^(g-(m:ℝ)*(1+h))*(1+|Real.log q|)^P) :=
      mul_le_mul_of_nonneg_left (hweight n (by omega) q hq hlo hhi) (mul_nonneg hK.le hA')
    _ = _ := by ring

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem common_stripped_log_bound_local {h a b : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (Δ m : ℕ) (g e A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b → |w.1| ≤ 1 →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ f : LiftPoint → E, SmoothNear f (commonLift h n d w) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (commonLift h n d w)‖ ≤
        A * ChartScales.Q n ^ g * ChartScales.S n ^ e) →
      ‖iteratedFDeriv ℝ m (f ∘ commonLift h n d) w‖ ≤
        C*q^(g-(m:ℝ)*(1+h))*(1+|Real.log q|)^P := by
  obtain ⟨C, hC, P, hb⟩ := common_stripped_log_bound (E := E) (b := b)
    hh hh1 ha Δ m g e A hA
  refine ⟨C, hC, P, ?_⟩
  intro n hn d hd w hann ht q hq hlo hhi f hf hjet
  obtain ⟨F, hF, he⟩ := hf.exists_global_germ
  have haxis := PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree ha hann)
  have he' := he.comp_tendsto (commonLift_smoothAt h n d haxis).continuousAt
  rw [iteratedFDeriv_eq_of_eventuallyEq he' m]
  apply hb n hn d hd w hann ht q hq hlo hhi F hF
  intro i hi
  rw [← iteratedFDeriv_eq_of_eventuallyEq he i]
  exact hjet i hi

noncomputable def meanLoss (h degree : ℝ) (m : ℕ) : ℝ := (m:ℝ)*(1+h)+degree

theorem bandField_log_bound {h a b : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (Δ m : ℕ) (gain degree e A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b → |w.1| ≤ 1 →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ f : Point → E, SmoothNear f (graph h n d w) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (graph h n d w)‖ ≤
        A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) →
      ‖iteratedFDeriv ℝ m (bandField h n d degree f) w‖ ≤
        C*q^(gain-meanLoss h degree m)*(1+|Real.log q|)^P := by
  obtain ⟨B, hB, hBj⟩ := PhysicalClassBounds.cylindricalMap_positiveJets (b := b) ha m
  let A' : ℝ := (m.factorial : ℝ) * A * B ^ m
  have hA' : 0 ≤ A' := by dsimp [A']; positivity
  obtain ⟨C, hC, P, hb⟩ := common_stripped_log_bound_local (E := E) (b := b)
    hh hh1 ha Δ m (gain - degree) e A' hA'
  refine ⟨C, hC, P, ?_⟩
  intro n hn d hd w hann ht q hq hlo hhi f hf hjet
  obtain ⟨F, hF, he⟩ := hf.exists_global_germ
  have hx := PhysicalClassBounds.commonLift_mem_cylindricalDomain ha h n d w hann
  have hg : ContDiffOn ℝ ∞ (F ∘ PhysicalClassBounds.cylindricalMap)
      (PhysicalClassBounds.cylindricalDomain a b) :=
    hF.comp_contDiffOn (PhysicalClassBounds.cylindricalMap_smooth ha)
  let u : LiftPoint → E := fun x => (ChartScales.Q n ^ (-degree)) • F (PhysicalClassBounds.cylindricalMap x)
  have hu : SmoothNear u (commonLift h n d w) :=
    SmoothNear.of_open (PhysicalClassBounds.cylindricalDomain_open a b)
      (hg.const_smul _) hx
  have he' : bandField h n d degree f =ᶠ[𝓝 w] u ∘ commonLift h n d := by
    filter_upwards [he.comp_tendsto (graph_smoothAt ha h n d hann).continuousAt] with z hz
    exact congrArg (fun v => (ChartScales.Q n ^ (-degree)) • v) hz
  rw [iteratedFDeriv_eq_of_eventuallyEq he' m]
  have hbound := hb n hn d hd w hann ht q hq hlo hhi u hu
  have hqN := ChartScales.Q_pos n
  have hSN := ChartScales.S_pos (show 1 ≤ n by omega)
  have hab : 0 ≤ A * ChartScales.Q n ^ gain * ChartScales.S n ^ e := by positivity
  have hFjet : ∀ i ≤ m, ‖iteratedFDeriv ℝ i F (graph h n d w)‖ ≤
      A * ChartScales.Q n ^ gain * ChartScales.S n ^ e := by
    intro i hi
    rw [← iteratedFDeriv_eq_of_eventuallyEq he i]
    exact hjet i hi
  have hcomp := PhysicalClassBounds.composition_jet_bound hF
    (PhysicalClassBounds.cylindricalDomain_open a b) (PhysicalClassBounds.cylindricalMap_smooth ha)
    hx m hab hB hFjet (hBj _ hx)
  have huc : ∀ i ≤ m, ‖iteratedFDeriv ℝ i u (commonLift h n d w)‖ ≤
      A' * ChartScales.Q n ^ (gain - degree) * ChartScales.S n ^ e := by
    intro i hi
    have hnear := hg.contDiffAt ((PhysicalClassBounds.cylindricalDomain_open a b).mem_nhds hx)
    change ‖iteratedFDeriv ℝ i (fun x => (ChartScales.Q n ^ (-degree)) •
      (F ∘ PhysicalClassBounds.cylindricalMap) x) (commonLift h n d w)‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hnear.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)),
      norm_smul (ChartScales.Q n ^ (-degree))
        (iteratedFDeriv ℝ i (F ∘ PhysicalClassBounds.cylindricalMap) (commonLift h n d w)),
      Real.norm_of_nonneg (Real.rpow_pos_of_pos hqN (-degree)).le]
    calc
      _ ≤ ChartScales.Q n ^ (-degree) * ((m.factorial : ℝ) *
          (A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) * B ^ m) :=
        mul_le_mul_of_nonneg_left (hcomp i hi) (Real.rpow_pos_of_pos hqN _).le
      _ = _ := by dsimp [A']; rw [Real.rpow_sub hqN, Real.rpow_neg hqN.le]; ring
  have hexp : gain-degree-(m:ℝ)*(1+h) = gain-meanLoss h degree m := by
    unfold meanLoss
    ring
  simpa only [hexp] using hbound huc

theorem bandAngularField_log_bound {h a b : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (Δ m : ℕ) (gain degree e A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b → |w.1| ≤ 1 →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ f : Point → ℝ, SmoothNear f (graph h n d w) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (graph h n d w)‖ ≤
        A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) →
      ‖iteratedFDeriv ℝ m (bandAngularField h n d degree f) w‖ ≤
        C*q^(gain-meanLoss h degree m)*(1+|Real.log q|)^P := by
  obtain ⟨B, hB, hBj⟩ := PhysicalClassBounds.cylindricalMap_positiveJets (b := b) ha m
  obtain ⟨V, hV, hVj⟩ := angularVector_lift_jet_bound (b := b) ha m
  let A' : ℝ := (2 : ℝ) ^ m * ((m.factorial : ℝ) * A * B ^ m) * V
  have hA' : 0 ≤ A' := by dsimp [A']; positivity
  obtain ⟨C, hC, P, hb⟩ := common_stripped_log_bound_local (E := Space) (b := b)
    hh hh1 ha Δ m (gain - degree) e A' hA'
  refine ⟨C, hC, P, ?_⟩
  intro n hn d hd w hann ht q hq hlo hhi f hf hjet
  obtain ⟨F, hF, he⟩ := hf.exists_global_germ
  have hx := PhysicalClassBounds.commonLift_mem_cylindricalDomain ha h n d w hann
  have hg : ContDiffOn ℝ ∞ (F ∘ PhysicalClassBounds.cylindricalMap)
      (PhysicalClassBounds.cylindricalDomain a b) :=
    hF.comp_contDiffOn (PhysicalClassBounds.cylindricalMap_smooth ha)
  let v : LiftPoint → Space := fun x => F (PhysicalClassBounds.cylindricalMap x) •
    angularVector (PhysicalGraphBounds.liftXY x)
  have hv : ContDiffOn ℝ ∞ v (PhysicalClassBounds.cylindricalDomain a b) :=
    hg.smul (angularVector_lift_smooth ha)
  let u : LiftPoint → Space := fun x => (ChartScales.Q n ^ (-degree)) • v x
  have hu : SmoothNear u (commonLift h n d w) :=
    SmoothNear.of_open (PhysicalClassBounds.cylindricalDomain_open a b)
      (hv.const_smul _) hx
  have he' : bandAngularField h n d degree f =ᶠ[𝓝 w] u ∘ commonLift h n d := by
    filter_upwards [he.comp_tendsto (graph_smoothAt ha h n d hann).continuousAt] with z hz
    change (ChartScales.Q n ^ (-degree) * f (graph h n d z)) •
      angularVector (PhysicalGraphBounds.radialProjection z) =
        ChartScales.Q n ^ (-degree) • (F (graph h n d z) •
          angularVector (PhysicalGraphBounds.liftXY (commonLift h n d z)))
    rw [PhysicalClassBounds.liftXY_commonLift, angularVector_scaledRadial]
    change f (graph h n d z) = F (graph h n d z) at hz
    simp only [hz, smul_smul]
  rw [iteratedFDeriv_eq_of_eventuallyEq he' m]
  have hbound := hb n hn d hd w hann ht q hq hlo hhi u hu
  have hqN := ChartScales.Q_pos n
  have hSN := ChartScales.S_pos (show 1 ≤ n by omega)
  have hab : 0 ≤ A * ChartScales.Q n ^ gain * ChartScales.S n ^ e := by positivity
  have hFjet : ∀ i ≤ m, ‖iteratedFDeriv ℝ i F (graph h n d w)‖ ≤
      A * ChartScales.Q n ^ gain * ChartScales.S n ^ e := by
    intro i hi
    rw [← iteratedFDeriv_eq_of_eventuallyEq he i]
    exact hjet i hi
  have hcomp := PhysicalClassBounds.composition_jet_bound hF
    (PhysicalClassBounds.cylindricalDomain_open a b) (PhysicalClassBounds.cylindricalMap_smooth ha)
    hx m hab hB hFjet (hBj _ hx)
  have huc : ∀ i ≤ m, ‖iteratedFDeriv ℝ i u (commonLift h n d w)‖ ≤
      A' * ChartScales.Q n ^ (gain - degree) * ChartScales.S n ^ e := by
    intro i hi
    have hnear := hv.contDiffAt ((PhysicalClassBounds.cylindricalDomain_open a b).mem_nhds hx)
    change ‖iteratedFDeriv ℝ i (fun x => (ChartScales.Q n ^ (-degree)) • v x)
      (commonLift h n d w)‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hnear.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)),
      norm_smul (ChartScales.Q n ^ (-degree)) (iteratedFDeriv ℝ i v (commonLift h n d w)),
      Real.norm_of_nonneg (Real.rpow_pos_of_pos hqN (-degree)).le]
    have hprod := smul_jet_bound (PhysicalClassBounds.cylindricalDomain_open a b)
      hg (angularVector_lift_smooth ha) hx hi
      (by positivity : 0 ≤ (m.factorial : ℝ) *
        (A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) * B ^ m)
      (zero_le_one.trans hV) hcomp (hVj _ hx)
    calc
      _ ≤ ChartScales.Q n ^ (-degree) * ((2 : ℝ) ^ m * ((m.factorial : ℝ) *
          (A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) * B ^ m) * V) :=
        mul_le_mul_of_nonneg_left hprod (Real.rpow_pos_of_pos hqN _).le
      _ = _ := by dsimp [A']; rw [Real.rpow_sub hqN, Real.rpow_neg hqN.le]; ring
  have hexp : gain-degree-(m:ℝ)*(1+h) = gain-meanLoss h degree m := by
    unfold meanLoss
    ring
  simpa only [hexp] using hbound huc

variable {h degree a b : ℝ} {N Δ : ℕ} {U : Set PhysicalGraphBounds.Plane}

theorem field_log_bound (D : CoherentFamily h degree N Δ U E)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {gain : ℝ} (hj : NativeJets N U gain D.native)
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      physicalQ h w ≤ ChartScales.Q N →
      ‖iteratedFDeriv ℝ m D.field w‖ ≤ C*physicalQ h w^(gain-meanLoss h degree m)*(1+|Real.log (physicalQ h w)|)^P := by
  obtain ⟨A, hA, e, hjet⟩ := hj m
  obtain ⟨C, hC, P, hb⟩ := bandField_log_bound (E := E) (b := 2 * b)
    hh.le hh1.le (div_pos ha (by norm_num : (0 : ℝ) < 4)) Δ m gain degree e A hA
  refine ⟨C, hC, P, ?_⟩
  intro w hw ht hsmall
  have hq := physicalQ_pos hh hh1 hw
  by_cases hts : w ∈ tsupport D.field
  · obtain ⟨n, hn, hqn, hnq, hu, he⟩ := exists_field_germ D hh hh1 hU hcover hw hsmall
    have hlo : physicalQ h w / 2 ≤ ChartScales.Q n := by linarith
    have hann := D.annulus_on_tsupport hh hh1 ha hab hU hs n hn hw hu hlo hnq.le hts
    rw [iteratedFDeriv_eq_of_eventuallyEq he m]
    apply hb n (hN.trans hn) (D.gap n) (D.gap_le n hn) w hann ht
      (physicalQ h w) hq hlo hnq.le (D.native n)
    · exact SmoothNear.of_open (PhysicalMeanDomain.slowDomain_open hU) (hsm n hn) hu
    · intro j hjm
      simpa only [Real.rpow_natCast] using hjet n hn _ hu j hjm
  · rw [jet_zero_off_tsupport _ _ hts, norm_zero]
    positivity

theorem angularField_log_bound (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {gain : ℝ} (hj : NativeJets N U gain D.native)
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      physicalQ h w ≤ ChartScales.Q N →
      ‖iteratedFDeriv ℝ m D.angularField w‖ ≤ C*physicalQ h w^(gain-meanLoss h degree m)*(1+|Real.log (physicalQ h w)|)^P := by
  obtain ⟨A, hA, e, hjet⟩ := hj m
  obtain ⟨C, hC, P, hb⟩ := bandAngularField_log_bound (b := 2 * b)
    hh.le hh1.le (div_pos ha (by norm_num : (0 : ℝ) < 4)) Δ m gain degree e A hA
  refine ⟨C, hC, P, ?_⟩
  intro w hw ht hsmall
  have hq := physicalQ_pos hh hh1 hw
  by_cases hts : w ∈ tsupport D.field
  · obtain ⟨n, hn, hqn, hnq, hu, he⟩ := exists_angularField_germ D hh hh1 hU hcover hw hsmall
    have hlo : physicalQ h w / 2 ≤ ChartScales.Q n := by linarith
    have hann := D.annulus_on_tsupport hh hh1 ha hab hU hs n hn hw hu hlo hnq.le hts
    rw [iteratedFDeriv_eq_of_eventuallyEq he m]
    apply hb n (hN.trans hn) (D.gap n) (D.gap_le n hn) w hann ht
      (physicalQ h w) hq hlo hnq.le (D.native n)
    · exact SmoothNear.of_open (PhysicalMeanDomain.slowDomain_open hU) (hsm n hn) hu
    · intro j hjm
      simpa only [Real.rpow_natCast] using hjet n hn _ hu j hjm
  · rw [jet_zero_off_tsupport _ _
      (notMem_tsupport_iff_eventuallyEq.mpr (D.angularField_zero_germ hts)), norm_zero]
    positivity


theorem curl_angularField_log_bound (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {gain : ℝ} (hj : NativeJets N U gain D.native)
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ w : SpaceTime, w ∈ physicalDomain h N → |w.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl D.angularField) w‖ ≤
        C*physicalQ h w^(gain-meanLoss h degree (m+1))*(1+|Real.log (physicalQ h w)|)^P := by
  obtain ⟨C, hC, P, hb⟩ := angularField_log_bound D hh hh1 ha hab hN hU hcover hsm hs hj (m + 1)
  refine ⟨‖PhysicalClassBounds.jointCurl‖ * C,
    mul_nonneg (norm_nonneg PhysicalClassBounds.jointCurl) hC, P, ?_⟩
  intro w hw ht
  exact (PhysicalClassBounds.spatialCurl_jet_bound (physicalDomain_open hh hh1 N)
    (angularField_smooth D hh hh1 ha hab hU hcover hsm hs) hw m).trans
    ((mul_le_mul_of_nonneg_left (hb w hw.1 ht hw.2.le)
      (norm_nonneg PhysicalClassBounds.jointCurl)).trans_eq (by ring))

end NavierStokes.SharpMeanJetBounds
end

/-! Merged from `NavierStokes.SharpPhysicalCopyBounds` (in a section, so its `open`s cannot leak). -/
section
noncomputable section
namespace NavierStokes.SharpPhysicalCopyBounds
open Set Function Filter ProblemStatement PhysicalWaveSum PhysicalCopyBounds LocalPhysicalCopyBounds
open SharpPhysicalPhase SharpPhysicalCarrier
open scoped Topology ContDiff BigOperators

theorem common_carrier_log_bound {h a b Z r0 P B eBase : ℝ}
    (hh : 0 ≤ h) (_hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (_hZ : 0 ≤ Z) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B) (heBase : 0 ≤ eBase)
    (Δ m : ℕ) (g eAmp A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b →
      |w.1| ≤ 1 → ‖PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h n w)‖ ≤ Z →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ (c : CarrierData) (amp : LiftPoint → ℂ) (j : ℤ),
      |c.angular| ≤ P → |c.axial| ≤ P → |c.radial| ≤ P →
      |PhysicalGraphBounds.etaCoordinate (PhysicalGraphBounds.nativeGraph h n w - c.center)| ≤ r0 →
      ContDiff ℝ ∞ amp → ContDiff ℝ ∞ c.F → ContDiff ℝ ∞ c.G → |(j : ℝ)| ≤ H →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i amp (commonLift h n d w)‖ ≤
        A * ChartScales.Q n ^ g * ChartScales.S n ^ eAmp) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i c.F
        (PhysicalGraphBounds.slotMap (PolarCharts.chart a c.chart)
          (ChartScales.timeCoefficient h n) c.center r0 (PhysicalGraphBounds.physicalLift h n w)).1‖ ≤
            B * ChartScales.S n ^ eBase) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i c.G
        (PhysicalGraphBounds.slotMap (PolarCharts.chart a c.chart)
          (ChartScales.timeCoefficient h n) c.center r0 (PhysicalGraphBounds.physicalLift h n w)).1‖ ≤
            B * ChartScales.S n ^ eBase) →
      ‖iteratedFDeriv ℝ m (commonWave a h n d r0 c amp j) w‖ ≤
        C * q ^ (g - (m:ℝ)*derivativeCost h) * (1+|Real.log q|)^N := by
  have hK : 0 ≤ coverBound Δ := zero_le_one.trans (coverBound_ge_one Δ)
  obtain ⟨C,hC,hb⟩ := SharpPhysicalCarrier.native_carrier_bound (b := b) hh ha hr0 hP hB heBase
    m g eAmp (A*coverBound Δ^m) H (by positivity) hH
  obtain ⟨D,hD,N,hweight⟩ := SharpLogWeights.chart_weight_bound
    (g-(m:ℝ)*derivativeCost h) (eAmp+(eBase+1)*(m:ℝ))
  refine ⟨C*D,mul_nonneg hC hD.le,N,?_⟩
  intro n hn d hd w hw ht hz q hq hlo hhi c amp j hp hpz hx0 hslot hamp hF hG hj hab hFb hGb
  have hQ := ChartScales.Q_pos n
  have hS := ChartScales.S_pos (show 1 ≤ n by omega)
  have ha : ∀ i ≤ m, ‖iteratedFDeriv ℝ i (amp ∘ downLift d) (PhysicalGraphBounds.physicalLift h n w)‖ ≤
      (A*coverBound Δ^m)*ChartScales.Q n^g*ChartScales.S n^eAmp := by
    intro i hi
    exact (downLift_jet_bound hamp hd (PhysicalGraphBounds.physicalLift h n w)
      (B := A*ChartScales.Q n^g*ChartScales.S n^eAmp) (by positivity) hab i hi).trans_eq (by ring)
  have hF' : ∀ i ≤ m, ‖iteratedFDeriv ℝ i c.F (slowMap (PolarCharts.chart a c.chart) h n w)‖ ≤
      B*ChartScales.S n^eBase := by
    intro i hi
    rw [slowMap_eq_slot _ _ _ c.center r0]
    exact hFb i hi
  have hG' : ∀ i ≤ m, ‖iteratedFDeriv ℝ i c.G (slowMap (PolarCharts.chart a c.chart) h n w)‖ ≤
      B*ChartScales.S n^eBase := by
    intro i hi
    rw [slowMap_eq_slot _ _ _ c.center r0]
    exact hGb i hi
  have he := hb n hn w hw ht c.chart c.center c.angular c.axial c.radial hp hpz hx0 hslot
    (amp ∘ downLift d) c.F c.G j (hamp.comp (downLift d).contDiff) hF hG hj ha hF' hG'
  apply he.trans
  calc
    _ = C*(ChartScales.Q n^(g-(m:ℝ)*derivativeCost h)*ChartScales.S n^(eAmp+(eBase+1)*(m:ℝ))) := by ring
    _ ≤ C*(D*q^(g-(m:ℝ)*derivativeCost h)*(1+|Real.log q|)^N) :=
      mul_le_mul_of_nonneg_left (hweight n (by omega) q hq hlo hhi) hC
    _ = _ := by ring

theorem common_carrier_log_bound_local {h a b Z r0 P B eBase : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B) (heBase : 0 ≤ eBase)
    (Δ m : ℕ) (g eAmp A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b →
      |w.1| ≤ 1 → ‖PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h n w)‖ ≤ Z →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ (c : CarrierData) (amp : LiftPoint → ℂ) (j : ℤ),
      |c.angular| ≤ P → |c.axial| ≤ P → |c.radial| ≤ P →
      |PhysicalGraphBounds.etaCoordinate (PhysicalGraphBounds.nativeGraph h n w - c.center)| ≤ r0 →
      SmoothNear amp (commonLift h n d w) → SmoothNear c.F (slotSlow c a h n r0 w) →
      SmoothNear c.G (slotSlow c a h n r0 w) → |(j : ℝ)| ≤ H →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i amp (commonLift h n d w)‖ ≤
        A * ChartScales.Q n ^ g * ChartScales.S n ^ eAmp) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i c.F (slotSlow c a h n r0 w)‖ ≤
        B * ChartScales.S n ^ eBase) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i c.G (slotSlow c a h n r0 w)‖ ≤
        B * ChartScales.S n ^ eBase) →
      ‖iteratedFDeriv ℝ m (commonWave a h n d r0 c amp j) w‖ ≤
        C * q ^ (g - (m:ℝ)*derivativeCost h) * (1+|Real.log q|)^N := by
  obtain ⟨C, hC, N, hb⟩ := common_carrier_log_bound (b := b)
    hh hh1 ha hZ hr0 hP hB heBase Δ m g eAmp A H hA hH
  refine ⟨C, hC, N, ?_⟩
  intro n hn d hd w hann ht hz q hq hlo hhi c amp j hp hpz hpx hslot haNear hFNear hGNear hj hab hFb hGb
  obtain ⟨amp', ha', hea⟩ := haNear.exists_global_germ
  obtain ⟨F, hF', heF⟩ := hFNear.exists_global_germ
  obtain ⟨G, hG', heG⟩ := hGNear.exists_global_germ
  have haxis := PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree ha hann)
  rw [iteratedFDeriv_eq_of_eventuallyEq (commonWave_germ ha h n d r0 c j haxis hea heF heG) m]
  apply hb n hn d hd w hann ht hz q hq hlo hhi (replaceProfiles c F G) amp' j
    hp hpz hpx hslot ha' hF' hG' hj
  · intro i hi
    rw [← iteratedFDeriv_eq_of_eventuallyEq hea i]
    exact hab i hi
  · intro i hi
    change ‖iteratedFDeriv ℝ i F (slotSlow c a h n r0 w)‖ ≤ _
    rw [← iteratedFDeriv_eq_of_eventuallyEq heF i]
    exact hFb i hi
  · intro i hi
    change ‖iteratedFDeriv ℝ i G (slotSlow c a h n r0 w)‖ ≤ _
    rw [← iteratedFDeriv_eq_of_eventuallyEq heG i]
    exact hGb i hi

theorem physical_sum_log_bound {K : Type*} {h a b Z r0 P B eBase : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a)
    (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B) (heBase : 0 ≤ eBase)
    (H Δ m : ℕ) (g eAmp A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ f : CopyFamily H K,
      SupportData f a b h r0 Z Δ → SmoothData f a h r0 → ∀ hc : SupportCells f,
      JetData f hc a b h r0 P A B g eAmp eBase m →
      ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (f.sum a h r0) w‖ ≤
        C * physicalQ h w ^ (g - (m:ℝ)*derivativeCost h) * (1+|Real.log (physicalQ h w)|)^N := by
  obtain ⟨C, hC, N, hpoint⟩ := common_carrier_log_bound_local (b := b) hh.le hh1.le ha
    hZ hr0 hP hB heBase Δ m g eAmp A (H : ℝ) hA (Nat.cast_nonneg H)
  refine ⟨((2250 * (2 * H + 1) : ℕ) : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC, N, ?_⟩
  intro f hr hs hc hb w hw ht
  have hq := physicalQ_pos hh hh1 hw
  have hcopy : ∀ (I : WaveIndex H),
      physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val → ∀ k,
      ‖iteratedFDeriv ℝ m (f.term a h r0 I k) w‖ ≤
        C * physicalQ h w ^ (g - (m:ℝ)*derivativeCost h) * (1+|Real.log (physicalQ h w)|)^N := by
    intro I hregion k
    by_cases hts : w ∈ tsupport (f.term a h r0 I k)
    · have hgeo := hr.tsupport_geometry I k hts
      have hcell := hc.term_tsupport_mem ha I k hgeo.1 hts
      obtain ⟨mode, hmode⟩ := hr.angular_integer k I.1
      let chart := chooseChart a (PhysicalGraphBounds.scaledRadial I.1.val.1 w)
      have hchart : PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PolarCharts.chartDomain a chart :=
        chooseChart_valid ha hgeo.1
      have he := globalWave_eventually_common (r0 := r0) ha I.1.val.1 (f.gap I.1)
        (f.carrier k I.1) (f.amplitude k I) I.2.val mode hmode
        (fun y hy => (hr.geometry_support k I y hy).1) chart hchart
      change ‖iteratedFDeriv ℝ m (globalWave a h I.1.val.1 (f.gap I.1) r0
        (f.carrier k I.1) (f.amplitude k I) I.2.val) w‖ ≤ _
      rw [iteratedFDeriv_eq_of_eventuallyEq he m]
      have hband := labelRegion_active_relation hregion
      have hp := hs.profiles k I w hw hts chart hchart
      have hjets := hb.jets k I w hw hregion hgeo.1 hcell hts
      exact hpoint I.1.val.1 I.1.property (f.gap I.1) (hr.gap_le I.1)
        w hgeo.1 ht hgeo.2.1 (physicalQ h w) hq hband.1 hband.2
        ((f.carrier k I.1).withChart chart) (f.amplitude k I) I.2.val
        (hb.parameters k I.1).1 (hb.parameters k I.1).2.1 (hb.parameters k I.1).2.2 hgeo.2.2
        (hs.amplitude k I w hw hts) hp.1 hp.2 (harmonic_bound I.2)
        hjets.1 (hjets.2 chart hchart).1 (hjets.2 chart hchart).2
    · rw [jet_zero_off_tsupport _ _ hts, norm_zero]
      positivity
  have hsum := masked_finsum_jet_bound hh hh1 (f.periodized a h r0)
    (hr.periodized_smoothAt hs hc ha) hr.periodized_support hw m
    (B := C * physicalQ h w ^ (g - (m:ℝ)*derivativeCost h) * (1+|Real.log (physicalQ h w)|)^N) (by positivity)
  refine (hsum ?_).trans_eq (by ring)
  intro I hregion
  rcases hr.periodized_germ_cover hc ha I w with ⟨k, _, hg⟩ | hg
  · rw [iteratedFDeriv_eq_of_eventuallyEq hg m]
    exact hcopy I hregion k
  · rw [iteratedFDeriv_eq_of_eventuallyEq hg m]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    positivity



section WeightedInputs
open WeightedClasses
variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {ι K : Type*}
  {h a b r0 Z : ℝ} {H Δ : ℕ} {f : CopyFamily H K}

theorem physical_sum_log_bound_of_weighted {s : StripData D} {α σ P : ℝ}
    {w : ι → ℕ → D → ℝ} {source : ι → ℕ → D → ℂ}
    (hsource : LocalSourceBounds s h α w source) {hc : SupportCells f}
    (hchart : CommonChart f hc a b h r0 σ source)
    (hmap : ∀ k I, MapsTo (hchart.map k I) (hchart.domain k I) s.domain)
    (hb : PhysicalCopyBounds.CarrierBounds f hc a b h r0)
    (hr : SupportData f a b h r0 Z Δ) (hs : SmoothData f a h r0)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0)
    (hP : 1 ≤ P) (hp : ∀ k L, |(f.carrier k L).angular| ≤ P ∧
      |(f.carrier k L).axial| ≤ P ∧ |(f.carrier k L).radial| ≤ P) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ z : SpaceTime,
      z ∈ preterminal → |z.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (f.sum a h r0) z‖ ≤
        C * physicalQ h z ^ (h * α + σ - (m:ℝ)*derivativeCost h) * (1+|Real.log (physicalQ h z)|)^N := by
  obtain ⟨A, hA, B, hB, p, q, hclass⟩ := localStrippedClass_of_weighted hsource hchart hmap hb hs hp m
  obtain ⟨C, hC, N, hbound⟩ := physical_sum_log_bound (K := K)
    (b := b) hh hh1 ha hZ hr0 hP hB (Nat.cast_nonneg q) H Δ m
      (h * α + σ) p A hA
  refine ⟨C, hC, N, ?_⟩
  intro z hz ht
  exact hbound f hr hs hc hclass z hz ht

end WeightedInputs
end NavierStokes.SharpPhysicalCopyBounds
end

/-! Merged from `NavierStokes.SharpWaveStageBounds` (in a section, so its `open`s cannot leak). -/
section
noncomputable section
namespace NavierStokes.PhysicalStageBounds.WaveData
open Set Function Filter ProblemStatement
open SharpPhysicalCarrier
open scoped Topology ContDiff BigOperators

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

variable {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K J : Type*}

/-- Exact linear derivative loss for a genuine wave stage, derived from
its weighted native source, common-chart maps and phase profiles. -/
theorem scalar_log_bound (W : WaveData h D I K J)
    (hh : 0 < h) (hh1 : h < 1/2) (i : J) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (W.scalar i) w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*W.alpha+W.shift-(m:ℝ)*derivativeCost h)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := SharpPhysicalCopyBounds.physical_sum_log_bound_of_weighted
    W.source_bounds (W.chart i) (W.chart_maps i) (W.carrier i) (W.support i) (W.smooth i)
    hh hh1 W.lower_pos W.slow_nonneg W.width_nonneg W.frequency_one_le (W.frequencies i) m
  exact ⟨C,hC,N,fun w hw hq => hb w hw (abs_time_le_one hh hh1 hw hq)⟩

theorem vector_log_bound (W : WaveData h D I K (Fin 3))
    (hh : 0 < h) (hh1 : h < 1/2) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m W.vector w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*W.alpha+W.shift-(m:ℝ)*derivativeCost h)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  classical
  have hb := fun i => W.scalar_log_bound hh hh1 i m
  choose C hC N hbound using hb
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => hC i)
  refine ⟨3*∑ i, C i, mul_nonneg (by norm_num) hsum, ∑ i, N i, ?_⟩
  intro w hw hq
  have hq0 := PhysicalWaveSum.physicalQ_pos hh hh1 hw
  have hL : 1 ≤ 1+|Real.log (PhysicalWaveSum.physicalQ h w)| := by linarith [abs_nonneg (Real.log (PhysicalWaveSum.physicalQ h w))]
  have hci (i : Fin 3) : C i ≤ ∑ j, C j :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  have hni (i : Fin 3) : N i ≤ ∑ j, N j := Finset.single_le_sum (by intros; omega) (Finset.mem_univ i)
  have he := LocalPhysicalCopyBounds.vectorSum_jet_bound W.support W.smooth W.cells W.lower_pos hh hh1 hw m
    (B := (∑ i, C i)*PhysicalWaveSum.physicalQ h w^(h*W.alpha+W.shift-(m:ℝ)*derivativeCost h)*
      (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^(∑ i,N i))
    (fun i => (hbound i w hw hq).trans (mul_le_mul
      (mul_le_mul_of_nonneg_right (hci i) (Real.rpow_nonneg hq0.le _))
      (pow_le_pow_right₀ hL (hni i)) (by positivity) (by positivity)))
  exact he.trans_eq (by ring)

theorem pressure_log_bound (W : WaveData h D I K Unit)
    (hh : 0 < h) (hh1 : h < 1/2) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m W.pressure w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*W.alpha+W.shift-(m:ℝ)*derivativeCost h)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := W.scalar_log_bound hh hh1 () m
  refine ⟨‖Complex.reCLM‖*C, mul_nonneg (norm_nonneg _) hC,N,?_⟩
  intro w hw hq
  have hs := ((W.scalar_smooth hh hh1 ()).contDiffAt
    (PhysicalWaveSum.preterminal_open.mem_nhds hw)).of_le (nat_le_infty m)
  have he := PhysicalWaveSum.norm_jet_linear_comp_at hs Complex.reCLM
  exact he.trans ((mul_le_mul_of_nonneg_left (hb w hw hq) (norm_nonneg _)).trans_eq (by ring))

theorem curl_log_bound (W : WaveData h D I K (Fin 3))
    (hh : 0 < h) (hh1 : h < 1/2) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl W.vector) w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*W.alpha+W.shift-((m:ℝ)+1)*derivativeCost h)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := W.vector_log_bound hh hh1 (m+1)
  refine ⟨‖PhysicalClassBounds.jointCurl‖*C, mul_nonneg (norm_nonneg PhysicalClassBounds.jointCurl) hC,N,?_⟩
  intro w hw hq
  have he := PhysicalClassBounds.spatialCurl_jet_bound PhysicalWaveSum.preterminal_open
    (W.vector_smooth hh hh1) hw m
  have hb' := hb w hw hq
  simp only [Nat.cast_add,Nat.cast_one] at hb'
  exact he.trans ((mul_le_mul_of_nonneg_left hb' (norm_nonneg PhysicalClassBounds.jointCurl)).trans_eq (by ring))

private theorem common_loss_bound {α σ q C : ℝ} {m k : ℕ}
    (hh : 0 ≤ h) (hσ : -(2*CoordinateAlgebra.A h) ≤ σ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hC : 0 ≤ C) (hkm : k ≤ m+1) (N : ℕ) :
    C*q^(h*α+σ-(k:ℝ)*derivativeCost h)*(1+|Real.log q|)^N ≤
      C*q^(h*α-physicalLoss h m)*(1+|Real.log q|)^N := by
  have hcost : 0 ≤ derivativeCost h := by unfold derivativeCost; linarith
  have hk : (k:ℝ) ≤ (m:ℝ)+1 := by exact_mod_cast hkm
  have he : h*α-physicalLoss h m ≤ h*α+σ-(k:ℝ)*derivativeCost h := by
    unfold physicalLoss
    nlinarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hq hq1 he) hC) (by positivity)

/-- The full physical wave vector obeys the manuscript's common `ell_m`. -/
theorem vector_printed_bound (W : WaveData h D I K (Fin 3))
    (hh : 0 < h) (hh1 : h < 1/2) (hshift : -(2*CoordinateAlgebra.A h) ≤ W.shift) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m W.vector w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*W.alpha-physicalLoss h m)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := W.vector_log_bound hh hh1 m
  exact ⟨C,hC,N,fun w hw hq => (hb w hw hq).trans
    (common_loss_bound hh.le hshift (PhysicalWaveSum.physicalQ_pos hh hh1 hw) hq hC (by omega) N)⟩

/-- Pressure has the same printed loss, including the permitted `Q⁻²ᴬ` prefactor. -/
theorem pressure_printed_bound (W : WaveData h D I K Unit)
    (hh : 0 < h) (hh1 : h < 1/2) (hshift : -(2*CoordinateAlgebra.A h) ≤ W.shift) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m W.pressure w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*W.alpha-physicalLoss h m)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := W.pressure_log_bound hh hh1 m
  exact ⟨C,hC,N,fun w hw hq => (hb w hw hq).trans
    (common_loss_bound hh.le hshift (PhysicalWaveSum.physicalQ_pos hh hh1 hw) hq hC (by omega) N)⟩

/-- Recovering velocity by the actual spatial curl is included in `ell_m`. -/
theorem curl_printed_bound (W : WaveData h D I K (Fin 3))
    (hh : 0 < h) (hh1 : h < 1/2) (hshift : -(2*CoordinateAlgebra.A h) ≤ W.shift) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl W.vector) w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*W.alpha-physicalLoss h m)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := W.curl_log_bound hh hh1 m
  refine ⟨C,hC,N,?_⟩
  intro w hw hq
  apply (hb w hw hq).trans
  simpa only [Nat.cast_add,Nat.cast_one] using
    common_loss_bound (α := W.alpha) hh.le hshift (PhysicalWaveSum.physicalQ_pos hh hh1 hw) hq hC
      (show m+1 ≤ m+1 from le_rfl) N

end NavierStokes.PhysicalStageBounds.WaveData
end

section
noncomputable section
namespace NavierStokes.ActualPhysicalStageBounds.MeanInput
open Set Function Filter ProblemStatement
open SharpMeanJetBounds SharpPhysicalCarrier
open scoped Topology ContDiff

/-- Coherent physical scalar means retain the exact graph loss and the
native logarithmic factor on their original common physical domain. -/
theorem field_log_bound {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1/2) (hq : qbig ≤ ChartScales.Q M.firstBand) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.field w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*M.alpha-meanLoss h degree m)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := SharpMeanJetBounds.field_log_bound M.family hh hh1 M.lower_pos
    M.radii_lt M.band_four (region_open hh hh1) (fun _ hx => hx) M.smooth M.support M.jets m
  refine ⟨C,hC,N,?_⟩
  intro w hw hqw
  exact hb w hw.1 (PhysicalStageBounds.abs_time_le_one hh hh1 hw.1 hqw) (hw.2.le.trans hq)

theorem angular_log_bound {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1/2) (hq : qbig ≤ ChartScales.Q M.firstBand) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.angularField w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*M.alpha-meanLoss h degree m)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := SharpMeanJetBounds.angularField_log_bound M.family hh hh1 M.lower_pos
    M.radii_lt M.band_four (region_open hh hh1) (fun _ hx => hx) M.smooth M.support M.jets m
  refine ⟨C,hC,N,?_⟩
  intro w hw hqw
  exact hb w hw.1 (PhysicalStageBounds.abs_time_le_one hh hh1 hw.1 hqw) (hw.2.le.trans hq)

theorem curl_log_bound {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1/2) (hq : qbig ≤ ChartScales.Q M.firstBand) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl M.family.angularField) w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*M.alpha-meanLoss h degree (m+1))*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := SharpMeanJetBounds.curl_angularField_log_bound M.family hh hh1 M.lower_pos
    M.radii_lt M.band_four (region_open hh hh1) (fun _ hx => hx) M.smooth M.support M.jets m
  refine ⟨C,hC,N,?_⟩
  intro w hw hqw
  exact hb w ⟨hw.1, hw.2.trans_le hq⟩ (PhysicalStageBounds.abs_time_le_one hh hh1 hw.1 hqw)

private theorem common_loss_bound {h degree q C α : ℝ} {m k : ℕ}
    (hh : 0 ≤ h) (hdegree : degree ≤ 2*CoordinateAlgebra.A h) (hkm : k ≤ m+1)
    (hq : 0 < q) (hq1 : q ≤ 1) (hC : 0 ≤ C) (N : ℕ) :
    C*q^(h*α-meanLoss h degree k)*(1+|Real.log q|)^N ≤
      C*q^(h*α-physicalLoss h m)*(1+|Real.log q|)^N := by
  have hk : (k:ℝ) ≤ (m:ℝ)+1 := by exact_mod_cast hkm
  have hm : 0 ≤ (m:ℝ)+1 := by positivity
  have he : h*α-physicalLoss h m ≤ h*α-meanLoss h degree k := by
    unfold physicalLoss meanLoss derivativeCost
    nlinarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hq hq1 he) hC) (by positivity)

theorem field_printed_bound {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1/2) (hq : qbig ≤ ChartScales.Q M.firstBand)
    (hdegree : degree ≤ 2*CoordinateAlgebra.A h) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.field w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*M.alpha-physicalLoss h m)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := M.field_log_bound hh hh1 hq m
  exact ⟨C,hC,N,fun w hw hqw => (hb w hw hqw).trans
    (common_loss_bound hh.le hdegree (by omega) (PhysicalWaveSum.physicalQ_pos hh hh1 hw.1) hqw hC N)⟩

theorem angular_printed_bound {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1/2) (hq : qbig ≤ ChartScales.Q M.firstBand)
    (hdegree : degree ≤ 2*CoordinateAlgebra.A h) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.angularField w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*M.alpha-physicalLoss h m)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := M.angular_log_bound hh hh1 hq m
  exact ⟨C,hC,N,fun w hw hqw => (hb w hw hqw).trans
    (common_loss_bound hh.le hdegree (by omega) (PhysicalWaveSum.physicalQ_pos hh hh1 hw.1) hqw hC N)⟩

theorem curl_printed_bound {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1/2) (hq : qbig ≤ ChartScales.Q M.firstBand)
    (hdegree : degree ≤ 2*CoordinateAlgebra.A h) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl M.family.angularField) w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*M.alpha-physicalLoss h m)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := M.curl_log_bound hh hh1 hq m
  exact ⟨C,hC,N,fun w hw hqw => (hb w hw hqw).trans
    (common_loss_bound hh.le hdegree le_rfl (PhysicalWaveSum.physicalQ_pos hh hh1 hw.1) hqw hC N)⟩

end NavierStokes.ActualPhysicalStageBounds.MeanInput
end

noncomputable section
namespace NavierStokes.SharpGluedStageBounds
open Set Function Filter ProblemStatement PhysicalWaveSum
open scoped Topology ContDiff BigOperators

open CorrectionInitialization CorrectionInitialization.ActualPrimary ActualStageEstimates

section SignedAndMean

variable {B N0 N : ℕ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {I K : Type*} (R : RunData B N0)
  (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
    (fun _ => ActualCycleParameters.fixedParameters B N0))
  (hN : 4 ≤ N) (W : GluedStageEstimates.SignedInputs D I K)

private theorem potential_gain (j : ℕ) :
    ActualIterationLedger.gain h (j+1) ≤ h * (W.potential j).alpha := by
  have hg := ActualIterationLedger.gain_le_wave outgoing.data.h_pos.le
    ActualCyclePreservation.kappa_small (Nat.succ_pos j)
  rw [← nativePotential_eq_ledger j] at hg
  exact hg.trans (mul_le_mul_of_nonneg_left (W.potential_exponent j) outgoing.data.h_pos.le)

private theorem pressure_gain (j : ℕ) :
    ActualIterationLedger.gain h (j+1) ≤ h * (W.pressure j).alpha := by
  have hg := ActualIterationLedger.gain_le_wavePressure outgoing.data.h_pos.le
    ActualCyclePreservation.kappa_small (Nat.succ_pos j)
  rw [← nativePressure_eq_ledger j] at hg
  exact hg.trans (mul_le_mul_of_nonneg_left (W.pressure_exponent j) outgoing.data.h_pos.le)

private theorem mean_gain (j : ℕ) :
    ActualIterationLedger.gain h (j+1) ≤ h * (1+ActualIterationLedger.sigma j-2*ChartScales.kappa) := by
  rw [nativeMean_eq_ledger]
  exact ActualIterationLedger.gain_le_mean outgoing.data.h_pos.le
    ActualCyclePreservation.kappa_small (Nat.succ_pos j)

private theorem mean_degree : CoordinateAlgebra.A h - 1/2 ≤ 2*CoordinateAlgebra.A h := by
  unfold CoordinateAlgebra.A
  linarith [outgoing.data.h_pos]

theorem signedMeanPotential_printed_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    LogBound h qbig (GluedStageEstimates.signedMeanPotential R M hN W j) m
      (ActualIterationLedger.gain h (j+1) - SharpPhysicalCarrier.physicalLoss h m) := by
  have hs0 := (W.potential j).vector_printed_bound outgoing.data.h_pos outgoing.data.h_lt_half
    (by rw [W.potential_shift]; unfold CoordinateAlgebra.A; linarith [outgoing.data.h_pos]) m
  have hs : LogBound h qbig (W.potential j).vector m
      (h*(W.potential j).alpha-SharpPhysicalCarrier.physicalLoss h m) := by
    obtain ⟨C,hC,n,hb⟩ := hs0
    exact ⟨C,hC,n,fun w hw hqw => hb w hw.1 hqw⟩
  have ht : LogBound h qbig (temporalInput R M hN j).family.angularField m
      (h*(1+ActualIterationLedger.sigma j-2*ChartScales.kappa)-SharpPhysicalCarrier.physicalLoss h m) :=
    (temporalInput R M hN j).angular_printed_bound outgoing.data.h_pos outgoing.data.h_lt_half
      hq mean_degree m
  have hr : LogBound h qbig (rankInput R M hN j).family.angularField m
      (h*(1+ActualIterationLedger.sigma j-2*ChartScales.kappa)-SharpPhysicalCarrier.physicalLoss h m) :=
    (rankInput R M hN j).angular_printed_bound outgoing.data.h_pos outgoing.data.h_lt_half
      hq mean_degree m
  have ss : ContDiffOn ℝ ∞ (W.potential j).vector (CutStageEstimates.physicalSublevel h qbig) :=
    ((W.potential j).vector_smooth outgoing.data.h_pos outgoing.data.h_lt_half).mono inter_subset_left
  have st := (temporalInput R M hN j).angular_smooth outgoing.data.h_pos outgoing.data.h_lt_half hq
  have sr := (rankInput R M hN j).angular_smooth outgoing.data.h_pos outgoing.data.h_lt_half hq
  exact ((hs.weaken outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_right (potential_gain W j) _)).add
    (ht.weaken outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_right (mean_gain j) _))
    outgoing.data.h_pos outgoing.data.h_lt_half ss st).add
      (hr.weaken outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_right (mean_gain j) _))
      outgoing.data.h_pos outgoing.data.h_lt_half (ss.add st) sr

theorem signedMeanPressure_printed_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    LogBound h qbig (GluedStageEstimates.signedMeanPressure R M hN W j) m
      (ActualIterationLedger.gain h (j+1) - SharpPhysicalCarrier.physicalLoss h m) := by
  have hs0 := (W.pressure j).pressure_printed_bound outgoing.data.h_pos outgoing.data.h_lt_half
    (by rw [W.pressure_shift]) m
  have hs : LogBound h qbig (W.pressure j).pressure m
      (h*(W.pressure j).alpha-SharpPhysicalCarrier.physicalLoss h m) := by
    obtain ⟨C,hC,n,hb⟩ := hs0
    exact ⟨C,hC,n,fun w hw hqw => hb w hw.1 hqw⟩
  have hm : LogBound h qbig (pressureInput R M hN j).family.field m
      (h*(1+ActualIterationLedger.sigma j-2*ChartScales.kappa)-SharpPhysicalCarrier.physicalLoss h m) :=
    (pressureInput R M hN j).field_printed_bound outgoing.data.h_pos outgoing.data.h_lt_half hq le_rfl m
  exact (hs.weaken outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_right (pressure_gain W j) _)).add
    (hm.weaken outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_right (mean_gain j) _))
    outgoing.data.h_pos outgoing.data.h_lt_half
    (((W.pressure j).pressure_smooth outgoing.data.h_pos outgoing.data.h_lt_half).mono inter_subset_left)
    ((pressureInput R M hN j).field_smooth outgoing.data.h_pos outgoing.data.h_lt_half hq)

theorem direct_printed_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    LogBound h qbig (GluedStageEstimates.direct R M hN j) m
      (ActualIterationLedger.gain h (j+1) - SharpPhysicalCarrier.physicalLoss h m) := by
  have hm : LogBound h qbig (angularInput R M hN j).family.angularField m
      (h*(1+ActualIterationLedger.sigma j-2*ChartScales.kappa)-SharpPhysicalCarrier.physicalLoss h m) :=
    (angularInput R M hN j).angular_printed_bound outgoing.data.h_pos outgoing.data.h_lt_half hq
      (by unfold CoordinateAlgebra.A; linarith [outgoing.data.h_pos]) m
  exact hm.weaken outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_right (mean_gain j) _)

theorem signedMeanCurl_printed_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    LogBound h qbig (SpatialCurl.spatialCurl (GluedStageEstimates.signedMeanPotential R M hN W j)) m
      (ActualIterationLedger.gain h (j+1) - SharpPhysicalCarrier.physicalLoss h m) := by
  have hs0 := (W.potential j).curl_printed_bound outgoing.data.h_pos outgoing.data.h_lt_half
    (by rw [W.potential_shift]; unfold CoordinateAlgebra.A; linarith [outgoing.data.h_pos]) m
  have hs : LogBound h qbig (SpatialCurl.spatialCurl (W.potential j).vector) m
      (h*(W.potential j).alpha-SharpPhysicalCarrier.physicalLoss h m) := by
    obtain ⟨C,hC,n,hb⟩ := hs0
    exact ⟨C,hC,n,fun w hw hqw => hb w hw.1 hqw⟩
  have ht : LogBound h qbig (SpatialCurl.spatialCurl (temporalInput R M hN j).family.angularField) m
      (h*(1+ActualIterationLedger.sigma j-2*ChartScales.kappa)-SharpPhysicalCarrier.physicalLoss h m) :=
    (temporalInput R M hN j).curl_printed_bound outgoing.data.h_pos outgoing.data.h_lt_half hq mean_degree m
  have hr : LogBound h qbig (SpatialCurl.spatialCurl (rankInput R M hN j).family.angularField) m
      (h*(1+ActualIterationLedger.sigma j-2*ChartScales.kappa)-SharpPhysicalCarrier.physicalLoss h m) :=
    (rankInput R M hN j).curl_printed_bound outgoing.data.h_pos outgoing.data.h_lt_half hq mean_degree m
  have hU := CutStageEstimates.physicalSublevel_open outgoing.data.h_pos outgoing.data.h_lt_half qbig
  have ss : ContDiffOn ℝ ∞ (W.potential j).vector (CutStageEstimates.physicalSublevel h qbig) :=
    ((W.potential j).vector_smooth outgoing.data.h_pos outgoing.data.h_lt_half).mono inter_subset_left
  have st := (temporalInput R M hN j).angular_smooth outgoing.data.h_pos outgoing.data.h_lt_half hq
  have sr := (rankInput R M hN j).angular_smooth outgoing.data.h_pos outgoing.data.h_lt_half hq
  have scs := InitializedPhysicalBackground.spatialCurl_smoothOn hU ss
  have sct := InitializedPhysicalBackground.spatialCurl_smoothOn hU st
  have scr := InitializedPhysicalBackground.spatialCurl_smoothOn hU sr
  have hb := ((hs.weaken outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_right (potential_gain W j) _)).add
    (ht.weaken outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_right (mean_gain j) _))
    outgoing.data.h_pos outgoing.data.h_lt_half scs sct).add
      (hr.weaken outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_right (mean_gain j) _))
      outgoing.data.h_pos outgoing.data.h_lt_half (scs.add sct) scr
  apply hb.congr outgoing.data.h_pos outgoing.data.h_lt_half
  intro w hw
  change _ = SpatialCurl.spatialCurl (fun z => (W.potential j).vector z +
    (temporalInput R M hN j).family.angularField z + (rankInput R M hN j).family.angularField z) w
  rw [InitializedPhysicalBackground.spatialCurl_add_on hU (ss.add st) sr hw]
  dsimp only
  rw [InitializedPhysicalBackground.spatialCurl_add_on hU ss st hw]

theorem potential_printed_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)
    {particular : ℕ → VelocityField} (j m : ℕ)
    (hs : ContDiffOn ℝ ∞ (particular j) (CutStageEstimates.physicalSublevel h qbig))
    (hb : LogBound h qbig (particular j) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m)) :
    LogBound h qbig (GluedStageEstimates.potential R M hN W particular j) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) := by
  rw [GluedStageEstimates.potential_eq]
  exact hb.add (signedMeanPotential_printed_bound R M hN W hq j m)
    outgoing.data.h_pos outgoing.data.h_lt_half hs
    (GluedStageEstimates.signedMeanPotential_smooth R M hN W hq j)

theorem pressure_printed_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)
    {particular : ℕ → PressureField} (j m : ℕ)
    (hs : ContDiffOn ℝ ∞ (particular j) (CutStageEstimates.physicalSublevel h qbig))
    (hb : LogBound h qbig (particular j) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m)) :
    LogBound h qbig (GluedStageEstimates.pressure R M hN W particular j) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) := by
  rw [GluedStageEstimates.pressure_eq]
  exact hb.add (signedMeanPressure_printed_bound R M hN W hq j m)
    outgoing.data.h_pos outgoing.data.h_lt_half hs
    (GluedStageEstimates.signedMeanPressure_smooth R M hN W hq j)

theorem curl_printed_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)
    {particular : ℕ → VelocityField} (j m : ℕ)
    (hs : ContDiffOn ℝ ∞ (particular j) (CutStageEstimates.physicalSublevel h qbig))
    (hb : LogBound h qbig (SpatialCurl.spatialCurl (particular j)) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m)) :
    LogBound h qbig (SpatialCurl.spatialCurl (GluedStageEstimates.potential R M hN W particular j)) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) := by
  have hU := CutStageEstimates.physicalSublevel_open outgoing.data.h_pos outgoing.data.h_lt_half qbig
  have ss := GluedStageEstimates.signedMeanPotential_smooth R M hN W hq j
  have hsum := hb.add (signedMeanCurl_printed_bound R M hN W hq j m)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (InitializedPhysicalBackground.spatialCurl_smoothOn hU hs)
    (InitializedPhysicalBackground.spatialCurl_smoothOn hU ss)
  rw [GluedStageEstimates.potential_eq]
  exact hsum.congr outgoing.data.h_pos outgoing.data.h_lt_half
    (InitializedPhysicalBackground.spatialCurl_add_on hU hs ss).symm

end SignedAndMean

end NavierStokes.SharpGluedStageBounds

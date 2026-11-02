import NavierStokes.ValidDyadicBandCover
import NavierStokes.CartesianCopySource
import NavierStokes.ParticularPaddedBackground
import NavierStokes.ActualParticularStageControls
import NavierStokes.ActualPhaseJetBounds
import NavierStokes.LocalPhysicalCopyBounds
import NavierStokes.ActualCurrentParticularPhysical
import NavierStokes.ActualSignedPhysicalData
import NavierStokes.PhysicalParticularWave
import NavierStokes.WaveEnvelopeTransport
import NavierStokes.ResidualPolarGraph
import NavierStokes.CurrentParticularLabelBounds
import NavierStokes.ActualCurrentWaveSupport

/-!
# Quantitative bounds for actual current-band particular fields

The estimates use the actual current coefficient and phase on their open
validity domains. No reference-field smoothness or auxiliary copy-family
representation is assumed.
-/
/-! Merged from `NavierStokes.CurrentPhysicalChartJets`. -/
/-!
# Uniform jets of the actual current physical chart

Only the transverse normalized coordinates are restricted to a fixed annulus.
The slow, angular, and free auxiliary coordinates need no bound for the
positive jets of the chart map.  Native coefficients need smoothness only
on a neighborhood of the evaluation point.
-/

noncomputable section

namespace NavierStokes.CurrentPhysicalChartJets

open Set Function Filter
open scoped Topology ContDiff

abbrev LiftPoint := PhysicalWaveSum.LiftPoint
abbrev Plane := PhysicalGraphBounds.Plane
abbrev Native := PhysicalParticularWave.WaveSpace
abbrev ComplexVector := HarmonicCalculus.ComplexVector

/-- The actual polar lift followed by the solver's fixed coordinate order. -/
noncomputable def chartMap (a : ℝ) (j : PolarCharts.Index) : LiftPoint → Native :=
  fun x => PhysicalParticularWave.waveEquiv (ActualSignedPhysicalData.cylinderAt a j x)

/-- Only the radial and angular entries depend on the nonlinear polar map. -/
noncomputable def polarPart : Plane →L[ℝ] Native :=
  (((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (0 : Plane →L[ℝ] Plane)).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)).prod (0 : Plane →L[ℝ] Plane)

noncomputable def reversePlane : Plane →L[ℝ] Plane :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)

/-- The free coordinates are copied by a bounded linear map. -/
noncomputable def freePart : LiftPoint →L[ℝ] Native :=
  (((0 : LiftPoint →L[ℝ] ℝ).prod (reversePlane.comp PhysicalGraphBounds.liftZT)).prod
    (0 : LiftPoint →L[ℝ] ℝ)).prod
      (ContinuousLinearMap.snd ℝ PhysicalGraphBounds.ChartPoint Plane)

theorem norm_polarPart_le : ‖polarPart‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro y
  simp [polarPart, Prod.norm_def, Real.norm_eq_abs, abs_nonneg]

theorem norm_freePart_le : ‖freePart‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  have hzt : ‖PhysicalGraphBounds.liftZT x‖ ≤ ‖x‖ :=
    (PhysicalGraphBounds.liftZT.le_opNorm x).trans
      (mul_le_of_le_one_left (norm_nonneg x) PhysicalGraphBounds.norm_liftZT_le)
  have hs : ‖reversePlane (PhysicalGraphBounds.liftZT x)‖ =
      ‖PhysicalGraphBounds.liftZT x‖ := by
    simp only [reversePlane, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_fst', Prod.norm_def]
    exact max_comm _ _
  change max (max (max ‖(0 : ℝ)‖ ‖reversePlane (PhysicalGraphBounds.liftZT x)‖)
    ‖(0 : ℝ)‖) ‖x.2‖ ≤ 1 * ‖x‖
  rw [norm_zero, hs, max_eq_right (norm_nonneg _), max_eq_left (norm_nonneg _), one_mul]
  exact max_le hzt (le_max_right _ _)

theorem chartMap_decomposition (a : ℝ) (j : PolarCharts.Index) :
    chartMap a j = fun x => polarPart (PolarCharts.chart a j (PhysicalGraphBounds.liftXY x)) +
      freePart x := by
  funext x
  ext <;> simp [chartMap, PhysicalParticularWave.waveEquiv_apply,
    ActualSignedPhysicalData.cylinderAt, polarPart, freePart, reversePlane]

theorem chartMap_smooth {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) :
    ContDiff ℝ ∞ (chartMap a j) := by
  rw [chartMap_decomposition]
  exact (polarPart.contDiff.comp ((PolarCharts.chart_contDiff ha j).comp
    PhysicalGraphBounds.liftXY.contDiff)).add freePart.contDiff

/-- One constant bounds all positive map jets on the transverse ball,
uniformly in all four charts and every unbounded free coordinate. -/
theorem chartMap_positive_jets_ball {a : ℝ} (ha : 0 < a) (b : ℝ) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ j : PolarCharts.Index, ∀ x : LiftPoint,
      PhysicalGraphBounds.liftXY x ∈ Metric.closedBall (0 : Plane) b →
      ∀ k, 1 ≤ k → k ≤ m → ‖iteratedFDeriv ℝ k (chartMap a j) x‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := PolarCharts.chart_finiteJets_uniform ha b m
  refine ⟨B + 1, by linarith, fun j x hx k hk hkm => ?_⟩
  have hc := (PolarCharts.chart_contDiff ha j).comp PhysicalGraphBounds.liftXY.contDiff
  have hcb := PhysicalGraphBounds.jet_comp_linear_bound (PolarCharts.chart_contDiff ha j)
    PhysicalGraphBounds.liftXY PhysicalGraphBounds.norm_liftXY_le x (zero_le_one.trans hB) m
    (fun i hi => hb j i hi _ hx)
  have hp := PhysicalGraphBounds.norm_jet_linear_comp hc polarPart x k
  have hpb : ‖iteratedFDeriv ℝ k
      (fun y => polarPart (PolarCharts.chart a j (PhysicalGraphBounds.liftXY y))) x‖ ≤ B :=
    hp.trans ((mul_le_mul norm_polarPart_le (hcb k hkm) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul B))
  rw [chartMap_decomposition]
  have ha := ResidualStability.norm_jet_add_le isOpen_univ
    (f := fun y => polarPart (PolarCharts.chart a j (PhysicalGraphBounds.liftXY y)))
    (g := fun y => freePart y)
    (polarPart.contDiff.comp hc).contDiffOn freePart.contDiff.contDiffOn (mem_univ x) k
  exact ha.trans (add_le_add hpb
    ((PhysicalGraphBounds.norm_positive_jet_linear_le freePart x hk).trans norm_freePart_le))

theorem chartMap_positive_jets {a b : ℝ} (ha : 0 < a) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ j : PolarCharts.Index, ∀ x ∈ PhysicalClassBounds.cylindricalDomain a b,
      ∀ k, 1 ≤ k → k ≤ m → ‖iteratedFDeriv ℝ k (chartMap a j) x‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := chartMap_positive_jets_ball ha (b + 1) m
  refine ⟨B, hB, fun j x hx => hb j x ?_⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2.le

section Composition

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a : ℝ} (ha : 0 < a) {j : PolarCharts.Index} {x : LiftPoint} {f : Native → E}

include ha

/-- One native open neighborhood suffices for the pulled-back coefficient. -/
theorem composition_smoothNear
    (hf : LocalPhysicalCopyBounds.SmoothNear f (chartMap a j x)) :
    LocalPhysicalCopyBounds.SmoothNear (f ∘ chartMap a j) x := by
  obtain ⟨V, hV, hx, hf⟩ := hf
  exact ⟨chartMap a j ⁻¹' V, hV.preimage (chartMap_smooth ha j).continuous, hx,
    hf.comp (chartMap_smooth ha j).contDiffOn (fun _ hy => hy)⟩

/-- Pointwise finite-jet composition using only the native germ. -/
theorem composition_jet_bound (m : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hf : LocalPhysicalCopyBounds.SmoothNear f (chartMap a j x))
    (hfj : ∀ k ≤ m, ‖iteratedFDeriv ℝ k f (chartMap a j x)‖ ≤ A)
    (hmap : ∀ k, 1 ≤ k → k ≤ m → ‖iteratedFDeriv ℝ k (chartMap a j) x‖ ≤ B) :
    ∀ k ≤ m, ‖iteratedFDeriv ℝ k (f ∘ chartMap a j) x‖ ≤
      (m.factorial : ℝ) * A * B ^ m := by
  obtain ⟨V, hV, hx, hf⟩ := hf
  exact LocalPhysicalCopyBounds.composition_jet_bound_on
    (g := f) (φ := chartMap a j) (U := chartMap a j ⁻¹' V) (V := V)
    (hV.preimage (chartMap_smooth ha j).continuous) hV hf
    (chartMap_smooth ha j).contDiffOn (fun _ hy => hy) hx m hA hB hfj hmap

/-- The multiplicative constant is chosen before the chart, point, native
coefficient, band, or value of its frozen finite-jet bound. -/
theorem composition_jets {b : ℝ} (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j : PolarCharts.Index, ∀ x ∈ PhysicalClassBounds.cylindricalDomain a b,
      ∀ (f : Native → E), LocalPhysicalCopyBounds.SmoothNear f (chartMap a j x) →
      ∀ A : ℝ, 0 ≤ A → (∀ k ≤ m, ‖iteratedFDeriv ℝ k f (chartMap a j x)‖ ≤ A) →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (f ∘ chartMap a j) x‖ ≤ C * A := by
  obtain ⟨B, hB, hb⟩ := chartMap_positive_jets (b := b) ha m
  refine ⟨max 1 ((m.factorial : ℝ) * B ^ m), le_max_left _ _, ?_⟩
  intro j x hx f hf A hA hfj k hk
  have he := composition_jet_bound ha m hA hB hf hfj (hb j x hx) k hk
  calc
    _ ≤ (m.factorial : ℝ) * A * B ^ m := he
    _ = ((m.factorial : ℝ) * B ^ m) * A := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hA

end Composition

/-! ## Compatibility with positive physical radial scaling -/

theorem chartDomain_smul {a c : ℝ} (hc : 0 < c) (j : PolarCharts.Index) {p : Plane}
    (hp : p ∈ PolarCharts.chartDomain a j) :
    c • p ∈ PolarCharts.chartDomain (c * a) j := by
  change c * a / 4 < (PolarCharts.rotate j (c • p)).1
  rw [PolarCharts.rotate_smul]
  change c * a / 4 < c * (PolarCharts.rotate j p).1
  have he := mul_lt_mul_of_pos_left (show a / 4 < (PolarCharts.rotate j p).1 from hp) hc
  linarith

/-- On the genuine inverse-chart region, simultaneous scaling of the
physical radius and chart padding preserves the exact angular branch. -/
theorem chart_smul {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (j : PolarCharts.Index) {p : Plane}
    (hp : p ∈ PolarCharts.chartDomain a j) :
    PolarCharts.chart (c * a) j (c • p) =
      (c * (PolarCharts.chart a j p).1, (PolarCharts.chart a j p).2) := by
  rw [PolarCharts.chart_eq_localChart (mul_pos hc ha) j (chartDomain_smul hc j hp),
    PolarCharts.chart_eq_localChart ha j hp, PolarCharts.localChart_smul j hc]


/-! ## The actual Cartesian rotation -/

noncomputable def rotation (x : LiftPoint) : ComplexVector →L[ℝ] ComplexVector :=
  CartesianCopySource.rotationMap (PhysicalGraphBounds.liftXY x)

theorem rotation_smooth {a b : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ rotation (PhysicalClassBounds.cylindricalDomain a b) :=
  CartesianCopySource.rotationMap_smooth.comp PhysicalGraphBounds.liftXY.contDiff.contDiffOn
    (fun _ hx => PhysicalClassBounds.cylindricalDomain_axisFree ha hx)


/-- These are full jets, including order zero, of the literal rotation
operator.  The same constant works for every chart and free coordinate. -/
theorem rotation_jets {a b : ℝ} (ha : 0 < a) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ PhysicalClassBounds.cylindricalDomain a b, ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k rotation x‖ ≤ C :=
  CartesianCopySource.rotationMap_jets ha m

/-- Positive radial rescaling leaves the actual Cartesian rotation fixed,
including at its totalized zero input. -/
theorem rotationMap_smul {c : ℝ} (hc : 0 < c) (p : Plane) :
    CartesianCopySource.rotationMap (c • p) = CartesianCopySource.rotationMap p := by
  have hr : PhysicalClassBounds.cartesianRadius (c • p) =
      c * PhysicalClassBounds.cartesianRadius p := PolarCharts.radius_smul hc p
  simp only [CartesianCopySource.rotationMap, hr, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [mul_div_mul_left _ _ hc.ne', mul_div_mul_left _ _ hc.ne']

/-- Rotate a native vector coefficient after pulling it into the actual
normalized Cartesian lift. -/
noncomputable def rotated (a : ℝ) (j : PolarCharts.Index) (f : Native → ComplexVector)
    (x : LiftPoint) : ComplexVector := rotation x (f (chartMap a j x))

theorem rotated_smoothNear {a b : ℝ} (ha : 0 < a) {j : PolarCharts.Index}
    {x : LiftPoint} (hx : x ∈ PhysicalClassBounds.cylindricalDomain a b)
    {f : Native → ComplexVector}
    (hf : LocalPhysicalCopyBounds.SmoothNear f (chartMap a j x)) :
    LocalPhysicalCopyBounds.SmoothNear (rotated a j f) x := by
  obtain ⟨U, hU, hxU, hs⟩ := composition_smoothNear ha hf
  exact ⟨PhysicalClassBounds.cylindricalDomain a b ∩ U,
    (PhysicalClassBounds.cylindricalDomain_open a b).inter hU, ⟨hx, hxU⟩,
    ((rotation_smooth ha).mono inter_subset_left).clm_apply (hs.mono inter_subset_right)⟩

/-- Local composition and the full Leibniz estimate give a uniform bound
for the actual rotated coefficient, including order zero.  The constant is
independent of every band or label entering the native finite-jet bound. -/
theorem rotated_composition_jets {a b : ℝ} (ha : 0 < a) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j : PolarCharts.Index, ∀ x ∈ PhysicalClassBounds.cylindricalDomain a b,
      ∀ (f : Native → ComplexVector), LocalPhysicalCopyBounds.SmoothNear f (chartMap a j x) →
      ∀ A : ℝ, 0 ≤ A → (∀ k ≤ m, ‖iteratedFDeriv ℝ k f (chartMap a j x)‖ ≤ A) →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (rotated a j f) x‖ ≤ C * A := by
  obtain ⟨B, hB, hcomp⟩ := composition_jets (E := ComplexVector) (b := b) ha m
  obtain ⟨R, hR, hrot⟩ := rotation_jets (b := b) ha m
  refine ⟨max 1 ((2 : ℝ) ^ m * R * B), le_max_left _ _, ?_⟩
  intro j x hx f hf A hA hfj k hk
  obtain ⟨U, hU, hxU, hs⟩ := composition_smoothNear ha hf
  have he := WaveEnvelopeTransport.clm_apply_jet_bound_on
    ((PhysicalClassBounds.cylindricalDomain_open a b).inter hU)
    ((rotation_smooth ha).mono inter_subset_left) (hs.mono inter_subset_right)
    (show x ∈ PhysicalClassBounds.cylindricalDomain a b ∩ U from ⟨hx, hxU⟩)
    m (zero_le_one.trans hR) (mul_nonneg (zero_le_one.trans hB) hA)
    (hrot x hx) (hcomp j x hx f hf A hA hfj) k hk
  calc
    _ ≤ (2 : ℝ) ^ m * R * (B * A) := he
    _ = ((2 : ℝ) ^ m * R * B) * A := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hA

/-! ## The fixed Cartesian realification -/

theorem realVector_norm_le (z : ComplexVector) :
    ‖PhysicalCurlCovariance.realVector z‖ ≤ 3 * ‖z‖ := by
  have hi (i : Fin 3) : ‖PhysicalCurlCovariance.realVector z i‖ ≤ ‖z‖ := by
    rw [PhysicalCurlCovariance.realVector_apply, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm (z i)).trans (norm_le_pi_norm z i)
  have hs : ‖PhysicalCurlCovariance.realVector z‖ ^ 2 ≤ 3 * ‖z‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _i : Fin 3, ‖z‖ ^ 2 :=
        Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hi i) 2)
      _ = 3 * ‖z‖ ^ 2 := by simp
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 3 * ‖z‖)).mp
  nlinarith [sq_nonneg ‖z‖]

/-- The literal real-vector constructor is a fixed bounded linear map.
This provides the final codomain conversion for physical vector modes. -/
noncomputable def realVectorCLM : ComplexVector →L[ℝ] ProblemStatement.Space :=
  ({ toFun := PhysicalCurlCovariance.realVector
     map_add' := by
       intro z w
       ext i
       simp [PhysicalCurlCovariance.realVector_apply]
     map_smul' := by
       intro c z
       ext i
       simp [PhysicalCurlCovariance.realVector_apply, Complex.real_smul] } :
    ComplexVector →ₗ[ℝ] ProblemStatement.Space).mkContinuous 3 realVector_norm_le

@[simp] theorem realVectorCLM_apply (z : ComplexVector) :
    realVectorCLM z = PhysicalCurlCovariance.realVector z := rfl

theorem norm_realVectorCLM_le : ‖realVectorCLM‖ ≤ 3 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) realVector_norm_le

end NavierStokes.CurrentPhysicalChartJets

/-! Merged from `NavierStokes.CurrentPhysicalModeGerms` (in a section, so its `open`s cannot leak). -/
section
/-!
# Normalized polar germs of the actual current particular modes

The native point below uses the actual common-cover index.  The ambient
germs retain the current solve, its chosen phase, and its Cartesian rotation.
-/

noncomputable section

namespace NavierStokes.CurrentPhysicalModeGerms

open Set Function Filter ProblemStatement
open CorrectionState CorrectionStep CorrectionInitialization
open scoped Topology ContDiff


abbrev Label (B N0 : ℕ) := ActualCurrentParticularPhysical.Label B N0

/-- The cover gap of the actual current-band graph. -/
noncomputable def commonGap (n : ℕ) : ℕ :=
  ChartScales.nativeIndex CorrectionInitialization.ActualPrimary.h n -
    CommonWindow.index CorrectionInitialization.ActualPrimary.h n

theorem commonGap_le (n : ℕ) :
    commonGap n ≤ ChartScales.nativeIndex CorrectionInitialization.ActualPrimary.h n :=
  Nat.sub_le _ _

theorem commonGap_index (n : ℕ) :
    ChartScales.nativeIndex CorrectionInitialization.ActualPrimary.h n - commonGap n =
      CommonWindow.index CorrectionInitialization.ActualPrimary.h n :=
  Nat.sub_sub_self (CommonWindow.index_le_native CorrectionInitialization.ActualPrimary.h n)

theorem liftXY_common (h : ℝ) (n d : ℕ) (w : SpaceTime) :
    PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift h n d w) =
      PhysicalGraphBounds.scaledRadial n w :=
  PhysicalGraphBounds.liftXY_physicalLift h n w

/-- The exact common-lift chart is the same cylindrical graph as the
one used by the current physical solve. -/
theorem cylinderAt_commonLift (h : ℝ) (n d : ℕ)
    (hd : d ≤ ChartScales.nativeIndex h n) {a : ℝ} (ha : 0 < a)
    (i : PolarCharts.Index) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    ActualSignedPhysicalData.cylinderAt a i (PhysicalWaveSum.commonLift h n d w) =
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
        (ChartScales.nativeIndex h n - d)).map
        (ResidualPolarGraph.cylindricalPoint a i n w) := by
  have hl : PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift h n d w) ∈
      PolarCharts.chartDomain a i := by
    rwa [liftXY_common]
  apply PhysicalResidualTZ.swapCylinder.injective
  change PhysicalResidualTZ.swapCylinder
    (ActualSignedPhysicalData.cylinderAt a i (PhysicalWaveSum.commonLift h n d w)) =
      PhysicalResidualTZ.graphMapTZ
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
          (ChartScales.nativeIndex h n - d)) (ResidualPolarGraph.cylindricalPoint a i n w)
  rw [ResidualPolarGraph.graphMapTZ_cylindricalPoint ha h i n d hd hw]
  apply Prod.ext
  · change PhysicalResidualTZ.swapSlow
      (ActualSignedPhysicalData.cylinderAt a i (PhysicalWaveSum.commonLift h n d w)).1 =
        PhysicalMeanJetBounds.graph h n d w
    rw [ActualSignedPhysicalData.cylinderAt_fst ha i hl]
    rfl
  · change (PolarCharts.chart a i
      (PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift h n d w))).2 =
        (PolarCharts.chart a i (PhysicalGraphBounds.scaledRadial n w)).2
    rw [liftXY_common]

theorem realVector_smul (c : ℝ) (v : HarmonicCalculus.ComplexVector) :
    PhysicalCurlCovariance.realVector (c • v) =
      c • PhysicalCurlCovariance.realVector v := by
  ext i
  fin_cases i <;> simp [PhysicalCurlCovariance.realVector, Complex.real_smul]

theorem radialProjection_eq_sqrt_smul (n : ℕ) (w : SpaceTime) :
    PhysicalGraphBounds.radialProjection w =
      Real.sqrt (ChartScales.Q n) • PhysicalGraphBounds.scaledRadial n w := by
  have hscale : Real.sqrt (ChartScales.Q n) * ChartScales.Q n ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (ChartScales.Q_pos n)]
    norm_num
  change PhysicalGraphBounds.radialProjection w =
    Real.sqrt (ChartScales.Q n) •
      (ChartScales.Q n ^ (-(1 / 2 : ℝ)) • PhysicalGraphBounds.radialProjection w)
  rw [smul_smul, hscale, one_smul]

theorem physical_chart_mem (n : ℕ) {a : ℝ} (i : PolarCharts.Index) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    w ∈ ActualMeanPotentialRealization.cartesianDomain (Real.sqrt (ChartScales.Q n) * a) i := by
  change PhysicalGraphBounds.radialProjection w ∈
    PolarCharts.chartDomain (Real.sqrt (ChartScales.Q n) * a) i
  rw [radialProjection_eq_sqrt_smul n w]
  exact CurrentPhysicalChartJets.chartDomain_smul (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) i hw

theorem physical_chart_angle (n : ℕ) {a : ℝ} (ha : 0 < a)
    (i : PolarCharts.Index) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    (PolarCharts.chart (Real.sqrt (ChartScales.Q n) * a) i
      (PhysicalGraphBounds.radialProjection w)).2 = ResidualPolarGraph.angle a i n w := by
  rw [radialProjection_eq_sqrt_smul n w]
  have hh := CurrentPhysicalChartJets.chart_smul ha
    (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) i hw
  have he := congrArg Prod.snd hh
  simpa only [ResidualPolarGraph.angle] using he

/-- The physical chart uses the same angular branch as the normalized
chart, with the physical radius restored. -/
theorem physical_polarCoordinates (n : ℕ) {a : ℝ} (ha : 0 < a)
    (i : PolarCharts.Index) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    PhysicalCurlCovariance.polarCoordinates (Real.sqrt (ChartScales.Q n) * a) i w =
      ResidualPolarGraph.cylindricalPoint a i n w := by
  have hp : PolarCharts.chart (Real.sqrt (ChartScales.Q n) * a) i
      (PhysicalGraphBounds.radialProjection w) =
        (PolarCharts.radius (PhysicalGraphBounds.radialProjection w), ResidualPolarGraph.angle a i n w) :=
    Prod.ext (ActualSignedPhysicalData.chart_radius
      (mul_pos (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) ha) i (physical_chart_mem n i hw))
      (physical_chart_angle n ha i hw)
  simp only [PhysicalCurlCovariance.polarCoordinates, PhysicalCurlCovariance.polarInput,
    hp, ResidualPolarGraph.cylindricalPoint]

/-- The current native map uses the common index, as opposed to the
larger native index of the unmodified lift. -/
theorem nativeMap_commonChart (n : ℕ) {a : ℝ} (ha : 0 < a)
    (i : PolarCharts.Index) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    PhysicalParticularWave.nativeMap ActualPrimary.h (ChartScales.Q n)
      (CommonWindow.index ActualPrimary.h n)
      (PhysicalCurlCovariance.polarCoordinates (Real.sqrt (ChartScales.Q n) * a) i w) =
        PhysicalParticularWave.waveEquiv
          (ActualSignedPhysicalData.cylinderAt a i
            (PhysicalWaveSum.commonLift ActualPrimary.h n (commonGap n) w)) := by
  rw [physical_polarCoordinates n ha i hw, PhysicalParticularWave.nativeMap,
    ← commonGap_index n]
  exact congrArg PhysicalParticularWave.waveEquiv
    (cylinderAt_commonLift ActualPrimary.h n (commonGap n) (commonGap_le n) ha i hw).symm

theorem rotation_commonLift (h : ℝ) (n d : ℕ) (w : SpaceTime) :
    CartesianCopySource.rotationMap (PhysicalGraphBounds.radialProjection w) =
      CartesianCopySource.rotationMap
        (PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift h n d w)) := by
  rw [liftXY_common]
  exact (CurrentPhysicalChartJets.rotationMap_smul
    (Real.rpow_pos_of_pos (ChartScales.Q_pos n) (-(1 / 2 : ℝ)))
    (PhysicalGraphBounds.radialProjection w)).symm

variable {B N0 : ℕ}

/-- Pointwise equality to the literal current potential on a valid
normalized polar chart. -/
theorem localPotentialMode_eq (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier ActualPrimary.h n)
    (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    ActualCurrentParticularPhysical.localPotentialMode x l j n w =
      ChartScales.Q n ^ (-ActualPrimary.h) • PhysicalCurlCovariance.realVector
        (CartesianCopySource.rotationMap
          (PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift ActualPrimary.h n (commonGap n) w))
          (ActualCurrentParticularPhysical.nativePotential x l j n
            (PhysicalParticularWave.waveEquiv (ActualSignedPhysicalData.cylinderAt a i
              (PhysicalWaveSum.commonLift ActualPrimary.h n (commonGap n) w))))) := by
  unfold ActualCurrentParticularPhysical.localPotentialMode
  rw [ActualCurrentParticularPhysical.periodic_cylinderPoint_eq_chart
    (ActualCurrentParticularPhysical.cylindricalPotential_periodic x l j hf n)
    (mul_pos (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) ha) i (physical_chart_mem n i hw)]
  unfold ActualCurrentParticularPhysical.cylindricalPotential
  rw [nativeMap_commonChart n ha i hw, rotation_commonLift ActualPrimary.h n (commonGap n) w,
    map_smul, realVector_smul]

theorem localPressureMode_eq (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier ActualPrimary.h n)
    (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    ActualCurrentParticularPhysical.localPressureMode x l j n w =
      ChartScales.Q n ^ (-2 * CoordinateAlgebra.A ActualPrimary.h) *
        (ActualCurrentParticularPhysical.nativePressure x l j n
          (PhysicalParticularWave.waveEquiv (ActualSignedPhysicalData.cylinderAt a i
            (PhysicalWaveSum.commonLift ActualPrimary.h n (commonGap n) w)))).re := by
  rw [ActualCurrentParticularPhysical.localPressureMode_eq_chart x l j hf n
    (mul_pos (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) ha) i (physical_chart_mem n i hw)]
  unfold ActualCurrentParticularPhysical.cylindricalPressure
  rw [nativeMap_commonChart n ha i hw]

/-- Ambient germ equality, suitable for ordinary Cartesian derivatives
of every order, with the actual common-cover lift. -/
theorem localPotentialMode_germ (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier ActualPrimary.h n)
    (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    ActualCurrentParticularPhysical.localPotentialMode x l j n =ᶠ[𝓝 w] fun y =>
      ChartScales.Q n ^ (-ActualPrimary.h) • PhysicalCurlCovariance.realVector
        (CartesianCopySource.rotationMap
          (PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift ActualPrimary.h n (commonGap n) y))
          (ActualCurrentParticularPhysical.nativePotential x l j n
            (PhysicalParticularWave.waveEquiv (ActualSignedPhysicalData.cylinderAt a i
              (PhysicalWaveSum.commonLift ActualPrimary.h n (commonGap n) y))))) := by
  filter_upwards [ResidualPolarGraph.eventually_chartDomain i n hw] with y hy
  exact localPotentialMode_eq x l j hf n ha i hy

theorem localPressureMode_germ (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) (hf : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier ActualPrimary.h n)
    (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    ActualCurrentParticularPhysical.localPressureMode x l j n =ᶠ[𝓝 w] fun y =>
      ChartScales.Q n ^ (-2 * CoordinateAlgebra.A ActualPrimary.h) *
        (ActualCurrentParticularPhysical.nativePressure x l j n
          (PhysicalParticularWave.waveEquiv (ActualSignedPhysicalData.cylinderAt a i
            (PhysicalWaveSum.commonLift ActualPrimary.h n (commonGap n) y)))).re := by
  filter_upwards [ResidualPolarGraph.eventually_chartDomain i n hw] with y hy
  exact localPressureMode_eq x l j hf n ha i hy

end NavierStokes.CurrentPhysicalModeGerms
end

/-! Merged from `NavierStokes.ActualCurrentCarrierJets` (in a section, so its `open`s cannot leak). -/
section
/-!
# Uniform phase jets for the actual current-chart copies

The functions below are literal reindexings of the selected common phase.
Positive jets have a fixed `Q^(-2h)` loss, uniformly before the label and
band are selected. No bound on the unbounded phase value is asserted.
-/

noncomputable section

namespace NavierStokes.ActualCurrentCarrierJets

open Set Function Filter CorrectionInitialization
open scoped Topology ContDiff

abbrev Label (B N0 : ℕ) := ActualPrimaryBounds.SignedLabel B N0
abbrev Native := ActualParticularBackground.Native
abbrev FullPoint := ActualPrimary.FullPoint

variable {B N0 : ℕ}

/-- The actual common phase in the current free-angle native coordinates. -/
noncomputable def phase (l : Label B N0) (n : ℕ) (z : Native) : ℝ :=
  (ActualPrimary.chartCoefficients l.1 l.2).phase n
    (ActualParticularBackground.nativeToFull z)

/-- The same phase with the actual base carrier already included. -/
noncomputable def weightedPhase (l : Label B N0) (n : ℕ) (z : Native) : ℝ :=
  ActualPhaseJetBounds.weightedPhase l n (ActualParticularBackground.nativeToFull z)

theorem weightedPhase_eq (l : Label B N0) (n : ℕ) :
    weightedPhase l n = fun z => (ChartScales.carrier ActualPrimary.h n : ℝ) * phase l n z := rfl

/-- The oscillatory factor used by the actual harmonic copy is exactly
the character of the carrier-weighted current phase. -/
theorem harmonic_carrier_eq (l : Label B N0) (n : ℕ) (j : ℤ) :
    HarmonicCalculus.carrier ((j : ℝ) * (ChartScales.carrier ActualPrimary.h n : ℝ))
      (phase l n) = PhysicalGraphBounds.character (j : ℝ) ∘ weightedPhase l n := by
  funext z
  simp only [HarmonicCalculus.carrier, HarmonicCalculus.phaseFactor,
    PhysicalGraphBounds.character, PhysicalGraphBounds.phaseFactor, Function.comp_apply,
    weightedPhase_eq, Complex.ofReal_mul]
  congr 1
  ring

theorem actualCarrier_phase
    (b : Label B N0 → CorrectionState.HarmonicBlock CorrectionStep.CyclePoint)
    (hb : ∀ l, CorrectionStep.SameCarrier (b l) (ActualParticularBackground.primaryBlock l))
    (j : ℤ) (l : Label B N0) (n : ℕ) :
    (ActualParticularBackground.carrier b j l).phase n = phase l n :=
  congrFun (ActualParticularBackground.carrier_phase b hb j l) n

theorem actualCarrier_character
    (b : Label B N0 → CorrectionState.HarmonicBlock CorrectionStep.CyclePoint)
    (hb : ∀ l, CorrectionStep.SameCarrier (b l) (ActualParticularBackground.primaryBlock l))
    (j : ℤ) (l : Label B N0) (n : ℕ) :
    HarmonicCalculus.carrier ((ActualParticularBackground.carrier b j l).frequency n)
      ((ActualParticularBackground.carrier b j l).phase n) =
        PhysicalGraphBounds.character (j : ℝ) ∘ weightedPhase l n := by
  rw [actualCarrier_phase b hb j l n, ActualParticularBackground.carrier_frequency b hb j l]
  exact harmonic_carrier_eq l n j


theorem mem_cells_iff (n : ℕ) (i : ActualPhaseJetBounds.CopyIndex B N0) (z : Native) :
    z ∈ ParticularPaddedBackground.cells n i ↔
      ActualParticularBackground.nativeToFull z ∈ ActualPhaseJetBounds.phaseCell n i := Iff.rfl

private theorem smoothNear_congr {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {x : E} (hf : LocalPhysicalCopyBounds.SmoothNear f x)
    (he : g =ᶠ[𝓝 x] f) : LocalPhysicalCopyBounds.SmoothNear g x := by
  obtain ⟨U, hU, hx, hf⟩ := hf
  obtain ⟨V, hVe, hV, hxV⟩ := mem_nhds_iff.mp he
  exact ⟨U ∩ V, hU.inter hV, ⟨hx,hxV⟩,
    (hf.mono inter_subset_left).congr (fun y hy => hVe hy.2)⟩

/-- The one open neighborhood is obtained from the actual analytic phase
cell, then intersected with the genuine periodic-copy germ neighborhood. -/
theorem full_weightedPhase_smoothNear {n : ℕ} {i : ActualPhaseJetBounds.CopyIndex B N0}
    {x : FullPoint} (hx : x ∈ ActualPhaseJetBounds.phaseCell n i) :
    LocalPhysicalCopyBounds.SmoothNear (ActualPhaseJetBounds.weightedPhase i.1 n) x := by
  let g : FullPoint → PhaseCalculus.Slow × ℝ := fun y =>
    ((ActualPrimaryBounds.fullCopy i.1 n i.2 y).1,
      (ActualPrimaryBounds.fullCopy i.1 n i.2 y).2.2)
  have hg : ContDiff ℝ ∞ g := by
    have he : g = fun y => ActualPrimaryBounds.slotLinear i.1 n y +
        ActualPrimaryBounds.slotOfNative (ActualPrimaryBounds.copyPoint i.1 n i.2 0) :=
      funext (ActualPrimaryBounds.slotCopy_affine i.1 n i.2)
    rw [he]
    exact (ActualPrimaryBounds.slotLinear i.1 n).contDiff.add contDiff_const
  let U := g ⁻¹' ActualPhaseJetBounds.jetDomain.carrier i.1
  have hU : IsOpen U := (ActualPhaseJetBounds.jetDomain.isOpen i.1).preimage hg.continuous
  have hxU : x ∈ U := ActualPhaseJetBounds.phaseCell_maps hx
  have hr : ContDiffOn ℝ ∞ (fun y => ActualPhaseJetBounds.nativeRemainder i.1 (g y)) U :=
    (ActualPhaseJetBounds.nativeRemainder_polynomial.smooth i.1).comp
      hg.contDiffOn (fun _ hy => hy)
  have hl : ContDiffOn ℝ ∞ (ActualPhaseJetBounds.localPhase n i) U := by
    have hs := (((ActualPhaseJetBounds.phaseLinear i.1 n).contDiff.add
      (contDiff_const (c := ActualPhaseJetBounds.phaseOffset n i))).contDiffOn).add hr
    exact hs.congr (fun y _ => ActualPhaseJetBounds.localPhase_decomposition n i y)
  have hm : LocalPhysicalCopyBounds.SmoothNear
      (fun y => (ChartScales.carrier ActualPrimary.h (BaseChartJets.cellBand i.1.2) : ℝ) *
        ActualPhaseJetBounds.localPhase n i y) x :=
    ⟨U, hU, hxU, contDiffOn_const.mul hl⟩
  exact smoothNear_congr hm (ActualPhaseJetBounds.weightedPhase_germ hx)

theorem weightedPhase_smoothNear {n : ℕ} {i : ActualPhaseJetBounds.CopyIndex B N0}
    {z : Native} (hz : z ∈ ParticularPaddedBackground.cells n i) :
    LocalPhysicalCopyBounds.SmoothNear (weightedPhase i.1 n) z := by
  obtain ⟨U, hU, hx, hf⟩ := full_weightedPhase_smoothNear ((mem_cells_iff n i z).mp hz)
  exact ⟨ActualParticularBackground.nativeToFull ⁻¹' U,
    hU.preimage ActualParticularBackground.nativeToFull.continuous, hx,
    hf.comp ActualParticularBackground.nativeToFull.toContinuousLinearEquiv.contDiff.contDiffOn
      (fun _ hy => hy)⟩


/-- Constants are chosen before the active label, band, copy, point, and
positive derivative order. Reindexing is an isometry and adds no loss. -/
theorem weightedPhase_positive_jets (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n (i : ActualPhaseJetBounds.CopyIndex B N0) z,
      z ∈ ParticularPaddedBackground.cells n i → ∀ r, 1 ≤ r → r ≤ m →
      ‖iteratedFDeriv ℝ r (weightedPhase i.1 n) z‖ ≤
        C * ChartScales.S n ^ p * ChartScales.Q n ^ (-(2 * ActualPrimary.h)) := by
  obtain ⟨C,hC,p,hb⟩ := ActualPhaseJetBounds.weightedPhase_positive_jets (B := B) (N0 := N0) m
  refine ⟨C,hC,p,?_⟩
  intro n i z hz r hr hrm
  change ‖iteratedFDeriv ℝ r (fun y => ActualPhaseJetBounds.weightedPhase i.1 n
    (ActualParticularBackground.nativeToFull y)) z‖ ≤ _
  rw [StateReindex.norm_iteratedFDeriv_pull]
  exact hb n i _ ((mem_cells_iff n i z).mp hz) r hr hrm

theorem phase_positive_jets (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n (i : ActualPhaseJetBounds.CopyIndex B N0) z,
      z ∈ ParticularPaddedBackground.cells n i → ∀ r, 1 ≤ r → r ≤ m →
      ‖iteratedFDeriv ℝ r (phase i.1 n) z‖ ≤
        C * ChartScales.S n ^ p * ChartScales.Q n ^ (-(2 * ActualPrimary.h)) := by
  obtain ⟨C,hC,p,hb⟩ := ActualPhaseJetBounds.phase_positive_jets (B := B) (N0 := N0) m
  refine ⟨C,hC,p,?_⟩
  intro n i z hz r hr hrm
  change ‖iteratedFDeriv ℝ r (fun y => (ActualPrimary.chartCoefficients i.1.1 i.1.2).phase n
    (ActualParticularBackground.nativeToFull y)) z‖ ≤ _
  rw [StateReindex.norm_iteratedFDeriv_pull]
  exact hb n i _ ((mem_cells_iff n i z).mp hz) r hr hrm


theorem weightedPhase_smoothNear_controlPatch (l : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {z : Native}
    (hz : z ∈ ActualParticularStageControls.controlPatch l n k) :
    LocalPhysicalCopyBounds.SmoothNear (weightedPhase l n) z :=
  weightedPhase_smoothNear (n := n) (i := (l,k)) (z := z)
    (ActualParticularStageControls.controlPatch_subset_padded l n k hz)


/-- The quantitative statement on the actual retained current-copy cells.
The cell hypothesis already supplies activeness; no native-band interior
or separate phase-jet assumption is added. -/
theorem weightedPhase_positive_jets_controlPatch (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ (l : Label B N0) n k z,
      z ∈ ActualParticularStageControls.controlPatch l n k → ∀ r, 1 ≤ r → r ≤ m →
      ‖iteratedFDeriv ℝ r (weightedPhase l n) z‖ ≤
        C * ChartScales.S n ^ p * ChartScales.Q n ^ (-(2 * ActualPrimary.h)) := by
  obtain ⟨C,hC,p,hb⟩ := weightedPhase_positive_jets (B := B) (N0 := N0) m
  exact ⟨C,hC,p,fun l n k z hz r hr hrm =>
    hb n (l,k) z (ActualParticularStageControls.controlPatch_subset_padded l n k hz) r hr hrm⟩


end NavierStokes.ActualCurrentCarrierJets
end

/-! Merged from `NavierStokes.CurrentModeGeometry` (in a section, so its `open`s cannot leak). -/
section
/-!
# Geometry of the actual current-mode evaluation point

The physical validity band and the closed nominal radial interval place
the normalized Cartesian coordinates in a fixed compact annulus.  The
same current common-cover chart has the actual native slow domain and
exactly the physical profile radius.
-/

noncomputable section

namespace NavierStokes.CurrentModeGeometry

open Set Function Filter ProblemStatement CorrectionInitialization
open scoped Topology ContDiff


noncomputable def chartInner : ℝ := PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 4

noncomputable def chartOuter : ℝ := 2 * PrimaryTargetBounds.rightRadius ActualPrimary.nominal

theorem chartInner_pos : 0 < chartInner :=
  div_pos (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal) (by norm_num)



theorem band_q_comparison (n : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band ActualPrimary.h n) :
    PhysicalWaveSum.physicalQ ActualPrimary.h w / 2 ≤ ChartScales.Q n ∧
      ChartScales.Q n ≤ 2 * PhysicalWaveSum.physicalQ ActualPrimary.h w := by
  constructor <;> linarith [hw.2.1, hw.2.2]

/-- The annulus is derived from the actual physical ratio, independently
of any field support or coherent-family assumption. -/
theorem scaledRadial_mem_annulus (n : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band ActualPrimary.h n)
    (hr : ActualCurrentWaveSupport.profileRadius ActualPrimary.h w ∈
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)) :
    PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus chartInner chartOuter := by
  have hc := band_q_comparison n hw
  have hlen := PhysicalMeanJetBounds.graph_length_bounds ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half n 0 hw.1 hc.1 hc.2
  have hell := PhysicalMeanJetBounds.graph_length_pos ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half n 0 hw.1
  have hratio : (PhysicalMeanJetBounds.graph ActualPrimary.h n 0 w).1 /
      VariableGaugeMean.qLength (2 * ActualPrimary.h)
        (PhysicalMeanJetBounds.graph ActualPrimary.h n 0 w).2.1 ∈
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal) := by
    rw [ActualCurrentWaveSupport.graph_profileRadius_eq ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half n 0 hw.1]
    exact hr
  have hloR := (le_div_iff₀ hell).mp hratio.1
  have hhiR := (div_le_iff₀ hell).mp hratio.2
  have ha := PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal
  have hb := PrimaryTargetBounds.rightRadius_pos ActualPrimary.nominal
  have hlow : PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 2 ≤
      (PhysicalMeanJetBounds.graph ActualPrimary.h n 0 w).1 := by nlinarith [hlen.1]
  have hupp : (PhysicalMeanJetBounds.graph ActualPrimary.h n 0 w).1 ≤
      2 * PrimaryTargetBounds.rightRadius ActualPrimary.nominal := by nlinarith [hlen.2]
  rw [PhysicalMeanJetBounds.graph_radius] at hlow hupp
  refine ⟨?_, ?_⟩
  · simpa only [chartOuter, Metric.mem_closedBall, dist_zero_right] using
      (PolarCharts.norm_le_radius _).trans hupp
  · change PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 4 ≤
      ‖PhysicalGraphBounds.scaledRadial n w‖
    linarith only [hlow, PolarCharts.radius_le_two_norm (PhysicalGraphBounds.scaledRadial n w)]

/-- The literal current common-cover evaluation point used in the
physical mode estimates. -/
noncomputable def point (a : ℝ) (i : PolarCharts.Index) (n : ℕ) (w : SpaceTime) :
    PhysicalParticularWave.WaveSpace :=
  CurrentPhysicalChartJets.chartMap a i
    (PhysicalWaveSum.commonLift ActualPrimary.h n (CurrentPhysicalModeGerms.commonGap n) w)

theorem point_eq_nativeMap (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {w : SpaceTime} (hc : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    point a i n w = PhysicalParticularWave.nativeMap ActualPrimary.h (ChartScales.Q n)
      (CommonWindow.index ActualPrimary.h n)
      (PhysicalCurlCovariance.polarCoordinates (Real.sqrt (ChartScales.Q n) * a) i w) :=
  (CurrentPhysicalModeGerms.nativeMap_commonChart n ha i hc).symm

theorem point_mem_nativeDomain (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band ActualPrimary.h n)
    (hc : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    point a i n w ∈ ActualCurrentParticularPhysical.nativeDomain := by
  rw [point_eq_nativeMap n ha i hc,
    ActualCurrentParticularPhysical.nativeMap_polar_mem_iff]
  exact ⟨ActualCurrentWaveSupport.nativePoint_parameterDomain n hw, mem_univ _⟩

theorem point_profileRadius (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {w : SpaceTime} (ht : w.1 < 1)
    (hc : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm (point a i n w)) =
      ActualCurrentWaveSupport.profileRadius ActualPrimary.h w := by
  rw [point_eq_nativeMap n ha i hc, CurrentPhysicalModeGerms.physical_polarCoordinates n ha i hc]
  have he : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm
      (PhysicalParticularWave.nativeMap ActualPrimary.h (ChartScales.Q n)
        (CommonWindow.index ActualPrimary.h n) (ResidualPolarGraph.cylindricalPoint a i n w))) =
      ActualCoreSupport.radialRatio
        (ActualCarrierTransport.associatedPoint
          (ActualCurrentParticularPhysical.nativePoint n w).1.1
          (ActualCurrentParticularPhysical.nativePoint n w).2) := by
    change (PhysicalParticularWave.nativeMap ActualPrimary.h (ChartScales.Q n)
        (CommonWindow.index ActualPrimary.h n) (ResidualPolarGraph.cylindricalPoint a i n w)).1.1.1 /
        VariableGaugeMean.qLength (2 * ActualPrimary.h)
          (PhysicalParticularWave.nativeMap ActualPrimary.h (ChartScales.Q n)
            (CommonWindow.index ActualPrimary.h n) (ResidualPolarGraph.cylindricalPoint a i n w)).1.1.2 =
      (ActualCurrentParticularPhysical.nativePoint n w).1.1.1 /
        VariableGaugeMean.qLength (2 * ActualPrimary.h)
          (ActualCurrentParticularPhysical.nativePoint n w).1.1.2
    simp only [PhysicalParticularWave.nativeMap, PhysicalParticularWave.waveEquiv_apply,
      PhysicalResidualBridge.ScaledGraph.map, ResidualPolarGraph.cylindricalPoint,
      ActualCurrentParticularPhysical.nativePoint, ActualCurrentParticularPhysical.cylinderPoint,
      AxisymmetricResidual.pack_zero, AxisymmetricResidual.pack_two]
  rw [he, ActualCurrentWaveSupport.nativePoint_profileRadius n ht]


end NavierStokes.CurrentModeGeometry
end


noncomputable section

namespace NavierStokes.ActualCurrentParticularBounds

open Set Function Filter ProblemStatement WeightedClasses HarmonicCalculus LinearWaveBounds
open scoped Topology ContDiff BigOperators


private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

/-! ## The literal native potential coefficient -/

section NativePotential

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : StripData E} {cells : ℕ → I → Set E} {envelope : ℕ → I → E → ℝ}
  {α κ : ℝ} {d : GraphDirections E} {a : LocalizedWaveBounds.WaveFamily E I}

theorem potential_local_class
    (hin : LocalizedWaveBounds.InputBounds s cells envelope α κ d a)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n i x, x ∈ s.domain → x ∈ cells n i → b ≤ ‖a.normal s d n i x‖)
    (hupper : ∀ n i x, x ∈ s.domain → x ∈ cells n i → ‖a.normal s d n i x‖ ≤ M)
    (hfreq : LocalizedWaveBounds.LocalUnweighted s cells (1 / 2)
      (fun n i _ => 1 / a.frequency n i)) :
    LocalizedWaveBounds.LocalWave s cells envelope (α + 1 / 2)
      (fun n i x => CurlClassBounds.inverseCarrier (a.frequency n i) •
        CurlClassBounds.normalCoefficient (a.normal s d n i x) (a.amplitude n i x)) := by
  have hc := hin.normalCoefficient_class hb hlower hupper
  have hi := (LocalizedWaveBounds.unweighted_smul hfreq hc).map
    (Complex.I • ContinuousLinearMap.id ℝ ComplexVector)
  rw [show (1 / 2 : ℝ) + α = α + 1 / 2 by ring] at hi
  apply hi.congr
  intro n i x
  ext j
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply,
    Pi.smul_apply, Complex.real_smul, smul_eq_mul, CurlClassBounds.inverseCarrier]
  push_cast
  ring

end NativePotential

section CommonPotential

variable {E L I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def strippedPotential (a : PeriodizedWaveBounds.CopyData E I)
    (s : StripData E) (d : GraphDirections E) (n : ℕ) (x : E) : ComplexVector :=
  CurlClassBounds.inverseCarrier (a.background.frequency n) •
    CurlClassBounds.normalCoefficient (a.background.normal s d n x) (a.common.amplitude n x)

/-- The actual common potential coefficient inherits the inverse-carrier
gain. The native normal estimates are used only on their control cells;
the remaining portions are handled by actual amplitude zero germs. -/
theorem common_potential_class
    (a : L → PeriodizedWaveBounds.CopyData E I) (K : L → PeriodizedWaveBounds.Cells E I)
    (hs : ∀ l n i, support ((a l).cutoff n i) ⊆ (K l).carrier n i)
    (C : L → ℕ → I → Set E) {s : StripData E} {d : GraphDirections E}
    {W : L → ℕ → E → ℝ} {α κ : ℝ}
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hin : LocalizedWaveBounds.InputBounds s (fun n (i : L × I) => C i.1 n i.2)
      (fun n i x => W i.1 n x) α κ d (LocalizedWaveBounds.jointNativeFamily a))
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ l n i x, x ∈ s.domain → x ∈ C l n i → b ≤ ‖(a l).background.normal s d n x‖)
    (hupper : ∀ l n i x, x ∈ s.domain → x ∈ C l n i → ‖(a l).background.normal s d n x‖ ≤ M)
    (hfreq : LocalizedWaveBounds.LocalUnweighted s (fun n (i : L × I) => C i.1 n i.2)
      (1 / 2) (fun n i _ => 1 / (a i.1).background.frequency n))
    (hcover : ∀ l n i x, x ∈ s.domain → x ∈ (K l).carrier n i → x ∈ C l n i ∨
      (((a l).localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0)) :
    LabelSumBounds.UniformWaveClass s W (α + 1 / 2)
      (fun l => strippedPotential (a l) s d) := by
  have hp := potential_local_class hin hb
    (fun n i x hx hi => hlower i.1 n i.2 x hx hi)
    (fun n i x hx hi => hupper i.1 n i.2 x hx hi) hfreq
  have hp' := hp.enlarge (K := fun n (i : L × I) => (K i.1).carrier n i.2) (by
    intro n i x hx hi
    rcases hcover i.1 n i.2 x hx hi with h | hz
    · exact Or.inl h
    · right
      filter_upwards [hz] with y hy
      change CurlClassBounds.inverseCarrier _ •
        CurlClassBounds.normalCoefficient _ (((a i.1).localized i.2).amplitude n y) = 0
      rw [hy]
      simp [CurlClassBounds.normalCoefficient, CurlClassBounds.normalCross])
  have hpj : PeriodizedWaveBounds.UniformLocalJets s
      (fun l n x => Real.sqrt (s.zeta x) * W l n x) (α + 1 / 2)
      (fun l n i => (K l).carrier n i)
      (fun l n i x => CurlClassBounds.inverseCarrier ((a l).background.frequency n) •
        CurlClassBounds.normalCoefficient ((a l).background.normal s d n x)
          (((a l).localized i).amplitude n x)) :=
    hp'.to_uniformLocalJets
  apply PeriodizedWaveBounds.uniformClass_of_local_germs
    (fun l n x hx => mul_nonneg (Real.sqrt_nonneg _) (hW l n x hx)) hpj
  intro l n x hx
  classical
  by_cases hi : ∃ i, x ∈ (K l).carrier n i
  · obtain ⟨i, hi⟩ := hi
    refine Or.inl ⟨i, hi, ?_⟩
    filter_upwards [(a l).common_amplitude_germ (K l) (hs l) n hi] with y hy
    change CurlClassBounds.inverseCarrier _ •
      CurlClassBounds.normalCoefficient _ ((a l).common.amplitude n y) = _
    rw [hy]
  · right
    filter_upwards [((a l).common_zero_germs (K l) (hs l) (not_exists.mp hi)).1] with y hy
    change CurlClassBounds.inverseCarrier _ •
      CurlClassBounds.normalCoefficient _ ((a l).common.amplitude n y) = 0
    rw [hy]
    simp [CurlClassBounds.normalCoefficient, CurlClassBounds.normalCross]

end CommonPotential

/-! The supplied source below is the actual current harmonic residual.
The normal-inverse and periodization estimates are derived here. -/

section ActualNative

open CorrectionStep

variable {B N0 : ℕ}

abbrev Label (B N0 : ℕ) := ActualParticularStageControls.Label B N0
abbrev Native := ActualParticularStageControls.Native

noncomputable def nativeStrip : StripData Native :=
  CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip ActualParticularStageControls.slowStrip)

noncomputable def potentialCoefficient (x : CycleState (Label B N0)) (l : Label B N0)
    (j : ℤ) : ℕ → Native → ComplexVector :=
  strippedPotential (ActualParticularStageControls.data x l j) nativeStrip
    (ActualParticularStageControls.directions (B := B))

theorem actual_potential_coefficient_class (x : CycleState (Label B N0))
    (hx : ActualParticularStageControls.PreservesCarriers x)
    (hs : ActualParticularStageControls.InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass nativeStrip ActualParticularStageControls.nativeEnvelope
      α (ActualParticularStageControls.currentSource x j)) :
    LabelSumBounds.UniformWaveClass nativeStrip ActualParticularStageControls.nativeEnvelope
      (α + 1 / 2) (fun l => potentialCoefficient x l j) := by
  have hr := ActualParticularStageControls.raw_jets x
    (ActualParticularStageControls.preserves_frequency hx) j hj H
  have hi := CorrectionStep.uniform_localInput_of_coefficients
    (fun l => ActualParticularStageControls.data x l j)
    (ActualParticularStageControls.actual_background_inputs x hx hN j)
    (fun l n z _ => ActualParticularStageControls.envelope_nonneg l n (z.1.1, z.2)) hr.1 hr.2
  have hin := hi.with_cutoff
    (LocalizedWaveBounds.LocalClass.of_uniformLocalJets (fun _ _ _ _ => zero_le_one)
      (ActualParticularStageControls.cutoff_jets x j))
  exact common_potential_class (fun l => ActualParticularStageControls.data x l j)
    ActualParticularStageControls.carrierCells
    (fun l n k => ActualParticularStageControls.data_cutoff_support x l j n k)
    ActualParticularStageControls.controlPatch
    (fun l n z _ => ActualParticularStageControls.envelope_nonneg l n (z.1.1, z.2)) hin
    (ActualPrimaryBounds.normalFloor_pos B N0)
    (fun l n k z hz hk => (ActualParticularStageControls.actual_normal_range x hx l j n k hz hk).1)
    (fun l n k z hz hk => (ActualParticularStageControls.actual_normal_range x hx l j n k hz hk).2)
    (ActualParticularStageControls.actual_inverse_frequency x hx j)
    (fun l n k z hz hk =>
      (ActualParticularStageControls.data_control_cover x hs hN l j n k hz hk).imp_right And.left)

theorem actual_pressure_coefficient_class (x : CycleState (Label B N0))
    (hx : ActualParticularStageControls.PreservesCarriers x)
    (hs : ActualParticularStageControls.InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass nativeStrip ActualParticularStageControls.nativeEnvelope
      α (ActualParticularStageControls.currentSource x j)) :
    LabelSumBounds.UniformWaveClass nativeStrip ActualParticularStageControls.nativeEnvelope
      (α + 1 / 2) (fun l => (ActualParticularStageControls.data x l j).common.pressure) :=
  (ActualParticularStageControls.common_bounds x hx hs hN j hj H).2.2.1

theorem native_envelope_le_one (l : Label B N0) (n : ℕ) (z : Native) :
    ActualParticularStageControls.nativeEnvelope l n z ≤ 1 :=
  ActualPrimaryBounds.envelope_le_one l n
    (ActualSignedGeometry.swapParameter z.1.1, z.2)

theorem native_flat_geometry :
    ∃ cL cR L : ℝ, ∃ ρ : Native → ℝ,
      PhysicalClassBounds.FlatGeometry nativeStrip cL cR L ρ := by
  let W := CorrectionInitialization.ActualPrimary.nominal
  let U := CorrectionInitialization.ActualPrimary.standardRegion
  have hg := PhysicalClassBounds.movingStrip_flatGeometry (b := PrimaryTargetBounds.rightRadius W) U
    (PrimaryTargetBounds.leftRadius_pos W)
    (div_pos (FinalSlowBase.edgeExponent_pos W) (by norm_num : (0 : ℝ) < 4))
    zero_lt_one (ChartScales.epsilon CorrectionInitialization.ActualPrimary.h)
    BaseContextAssembly.slowScale (ChartScales.epsilon_pos _)
    (ChartScales.epsilon_le_one _ CorrectionInitialization.ActualPrimary.outgoing.data.h_pos.le)
    BaseContextAssembly.one_le_slowScale
  refine ⟨_, _, WeightedRadialPrimitive.logLength
    (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W),
    fun z => WeightedRadialPrimitive.logPosition
    (PrimaryTargetBounds.leftRadius W)
    (LocalSignedRequest.profileMap (2 * CorrectionInitialization.ActualPrimary.h)
      (ActualParticularStageControls.slowInsert z.1.1)).1,
    hg.left_pos, hg.right_pos, ?_, ?_, ?_⟩
  · intro z hz
    exact hg.position _ hz
  · intro z hz
    exact hg.delta_eq _ hz
  · intro z hz
    exact hg.zeta_eq _ hz

/-- The actual moving flat weight removes every inverse-edge power before
passing to the physical graph. -/
theorem native_source_bounds {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} {f : Label B N0 → ℕ → Native → E}
    (hf : LabelSumBounds.UniformWaveClass nativeStrip
      ActualParticularStageControls.nativeEnvelope α f) :
    LocalPhysicalCopyBounds.LocalSourceBounds nativeStrip
      CorrectionInitialization.ActualPrimary.h α
      (fun l n z => Real.sqrt (nativeStrip.zeta z) *
        ActualParticularStageControls.nativeEnvelope l n z) f := by
  refine ⟨hf, native_flat_geometry, ⟨1 / 2, by norm_num, ?_⟩, fun _ => rfl,
    ⟨1, le_rfl, 1, ?_⟩⟩
  · intro l n z hz
    exact (mul_le_of_le_one_right (Real.sqrt_nonneg _) (native_envelope_le_one l n z)).trans_eq
      (Real.sqrt_eq_rpow _)
  · intro n hn
    have hS := PhysicalGraphBounds.S_ge_one (show 1 ≤ n by omega)
    change max 1 (ChartScales.S n) ≤ 1 * ChartScales.S n ^ 1
    simp only [max_eq_right hS, pow_one, one_mul, le_refl]

theorem common_control_or_zero (x : CycleState (Label B N0))
    (hs : ActualParticularStageControls.InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Label B N0) (j : ℤ) (n : ℕ) {z : Native} (hz : z ∈ nativeStrip.domain) :
    (∃ k, z ∈ ActualParticularStageControls.controlPatch l n k) ∨
      (potentialCoefficient x l j n =ᶠ[𝓝 z] fun _ => 0) ∧
      ((ActualParticularStageControls.data x l j).common.pressure n =ᶠ[𝓝 z] fun _ => 0) := by
  classical
  let a := ActualParticularStageControls.data x l j
  let K := ActualParticularStageControls.carrierCells l
  have hcut := ActualParticularStageControls.data_cutoff_support x l j
  have hzero (ha : a.common.amplitude n =ᶠ[𝓝 z] fun _ => 0)
      (hp : a.common.pressure n =ᶠ[𝓝 z] fun _ => 0) :
      (potentialCoefficient x l j n =ᶠ[𝓝 z] fun _ => 0) ∧
      (a.common.pressure n =ᶠ[𝓝 z] fun _ => 0) := by
    refine ⟨?_, hp⟩
    filter_upwards [ha] with y hy
    change CurlClassBounds.inverseCarrier _ •
      CurlClassBounds.normalCoefficient _ (a.common.amplitude n y) = 0
    rw [hy]
    simp [CurlClassBounds.normalCoefficient, CurlClassBounds.normalCross]
  by_cases hi : ∃ k, z ∈ K.carrier n k
  · obtain ⟨k, hk⟩ := hi
    rcases ActualParticularStageControls.data_control_cover x hs hN l j n k hz hk with hc | h0
    · exact Or.inl ⟨k, hc⟩
    · right
      exact hzero ((a.common_amplitude_germ K hcut n hk).trans h0.1)
        ((a.common_pressure_germ K hcut n hk).trans h0.2)
  · exact Or.inr (hzero (a.common_zero_germs K hcut (not_exists.mp hi)).1
      (a.common_zero_germs K hcut (not_exists.mp hi)).2)

end ActualNative

/-! ## Local finite jets of the actual oscillatory exponential -/

section Carrier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem character_comp_positive_jets {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (x : E) (m : ℕ) {c B M : ℝ} (hB : 1 ≤ B) (hM : 1 ≤ M) (hc : |c| ≤ M)
    (hΦb : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i Φ x‖ ≤ B) :
    ∀ k ≤ m, ‖iteratedFDeriv ℝ k (PhysicalGraphBounds.character c ∘ Φ) x‖ ≤
      (m.factorial : ℝ) * M ^ m * B ^ m := by
  intro k hk
  have he := norm_iteratedFDeriv_comp_le (PhysicalGraphBounds.character_smooth c) hΦ
    (nat_le_infty k) x (C := M ^ m) (D := B)
    (fun i hi => by
      rw [PhysicalGraphBounds.norm_character_jet]
      exact (pow_le_pow_left₀ (abs_nonneg _) hc i).trans
        (pow_le_pow_right₀ hM (hi.trans hk)))
    (fun i hi hik => (hΦb i hi (hik.trans hk)).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hB hi))
  exact he.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hk) (by positivity))
    (pow_le_pow_right₀ hB hk) (by positivity) (by positivity))

variable [FiniteDimensional ℝ E]

theorem mode_jet_bound_local {a : E → ℂ} {Φ : E → ℝ} {x : E}
    (ha : LocalPhysicalCopyBounds.SmoothNear a x)
    (hΦ : LocalPhysicalCopyBounds.SmoothNear Φ x)
    (m : ℕ) {c A B M : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hM : 1 ≤ M) (hc : |c| ≤ M)
    (hab : ∀ i ≤ m, ‖iteratedFDeriv ℝ i a x‖ ≤ A)
    (hΦb : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i Φ x‖ ≤ B) :
    ∀ k ≤ m, ‖iteratedFDeriv ℝ k
      (fun y => a y * PhysicalGraphBounds.character c (Φ y)) x‖ ≤
        (2 : ℝ) ^ m * A * ((m.factorial : ℝ) * M ^ m * B ^ m) := by
  obtain ⟨a', ha', hea⟩ := ha.exists_global_germ
  obtain ⟨Φ', hΦ', heΦ⟩ := hΦ.exists_global_germ
  have hprod : (fun y => a y * PhysicalGraphBounds.character c (Φ y)) =ᶠ[𝓝 x]
      (fun y => a' y * PhysicalGraphBounds.character c (Φ' y)) := by
    filter_upwards [hea, heΦ] with y hay hφy
    rw [hay, hφy]
  have hφbound := character_comp_positive_jets hΦ' x m hB hM hc (by
    intro i hi him
    rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq heΦ i]
    exact hΦb i hi him)
  intro k hk
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hprod k]
  exact PhysicalGraphBounds.pointwise_product_jet_bound ha'
    ((PhysicalGraphBounds.character_smooth c).comp hΦ') x hk hA (by positivity)
    (by intro i hi; rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hea i]; exact hab i hi)
    hφbound

theorem smul_mode_jet_bound_local {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]
    {a : E → V} {Φ : E → ℝ} {x : E}
    (ha : LocalPhysicalCopyBounds.SmoothNear a x)
    (hΦ : LocalPhysicalCopyBounds.SmoothNear Φ x)
    (m : ℕ) {c A B M : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hM : 1 ≤ M) (hc : |c| ≤ M)
    (hab : ∀ i ≤ m, ‖iteratedFDeriv ℝ i a x‖ ≤ A)
    (hΦb : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i Φ x‖ ≤ B) :
    ∀ k ≤ m, ‖iteratedFDeriv ℝ k
      (fun y => PhysicalGraphBounds.character c (Φ y) • a y) x‖ ≤
        (2 : ℝ) ^ m * A * ((m.factorial : ℝ) * M ^ m * B ^ m) := by
  obtain ⟨a', ha', hea⟩ := ha.exists_global_germ
  obtain ⟨Φ', hΦ', heΦ⟩ := hΦ.exists_global_germ
  have hprod : (fun y => PhysicalGraphBounds.character c (Φ y) • a y) =ᶠ[𝓝 x]
      (fun y => PhysicalGraphBounds.character c (Φ' y) • a' y) := by
    filter_upwards [hea, heΦ] with y hay hφy
    rw [hay, hφy]
  have hφbound := character_comp_positive_jets hΦ' x m hB hM hc (by
    intro i hi him
    rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq heΦ i]
    exact hΦb i hi him)
  have haBound : ∀ i ≤ m, ‖iteratedFDeriv ℝ i a' x‖ ≤ A := by
    intro i hi
    rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hea i]
    exact hab i hi
  let D := (m.factorial : ℝ) * M ^ m * B ^ m
  have hD : 0 ≤ D := by dsimp [D]; positivity
  intro k hk
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hprod k]
  apply (norm_iteratedFDeriv_smul_le
    ((PhysicalGraphBounds.character_smooth c).comp hΦ') ha' x (nat_le_infty k)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * D * A := by
      apply Finset.sum_le_sum
      intro i hi
      have him : i ≤ m := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hk
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hφbound i him) (Nat.cast_nonneg _))
        (haBound (k - i) ((Nat.sub_le _ _).trans hk)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hD)
    _ = (2 : ℝ) ^ k * D * A := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ (2 : ℝ) ^ m * D * A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) hk) hD) hA
    _ = _ := by dsimp [D]; ring


end Carrier

/-! ## The current physical graph, with no copy-family premise -/

noncomputable def currentLoss (degree ρ : ℝ) (m : ℕ) : ℝ :=
  degree + ρ * m + PhysicalGraphBounds.graphLoss m + 1

private theorem mode_majorant_factorization {Q : ℝ} (hQ : 0 < Q)
    (S A B H gain degree ρ : ℝ) (p q m : ℕ) :
    Q ^ (-degree) * ((2 : ℝ) ^ m * (A * Q ^ gain * S ^ p) *
      ((m.factorial : ℝ) * (1 + H) ^ m * (B * Q ^ (-ρ) * S ^ q) ^ m)) =
      ((2 : ℝ) ^ m * A * (m.factorial : ℝ) * (1 + H) ^ m * B ^ m) *
        Q ^ (gain - degree - ρ * m) * S ^ (p + q * m) := by
  have he : Q ^ (-degree) * Q ^ gain * (Q ^ (-ρ)) ^ m =
      Q ^ (gain - degree - ρ * m) := by
    rw [← Real.rpow_mul_natCast hQ.le, ← Real.rpow_add hQ, ← Real.rpow_add hQ]
    congr 1
    ring
  calc
    _ = ((2 : ℝ) ^ m * A * (m.factorial : ℝ) * (1 + H) ^ m * B ^ m) *
        (Q ^ (-degree) * Q ^ gain * (Q ^ (-ρ)) ^ m) * (S ^ p * (S ^ q) ^ m) := by
      simp only [mul_pow]
      ring
    _ = _ := by rw [he, ← pow_mul, ← pow_add]

section NativeModes

variable {B N0 : ℕ} {V : Type} [NormedAddCommGroup V]
  [NormedSpace ℝ V] [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]

theorem native_modulated_smoothNear {α : ℝ}
    {f : Label B N0 → ℕ → Native → V}
    (hf : LabelSumBounds.UniformWaveClass nativeStrip
      ActualParticularStageControls.nativeEnvelope α f)
    (hzero : ∀ l n z, z ∈ nativeStrip.domain →
      (∃ k, z ∈ ActualParticularStageControls.controlPatch l n k) ∨
      (f l n =ᶠ[𝓝 z] fun _ => 0))
    (j : ℤ) (l : Label B N0) (n : ℕ) {z : Native} (hz : z ∈ nativeStrip.domain) :
    LocalPhysicalCopyBounds.SmoothNear (fun y =>
      PhysicalGraphBounds.character (j : ℝ) (ActualCurrentCarrierJets.weightedPhase l n y) • f l n y) z := by
  rcases hzero l n z hz with ⟨k, hk⟩ | h0
  · obtain ⟨U, hU, hzU, hPhi⟩ := ActualCurrentCarrierJets.weightedPhase_smoothNear_controlPatch l n k hk
    have hc : ContDiffOn ℝ ∞ (fun y => PhysicalGraphBounds.character (j : ℝ)
        (ActualCurrentCarrierJets.weightedPhase l n y)) (nativeStrip.domain ∩ U) :=
      (PhysicalGraphBounds.character_smooth (j : ℝ)).comp_contDiffOn
        (hPhi.mono inter_subset_right)
    exact ⟨nativeStrip.domain ∩ U, nativeStrip.isOpen_domain.inter hU, ⟨hz, hzU⟩,
      (hc.continuousLinearMap_comp (ContinuousLinearMap.lsmul ℝ ℂ :
        ℂ →L[ℝ] V →L[ℝ] V)).clm_apply ((hf.smooth l n).mono inter_subset_left)⟩
  · have hg : (fun y => PhysicalGraphBounds.character (j : ℝ)
        (ActualCurrentCarrierJets.weightedPhase l n y) • f l n y) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [h0] with y hy
      rw [hy, smul_zero]
    obtain ⟨U, he, hU, hzU⟩ := mem_nhds_iff.mp hg
    exact ⟨U, hU, hzU, contDiffOn_const.congr (fun y hy => he hy)⟩

/-- Uniform full native jets of the literal current oscillation.  The
actual periodic phase is used only where the native control cell applies;
outside those cells the cut coefficient has a zero germ. -/
theorem native_modulated_bound {α : ℝ}
    {f : Label B N0 → ℕ → Native → V}
    (hf : LabelSumBounds.UniformWaveClass nativeStrip
      ActualParticularStageControls.nativeEnvelope α f)
    (hzero : ∀ l n z, z ∈ nativeStrip.domain →
      (∃ k, z ∈ ActualParticularStageControls.controlPatch l n k) ∨
      (f l n =ᶠ[𝓝 z] fun _ => 0)) (j : ℤ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ l n, 4 ≤ n → ∀ z ∈ nativeStrip.domain, ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i (fun y => PhysicalGraphBounds.character (j : ℝ)
        (ActualCurrentCarrierJets.weightedPhase l n y) • f l n y) z‖ ≤
      C * ChartScales.Q n ^ (CorrectionInitialization.ActualPrimary.h * α -
        2 * CorrectionInitialization.ActualPrimary.h * m) * ChartScales.S n ^ p := by
  let h := CorrectionInitialization.ActualPrimary.h
  obtain ⟨A, hA, p, ha⟩ := (native_source_bounds hf).chart_bound m
  obtain ⟨D, hD, r, hd⟩ := ActualCurrentCarrierJets.weightedPhase_positive_jets_controlPatch
    (B := B) (N0 := N0) m
  let C := (2 : ℝ) ^ m * A * (m.factorial : ℝ) * (1 + |(j : ℝ)|) ^ m * D ^ m
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, p + r * m, ?_⟩
  intro l n hn z hz i him
  rcases hzero l n z hz with ⟨k, hk⟩ | h0
  · have hQ := ChartScales.Q_pos n
    have hS : 1 ≤ ChartScales.S n := PhysicalGraphBounds.S_ge_one (by omega)
    have hρ : 0 ≤ 2 * h := mul_nonneg (by norm_num) CorrectionInitialization.ActualPrimary.outgoing.data.h_pos.le
    have hQR : 1 ≤ ChartScales.Q n ^ (-(2 * h)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hQ (ChartScales.Q_le_one n) (neg_nonpos.mpr hρ)
    have hD' : 1 ≤ D * ChartScales.Q n ^ (-(2 * h)) * ChartScales.S n ^ r :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hD hQR) (one_le_pow₀ hS)
    have hh := smul_mode_jet_bound_local
      (show LocalPhysicalCopyBounds.SmoothNear (f l n) z from
        ⟨nativeStrip.domain, nativeStrip.isOpen_domain, hz, hf.smooth l n⟩)
      (ActualCurrentCarrierJets.weightedPhase_smoothNear_controlPatch l n k hk) m
      (by positivity : 0 ≤ A * ChartScales.Q n ^ (h * α) * ChartScales.S n ^ p)
      hD' (le_add_of_nonneg_right (abs_nonneg (j : ℝ)))
      (by linarith : |(j : ℝ)| ≤ 1 + |(j : ℝ)|)
      (ha l n hn z hz) (fun a h1 h2 => by
        simpa only [mul_right_comm] using hd l n k z hk a h1 h2) i him
    apply hh.trans_eq
    simpa only [neg_zero, Real.rpow_zero, one_mul, sub_zero, h, C, mul_assoc] using
      mode_majorant_factorization hQ (ChartScales.S n) A D |(j : ℝ)| (h * α) 0 (2 * h) p r m
  · have hg : (fun y => PhysicalGraphBounds.character (j : ℝ)
        (ActualCurrentCarrierJets.weightedPhase l n y) • f l n y) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [h0] with y hy
      rw [hy, smul_zero]
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hg i]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    have hS : 1 ≤ ChartScales.S n := PhysicalGraphBounds.S_ge_one (by omega)
    exact mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _).le)
      (pow_nonneg (zero_le_one.trans hS) _)

end NativeModes

section ActualModes

open CorrectionStep

variable {B N0 : ℕ}

theorem actual_nativePotential_eq_character (x : CycleState (Label B N0))
    (hx : ActualParticularStageControls.PreservesCarriers x)
    (l : Label B N0) (j : ℤ) (n : ℕ) :
    ActualCurrentParticularPhysical.nativePotential x l j n = fun y =>
      PhysicalGraphBounds.character (j : ℝ) (ActualCurrentCarrierJets.weightedPhase l n y) •
        potentialCoefficient x l j n y := by
  have hf := ActualParticularStageControls.preserves_frequency hx l
  have hcar := ActualCurrentCarrierJets.actualCarrier_character
    (fun l => x.coefficients.blocks l) hx j l n
  unfold ActualCurrentParticularPhysical.nativePotential
  rw [ActualCurrentParticularPhysical.copyData_eq_actual x l j hf]
  ext y i
  change (potentialCoefficient x l j n y i) *
    (HarmonicCalculus.carrier ((ActualParticularBackground.carrier
      (fun l => x.coefficients.blocks l) j l).frequency n)
      ((ActualParticularBackground.carrier (fun l => x.coefficients.blocks l) j l).phase n) y) = _
  rw [hcar]
  exact mul_comm _ _

theorem actual_nativePressure_eq_character (x : CycleState (Label B N0))
    (hx : ActualParticularStageControls.PreservesCarriers x)
    (l : Label B N0) (j : ℤ) (n : ℕ) :
    ActualCurrentParticularPhysical.nativePressure x l j n = fun y =>
      PhysicalGraphBounds.character (j : ℝ) (ActualCurrentCarrierJets.weightedPhase l n y) •
        (ActualParticularStageControls.data x l j).common.pressure n y := by
  have hf := ActualParticularStageControls.preserves_frequency hx l
  have hcar := ActualCurrentCarrierJets.actualCarrier_character
    (fun l => x.coefficients.blocks l) hx j l n
  unfold ActualCurrentParticularPhysical.nativePressure
  rw [ActualCurrentParticularPhysical.copyData_eq_actual x l j hf]
  ext y
  change (ActualParticularStageControls.data x l j).common.pressure n y *
    (HarmonicCalculus.carrier ((ActualParticularBackground.carrier
      (fun l => x.coefficients.blocks l) j l).frequency n)
      ((ActualParticularBackground.carrier (fun l => x.coefficients.blocks l) j l).phase n) y) = _
  rw [hcar]
  exact mul_comm _ _

theorem actual_native_potential_bound (x : CycleState (Label B N0))
    (hx : ActualParticularStageControls.PreservesCarriers x)
    (hs : ActualParticularStageControls.InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass nativeStrip ActualParticularStageControls.nativeEnvelope
      α (ActualParticularStageControls.currentSource x j)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ l n, 4 ≤ n → ∀ z ∈ nativeStrip.domain, ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i (ActualCurrentParticularPhysical.nativePotential x l j n) z‖ ≤
      C * ChartScales.Q n ^ (CorrectionInitialization.ActualPrimary.h * (α + 1 / 2) -
        2 * CorrectionInitialization.ActualPrimary.h * m) * ChartScales.S n ^ p := by
  have hb := native_modulated_bound (actual_potential_coefficient_class x hx hs hN j hj H)
    (fun l n z hz => (common_control_or_zero x hs hN l j n hz).imp_right And.left) j m
  simpa only [← actual_nativePotential_eq_character x hx] using hb

theorem actual_native_pressure_bound (x : CycleState (Label B N0))
    (hx : ActualParticularStageControls.PreservesCarriers x)
    (hs : ActualParticularStageControls.InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass nativeStrip ActualParticularStageControls.nativeEnvelope
      α (ActualParticularStageControls.currentSource x j)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ l n, 4 ≤ n → ∀ z ∈ nativeStrip.domain, ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i (ActualCurrentParticularPhysical.nativePressure x l j n) z‖ ≤
      C * ChartScales.Q n ^ (CorrectionInitialization.ActualPrimary.h * (α + 1 / 2) -
        2 * CorrectionInitialization.ActualPrimary.h * m) * ChartScales.S n ^ p := by
  have hb := native_modulated_bound (actual_pressure_coefficient_class x hx hs hN j hj H)
    (fun l n z hz => (common_control_or_zero x hs hN l j n hz).imp_right And.right) j m
  simpa only [← actual_nativePressure_eq_character x hx] using hb


theorem actual_native_pressure_smoothNear (x : CycleState (Label B N0))
    (hx : ActualParticularStageControls.PreservesCarriers x)
    (hs : ActualParticularStageControls.InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass nativeStrip ActualParticularStageControls.nativeEnvelope
      α (ActualParticularStageControls.currentSource x j))
    (l : Label B N0) (n : ℕ) {z : Native} (hz : z ∈ nativeStrip.domain) :
    LocalPhysicalCopyBounds.SmoothNear (ActualCurrentParticularPhysical.nativePressure x l j n) z := by
  rw [actual_nativePressure_eq_character x hx]
  exact native_modulated_smoothNear (actual_pressure_coefficient_class x hx hs hN j hj H)
    (fun l n z hz => (common_control_or_zero x hs hN l j n hz).imp_right And.right) j l n hz

theorem actual_native_pressure_re_bound (x : CycleState (Label B N0))
    (hx : ActualParticularStageControls.PreservesCarriers x)
    (hs : ActualParticularStageControls.InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass nativeStrip ActualParticularStageControls.nativeEnvelope
      α (ActualParticularStageControls.currentSource x j)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ l n, 4 ≤ n → ∀ z ∈ nativeStrip.domain, ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i (fun y => (ActualCurrentParticularPhysical.nativePressure x l j n y).re) z‖ ≤
      C * ChartScales.Q n ^ (CorrectionInitialization.ActualPrimary.h * (α + 1 / 2) -
        2 * CorrectionInitialization.ActualPrimary.h * m) * ChartScales.S n ^ p := by
  obtain ⟨C, hC, p, hb⟩ := actual_native_pressure_bound x hx hs hN j hj H m
  refine ⟨C, hC, p, ?_⟩
  intro l n hn z hz i him
  have hc := (actual_native_pressure_smoothNear x hx hs hN j hj H l n hz).contDiffAt
  rw [show (fun y => (ActualCurrentParticularPhysical.nativePressure x l j n y).re) =
    Complex.reCLM ∘ ActualCurrentParticularPhysical.nativePressure x l j n from rfl,
    Complex.reCLM.iteratedFDeriv_comp_left (hc.of_le (nat_le_infty i)) le_rfl]
  have hr : ‖Complex.reCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa only [Complex.reCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_re_le_norm z
  exact (Complex.reCLM.norm_compContinuousMultilinearMap_le _).trans
    ((mul_le_mul_of_nonneg_right hr (norm_nonneg _)).trans
      (by simpa only [one_mul] using hb l n hn z hz i him))

/-- The closed moving annulus is the closure of the genuine open native
strip within each positive-time slow fiber. -/
theorem native_closed_mem_closure {z : Native}
    (hz : z ∈ ActualCurrentParticularPhysical.nativeDomain)
    (hr : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z) ∈
      Icc (PrimaryTargetBounds.leftRadius CorrectionInitialization.ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius CorrectionInitialization.ActualPrimary.nominal)) :
    z ∈ closure nativeStrip.domain := by
  let U := CorrectionInitialization.ActualPrimary.standardRegion
  let ell := VariableGaugeMean.qLength (2 * CorrectionInitialization.ActualPrimary.h) z.1.1.2
  have hslow : z.1.1.2 ∈ U.carrier := hz.1
  have hell : 0 < ell := VariableGaugeMean.qLength_pos U.coord_pos U.coord_lt_one (U.time_pos _ hslow)
  let g : ℝ → Native := fun r => (((ell * r, z.1.1.2), z.1.2), z.2)
  have hg : Continuous g := by
    exact (((continuous_const.mul continuous_id).prodMk continuous_const).prodMk
      continuous_const).prodMk continuous_const
  have he : g (ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z)) = z := by
    change (((ell * (z.1.1.1 / ell), z.1.1.2), z.1.2), z.2) = z
    rw [show ell * (z.1.1.1 / ell) = z.1.1.1 by field_simp]
  have hmap : MapsTo g
      (Ioo (PrimaryTargetBounds.leftRadius CorrectionInitialization.ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius CorrectionInitialization.ActualPrimary.nominal)) nativeStrip.domain := by
    intro r hrr
    apply ActualCurrentParticularPhysical.nativeStrip_mem (show g r ∈
      ActualCurrentParticularPhysical.nativeDomain from hz)
    change ell * r / ell ∈ Ioo _ _
    rwa [mul_div_cancel_left₀ _ hell.ne']
  have hcl : g (ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z)) ∈
      closure (g '' Ioo (PrimaryTargetBounds.leftRadius CorrectionInitialization.ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius CorrectionInitialization.ActualPrimary.nominal)) := by
    apply mem_closure_image hg.continuousAt
    rw [closure_Ioo (PrimaryTargetBounds.radii_ordered CorrectionInitialization.ActualPrimary.nominal).ne]
    exact hr
  rw [he] at hcl
  exact closure_mono hmap.image_subset hcl

theorem native_bound_on_closed {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Native → E} (hf : ContDiffOn ℝ ∞ f ActualCurrentParticularPhysical.nativeDomain)
    {C : ℝ} (m : ℕ) (hb : ∀ z ∈ nativeStrip.domain, ‖iteratedFDeriv ℝ m f z‖ ≤ C)
    {z : Native} (hz : z ∈ ActualCurrentParticularPhysical.nativeDomain)
    (hr : ActualWaveRegularityData.radius (ActualWaveRegularity.particularChart.symm z) ∈
      Icc (PrimaryTargetBounds.leftRadius CorrectionInitialization.ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius CorrectionInitialization.ActualPrimary.nominal)) :
    ‖iteratedFDeriv ℝ m f z‖ ≤ C :=
  LocalPhysicalCopyBounds.jet_bound_at_closure
    (hf.contDiffAt (ActualCurrentParticularPhysical.nativeDomain_open.mem_nhds hz))
    (native_closed_mem_closure hz hr) m hb

end ActualModes

section PhysicalComposition

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A frozen physical power is included before applying the proved jets
of the actual common graph. -/
theorem scaled_common_bound {h a b : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (Δ m : ℕ) (gain degree A : ℝ) (p : ℕ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b →
      |w.1| ≤ 1 → ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ F : PhysicalWaveSum.LiftPoint → E,
      LocalPhysicalCopyBounds.SmoothNear F (PhysicalWaveSum.commonLift h n d w) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i F (PhysicalWaveSum.commonLift h n d w)‖ ≤
        A * ChartScales.Q n ^ gain * ChartScales.S n ^ p) →
      ‖iteratedFDeriv ℝ m (fun y => ChartScales.Q n ^ (-degree) •
        F (PhysicalWaveSum.commonLift h n d y)) w‖ ≤
      C * q ^ (gain - degree - (PhysicalGraphBounds.graphLoss m + 1)) := by
  obtain ⟨C, hC, hb⟩ := PhysicalMeanJetBounds.common_stripped_physical_bound_local (E := E)
    (b := b) hh hh1 ha Δ m (gain - degree) p A hA
  refine ⟨C, hC, ?_⟩
  intro n hn d hd w hann ht q hq hlo hhi F hF hFb
  let G : PhysicalWaveSum.LiftPoint → E := fun y => ChartScales.Q n ^ (-degree) • F y
  have hG : LocalPhysicalCopyBounds.SmoothNear G (PhysicalWaveSum.commonLift h n d w) := by
    obtain ⟨U, hU, hxU, hs⟩ := hF
    exact ⟨U, hU, hxU, hs.const_smul _⟩
  apply hb n hn d hd w hann ht q hq hlo hhi G hG
  intro i hi
  change ‖iteratedFDeriv ℝ i (fun y => ChartScales.Q n ^ (-degree) • F y) _‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hF.contDiffAt.of_le (nat_le_infty i)),
    norm_smul (ChartScales.Q n ^ (-degree) : ℝ)
      (iteratedFDeriv ℝ i F (PhysicalWaveSum.commonLift h n d w)),
    Real.norm_of_nonneg (Real.rpow_pos_of_pos (ChartScales.Q_pos n) (-degree)).le,
    Real.rpow_natCast]
  apply (mul_le_mul_of_nonneg_left (hFb i hi)
    (Real.rpow_pos_of_pos (ChartScales.Q_pos n) (-degree)).le).trans_eq
  have he : ChartScales.Q n ^ (-degree) * ChartScales.Q n ^ gain =
      ChartScales.Q n ^ (gain - degree) := by
    rw [← Real.rpow_add (ChartScales.Q_pos n)]
    congr 1
    ring
  calc
    _ = A * (ChartScales.Q n ^ (-degree) * ChartScales.Q n ^ gain) * ChartScales.S n ^ p := by ring
    _ = _ := by rw [he]

theorem scalar_chart_physical_bound {h a b : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (Δ m : ℕ) (gain degree A : ℝ) (p : ℕ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b →
      |w.1| ≤ 1 → ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ chart : PolarCharts.Index, ∀ f : Native → E,
      LocalPhysicalCopyBounds.SmoothNear f (CurrentPhysicalChartJets.chartMap a chart
        (PhysicalWaveSum.commonLift h n d w)) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (CurrentPhysicalChartJets.chartMap a chart
        (PhysicalWaveSum.commonLift h n d w))‖ ≤ A * ChartScales.Q n ^ gain * ChartScales.S n ^ p) →
      ‖iteratedFDeriv ℝ m (fun y => ChartScales.Q n ^ (-degree) •
        f (CurrentPhysicalChartJets.chartMap a chart (PhysicalWaveSum.commonLift h n d y))) w‖ ≤
      C * q ^ (gain - degree - (PhysicalGraphBounds.graphLoss m + 1)) := by
  obtain ⟨M, hM, hm⟩ := CurrentPhysicalChartJets.composition_jets (E := E) (b := b) ha m
  obtain ⟨C, hC, hc⟩ := scaled_common_bound (E := E) (b := b) hh hh1 ha Δ m gain degree (M * A) p
    (mul_nonneg (zero_le_one.trans hM) hA)
  refine ⟨C, hC, ?_⟩
  intro n hn d hd w hann ht q hq hlo hhi chart f hf hfb
  apply hc n hn d hd w hann ht q hq hlo hhi (f ∘ CurrentPhysicalChartJets.chartMap a chart)
    (CurrentPhysicalChartJets.composition_smoothNear ha hf)
  intro i hi
  have hS : 1 ≤ ChartScales.S n := PhysicalGraphBounds.S_ge_one (by omega)
  have ha' : 0 ≤ A * ChartScales.Q n ^ gain * ChartScales.S n ^ p :=
    mul_nonneg (mul_nonneg hA (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _).le)
      (pow_nonneg (zero_le_one.trans hS) _)
  simpa only [mul_assoc] using hm chart _
    (PhysicalClassBounds.commonLift_mem_cylindricalDomain ha h n d w hann) f hf _ ha' hfb i hi

end PhysicalComposition

theorem vector_chart_physical_bound {h a b : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (Δ m : ℕ) (gain degree A : ℝ) (p : ℕ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b →
      |w.1| ≤ 1 → ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ chart : PolarCharts.Index, ∀ f : Native → ComplexVector,
      LocalPhysicalCopyBounds.SmoothNear f (CurrentPhysicalChartJets.chartMap a chart
        (PhysicalWaveSum.commonLift h n d w)) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (CurrentPhysicalChartJets.chartMap a chart
        (PhysicalWaveSum.commonLift h n d w))‖ ≤ A * ChartScales.Q n ^ gain * ChartScales.S n ^ p) →
      ‖iteratedFDeriv ℝ m (fun y => ChartScales.Q n ^ (-degree) •
        PhysicalCurlCovariance.realVector (CurrentPhysicalChartJets.rotated a chart f
          (PhysicalWaveSum.commonLift h n d y))) w‖ ≤
      C * q ^ (gain - degree - (PhysicalGraphBounds.graphLoss m + 1)) := by
  obtain ⟨M, hM, hm⟩ := CurrentPhysicalChartJets.rotated_composition_jets (b := b) ha m
  obtain ⟨C, hC, hc⟩ := scaled_common_bound (E := Space) (b := b) hh hh1 ha Δ m gain degree
    (3 * M * A) p (by positivity)
  refine ⟨C, hC, ?_⟩
  intro n hn d hd w hann ht q hq hlo hhi chart f hf hfb
  have hdoma := PhysicalClassBounds.commonLift_mem_cylindricalDomain ha h n d w hann
  have hrot := CurrentPhysicalChartJets.rotated_smoothNear ha hdoma hf
  let G : PhysicalWaveSum.LiftPoint → Space :=
    CurrentPhysicalChartJets.realVectorCLM ∘ CurrentPhysicalChartJets.rotated a chart f
  have hG : LocalPhysicalCopyBounds.SmoothNear G (PhysicalWaveSum.commonLift h n d w) := by
    obtain ⟨U, hU, hxU, hs⟩ := hrot
    exact ⟨U, hU, hxU, hs.continuousLinearMap_comp CurrentPhysicalChartJets.realVectorCLM⟩
  apply hc n hn d hd w hann ht q hq hlo hhi G hG
  intro i hi
  have hS : 1 ≤ ChartScales.S n := PhysicalGraphBounds.S_ge_one (by omega)
  have ha' : 0 ≤ A * ChartScales.Q n ^ gain * ChartScales.S n ^ p :=
    mul_nonneg (mul_nonneg hA (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _).le)
      (pow_nonneg (zero_le_one.trans hS) _)
  change ‖iteratedFDeriv ℝ i (CurrentPhysicalChartJets.realVectorCLM ∘ _) _‖ ≤ _
  rw [CurrentPhysicalChartJets.realVectorCLM.iteratedFDeriv_comp_left
    (hrot.contDiffAt.of_le (nat_le_infty i)) le_rfl]
  apply (CurrentPhysicalChartJets.realVectorCLM.norm_compContinuousMultilinearMap_le _).trans
  have hb := mul_le_mul CurrentPhysicalChartJets.norm_realVectorCLM_le
    (hm chart _ hdoma f hf _ ha' hfb i hi) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
  simpa only [mul_assoc] using hb


section ActualPhysicalRates

open CorrectionStep CorrectionInitialization CorrectionInitialization.ActualPrimary

variable {B N0 : ℕ} {σ : ℝ}
  {x : CycleState (ActualInitialization.Index B N0)}

private theorem commonGap_bound (n : ℕ) :
    CurrentPhysicalModeGerms.commonGap n ≤ CommonWindow.gap h := by
  have hn := CommonWindow.native_le_index_add h outgoing.data.h_pos.le n
  unfold CurrentPhysicalModeGerms.commonGap
  omega

/-- All physical jets of the actual current particular potential mode.
The constant is chosen before the label, current band, and physical point.
Only the literal incoming analytic invariant is required. -/
theorem current_potential_mode_bound (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (j : ℤ) (hj : j ≠ 0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (l : Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotentialMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤
      C * PhysicalWaveSum.physicalQ h w ^
        (h * ((1 / 2 + σ) + 1 / 2) - currentLoss h (2 * h) m) := by
  let y := ActualCycleParameters.particularState x
  have hcar := ActualParticularCycleData.preservesCarriers H
  have hin := ActualParticularCycleData.native_inputSupport H
  have hsrc := ActualParticularCycleData.native_source_class H j hj
  obtain ⟨A, hA, p, hab⟩ := actual_native_potential_bound y hcar hin hN j hj hsrc m
  obtain ⟨C, hC, hb⟩ := vector_chart_physical_bound (b := CurrentModeGeometry.chartOuter)
    outgoing.data.h_pos.le outgoing.data.h_lt_half.le CurrentModeGeometry.chartInner_pos
    (CommonWindow.gap h) m (h * ((1 / 2 + σ) + 1 / 2) - 2 * h * m) h A p hA
  refine ⟨C, hC, ?_⟩
  intro l n hn w hw hq
  have hqpos := PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1
  by_cases hr : ActualCurrentWaveSupport.profileRadius h w ∈
      Icc (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)
  · have hann := CurrentModeGeometry.scaledRadial_mem_annulus n hw hr
    let chart := PhysicalWaveSum.chooseChart CurrentModeGeometry.chartInner
      (PhysicalGraphBounds.scaledRadial n w)
    have hchart : PhysicalGraphBounds.scaledRadial n w ∈
        PolarCharts.chartDomain CurrentModeGeometry.chartInner chart :=
      PhysicalWaveSum.chooseChart_valid CurrentModeGeometry.chartInner_pos hann
    have hz := CurrentModeGeometry.point_mem_nativeDomain n CurrentModeGeometry.chartInner_pos chart hw hchart
    have hzrad := CurrentModeGeometry.point_profileRadius n CurrentModeGeometry.chartInner_pos chart hw.1 hchart
    have hs : ContDiffOn ℝ ∞ (ActualCurrentParticularPhysical.nativePotential y l j n)
        ActualCurrentParticularPhysical.nativeDomain :=
      (ActualCurrentParticularPhysical.native_smooth_of_invariant H hN (l.2,l.1) j hj n).1
    have hnear : LocalPhysicalCopyBounds.SmoothNear
        (ActualCurrentParticularPhysical.nativePotential y l j n)
        (CurrentModeGeometry.point CurrentModeGeometry.chartInner chart n w) :=
      ⟨_, ActualCurrentParticularPhysical.nativeDomain_open, hz, hs⟩
    have hjets : ∀ i ≤ m, ‖iteratedFDeriv ℝ i
        (ActualCurrentParticularPhysical.nativePotential y l j n)
        (CurrentModeGeometry.point CurrentModeGeometry.chartInner chart n w)‖ ≤
        A * ChartScales.Q n ^ (h * ((1 / 2 + σ) + 1 / 2) - 2 * h * m) * ChartScales.S n ^ p := by
      intro i hi
      apply native_bound_on_closed hs i (fun z hz => hab l n hn z hz i hi) hz
      rwa [hzrad]
    have hlo : PhysicalWaveSum.physicalQ h w / 2 ≤ ChartScales.Q n := by linarith [hw.2.2]
    have hhi : ChartScales.Q n ≤ 2 * PhysicalWaveSum.physicalQ h w := by linarith [hw.2.1]
    have he := hb n hn (CurrentPhysicalModeGerms.commonGap n) (commonGap_bound n) w hann
      (PhysicalStageBounds.abs_time_le_one outgoing.data.h_pos outgoing.data.h_lt_half hw.1 hq)
      _ hqpos hlo hhi chart (ActualCurrentParticularPhysical.nativePotential y l j n) hnear hjets
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq
      (CurrentPhysicalModeGerms.localPotentialMode_germ y l j
        (ActualParticularStageControls.preserves_frequency hcar l) n
        CurrentModeGeometry.chartInner_pos chart hchart) m]
    convert! he using 1
    congr 2
    unfold currentLoss
    ring
  · have hsupport := (ActualCurrentWaveSupport.current_mode_annulus hN y l
      (H.inputSupport (l.2,l.1)) j 0).1
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq
      (hsupport.zero_germ outgoing.data.h_pos outgoing.data.h_lt_half (Nat.zero_le n) hw hr) m]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg hC (Real.rpow_pos_of_pos hqpos _).le

/-- The matching full physical-jet estimate for the literal current
particular pressure mode, with its actual quadratic physical scale. -/
theorem current_pressure_mode_bound (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (j : ℤ) (hj : j ≠ 0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (l : Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressureMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤
      C * PhysicalWaveSum.physicalQ h w ^
        (h * ((1 / 2 + σ) + 1 / 2) - currentLoss (2 * CoordinateAlgebra.A h) (2 * h) m) := by
  let y := ActualCycleParameters.particularState x
  have hcar := ActualParticularCycleData.preservesCarriers H
  have hin := ActualParticularCycleData.native_inputSupport H
  have hsrc := ActualParticularCycleData.native_source_class H j hj
  obtain ⟨A, hA, p, hab⟩ := actual_native_pressure_re_bound y hcar hin hN j hj hsrc m
  obtain ⟨C, hC, hb⟩ := scalar_chart_physical_bound (E := ℝ) (b := CurrentModeGeometry.chartOuter)
    outgoing.data.h_pos.le outgoing.data.h_lt_half.le CurrentModeGeometry.chartInner_pos
    (CommonWindow.gap h) m (h * ((1 / 2 + σ) + 1 / 2) - 2 * h * m)
    (2 * CoordinateAlgebra.A h) A p hA
  refine ⟨C, hC, ?_⟩
  intro l n hn w hw hq
  have hqpos := PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1
  by_cases hr : ActualCurrentWaveSupport.profileRadius h w ∈
      Icc (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)
  · have hann := CurrentModeGeometry.scaledRadial_mem_annulus n hw hr
    let chart := PhysicalWaveSum.chooseChart CurrentModeGeometry.chartInner
      (PhysicalGraphBounds.scaledRadial n w)
    have hchart : PhysicalGraphBounds.scaledRadial n w ∈
        PolarCharts.chartDomain CurrentModeGeometry.chartInner chart :=
      PhysicalWaveSum.chooseChart_valid CurrentModeGeometry.chartInner_pos hann
    have hz := CurrentModeGeometry.point_mem_nativeDomain n CurrentModeGeometry.chartInner_pos chart hw hchart
    have hzrad := CurrentModeGeometry.point_profileRadius n CurrentModeGeometry.chartInner_pos chart hw.1 hchart
    have hs : ContDiffOn ℝ ∞ (fun z => (ActualCurrentParticularPhysical.nativePressure y l j n z).re)
        ActualCurrentParticularPhysical.nativeDomain :=
      (ActualCurrentParticularPhysical.native_smooth_of_invariant H hN (l.2,l.1) j hj n).2
    have hnear : LocalPhysicalCopyBounds.SmoothNear
        (fun z => (ActualCurrentParticularPhysical.nativePressure y l j n z).re)
        (CurrentModeGeometry.point CurrentModeGeometry.chartInner chart n w) :=
      ⟨_, ActualCurrentParticularPhysical.nativeDomain_open, hz, hs⟩
    have hjets : ∀ i ≤ m, ‖iteratedFDeriv ℝ i
        (fun z => (ActualCurrentParticularPhysical.nativePressure y l j n z).re)
        (CurrentModeGeometry.point CurrentModeGeometry.chartInner chart n w)‖ ≤
        A * ChartScales.Q n ^ (h * ((1 / 2 + σ) + 1 / 2) - 2 * h * m) * ChartScales.S n ^ p := by
      intro i hi
      apply native_bound_on_closed hs i (fun z hz => hab l n hn z hz i hi) hz
      rwa [hzrad]
    have hlo : PhysicalWaveSum.physicalQ h w / 2 ≤ ChartScales.Q n := by linarith [hw.2.2]
    have hhi : ChartScales.Q n ≤ 2 * PhysicalWaveSum.physicalQ h w := by linarith [hw.2.1]
    have he := hb n hn (CurrentPhysicalModeGerms.commonGap n) (commonGap_bound n) w hann
      (PhysicalStageBounds.abs_time_le_one outgoing.data.h_pos outgoing.data.h_lt_half hw.1 hq)
      _ hqpos hlo hhi chart (fun z => (ActualCurrentParticularPhysical.nativePressure y l j n z).re) hnear hjets
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq
      (CurrentPhysicalModeGerms.localPressureMode_germ y l j
        (ActualParticularStageControls.preserves_frequency hcar l) n
        CurrentModeGeometry.chartInner_pos chart hchart) m]
    simp only [neg_mul] at he ⊢
    convert! he using 1
    congr 2
    unfold currentLoss
    ring
  · have hsupport := (ActualCurrentWaveSupport.current_mode_annulus hN y l
      (H.inputSupport (l.2,l.1)) j 0).2
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq
      (hsupport.zero_germ outgoing.data.h_pos outgoing.data.h_lt_half (Nat.zero_le n) hw hr) m]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg hC (Real.rpow_pos_of_pos hqpos _).le

end ActualPhysicalRates

end NavierStokes.ActualCurrentParticularBounds

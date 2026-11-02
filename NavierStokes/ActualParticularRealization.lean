import NavierStokes.CorrectionStep
import NavierStokes.CyclePhysicalPrefixes

/-!
# Cartesian realization of the actual reference particular update

The source is the current state's literal harmonic residual.  The common
solve, its transported cutoff, its curl correction, and its finite harmonic
assembly are retained in the realization.
-/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.ActualParticularRealization

open HarmonicCalculus ParticularWaveAssembly ParticularWaveBounds
open CurlClassBounds hiding ComplexVector
open CorrectionState

abbrev Parameter := PhysicalParticularWave.Parameter
abbrev Plane := TorusInverse.Plane
abbrev Associated := Parameter × Plane
abbrev WaveSpace := PhysicalParticularWave.WaveSpace
abbrev Cylinder := PhysicalParticularWave.Cylinder

section Reindex

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An invertible linear coordinate change transports the actual Fréchet
derivative, including its totalized value away from differentiability. -/
theorem normal_pull (e : E ≃ₗᵢ[ℝ] F) (R Φ : F → ℝ) (Vr Vθ Vz : F → F) :
    phaseNormal (fun x => R (e x)) (StateReindex.vector e Vr) (StateReindex.vector e Vθ)
      (StateReindex.vector e Vz) (fun x => Φ (e x)) = fun x => phaseNormal R Vr Vθ Vz Φ (e x) := by
  funext x
  simp only [phaseNormal, StateReindex.along_pull]

theorem curl_pull (e : E ≃ₗᵢ[ℝ] F) (R : F → ℝ) (Vr Vθ Vz : F → F)
    (a : F → ComplexVector) :
    cylindricalCurl (fun x => R (e x)) (StateReindex.vector e Vr) (StateReindex.vector e Vθ)
      (StateReindex.vector e Vz) (fun x => a (e x)) = fun x => cylindricalCurl R Vr Vθ Vz a (e x) := by
  funext x
  simp only [cylindricalCurl, StateReindex.along_pull_component]

theorem realizedCoefficient_pull (e : E ≃ₗᵢ[ℝ] F) (K : ℝ) (R Φ : F → ℝ)
    (Vr Vθ Vz : F → F) (a : F → ComplexVector) :
    realizedCoefficient K (fun x => R (e x)) (StateReindex.vector e Vr) (StateReindex.vector e Vθ)
      (StateReindex.vector e Vz) (fun x => Φ (e x)) (fun x => a (e x)) =
        fun x => realizedCoefficient K R Vr Vθ Vz Φ a (e x) := by
  have hc : coefficient (fun x => R (e x)) (StateReindex.vector e Vr) (StateReindex.vector e Vθ)
      (StateReindex.vector e Vz) (fun x => Φ (e x)) (fun x => a (e x)) =
        fun x => coefficient R Vr Vθ Vz Φ a (e x) := by
    funext x
    simp only [coefficient, normal_pull]
  funext x
  simp only [realizedCoefficient, hc, curlRemainder_eq, curl_pull]

/-- Phase agreement on a neighborhood suffices for the complete curl
correction; no global continuation of the phase identity is required. -/
theorem realizedCoefficient_phase_germ {Φ Ψ : E → ℝ} {x : E} (hΦ : Φ =ᶠ[𝓝 x] Ψ)
    (K : ℝ) (R : E → ℝ) (Vr Vθ Vz : E → E) (a : E → ComplexVector) :
    realizedCoefficient K R Vr Vθ Vz Φ a =ᶠ[𝓝 x] realizedCoefficient K R Vr Vθ Vz Ψ a := by
  have hc : coefficient R Vr Vθ Vz Φ a =ᶠ[𝓝 x] coefficient R Vr Vθ Vz Ψ a := by
    filter_upwards [hΦ.fderiv (𝕜 := ℝ)] with y hy
    simp only [coefficient, phaseNormal, along, hy]
  filter_upwards [ParticularWaveAssembly.curl_germ hc R Vr Vθ Vz] with y hy
  simp only [realizedCoefficient, curlRemainder_eq, hy]

end Reindex

noncomputable def raw (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ) (j : ℤ) :
    LinearWaveBounds.WaveCoefficients WaveSpace :=
  ((CorrectionStep.ParticularParameters.fromReference D h gap).copyData
    D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j).common

noncomputable def corrected (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
    (h : ℝ) (gap : ℕ → ℕ) (j : ℤ) : LinearWaveBounds.WaveCoefficients WaveSpace :=
  (CorrectionStep.ParticularParameters.fromReference D h gap).wave s
    D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j

/-- Only the primitive radius and differential directions are matched.
No solved coefficient or output field occurs in this record. -/
structure TargetChart (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
    (h : ℝ) (n i : ℕ) : Prop where
  radius : (fun x => D.background.radius n (PhysicalParticularWave.waveEquiv x)) =
    PhysicalResidualBridge.ScaledGraph.radius
  radial : StateReindex.vector PhysicalParticularWave.waveEquiv (D.directions.radialField n) =
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).radial
  angular : StateReindex.vector PhysicalParticularWave.waveEquiv (fun _ => D.directions.angular) =
    PhysicalResidualBridge.ScaledGraph.angular
  axial : StateReindex.vector PhysicalParticularWave.waveEquiv
    (D.directions.axialField (CorrectionStep.ParticularParameters.nativeStrip s) n) =
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).axial

section Band

variable (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
  (h : ℝ) (gap : ℕ → ℕ) (n i : ℕ)
  (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
    (ChartScales.Q_pos D.reference.band) i (gap n) n)
  (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
  (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput D.reference.band)

include H hn hr in
theorem raw_amplitude_pull (j : ℤ) :
    (fun x => (raw D h gap j).amplitude n (PhysicalParticularWave.waveEquiv x)) =
      PhysicalParticularWave.bandRaw D h (ChartScales.Q_pos n) (ChartScales.Q_pos D.reference.band)
        (gap n) ((j : ℝ) * D.carrierBlock.frequency n) j := by
  funext x
  exact congrFun (CorrectionStep.ParticularParameters.fromReference_coherent_amplitude
    D h gap j n i H hn hr) (PhysicalParticularWave.waveEquiv x)

include H hn hr in
theorem raw_pressure_pull (j : ℤ) (hk : (j : ℝ) * D.carrierBlock.frequency n ≠ 0) :
    (fun x => (raw D h gap j).pressure n (PhysicalParticularWave.waveEquiv x)) =
      PhysicalParticularWave.bandRawPressure D h (ChartScales.Q_pos n) (ChartScales.Q_pos D.reference.band)
        (gap n) ((j : ℝ) * D.carrierBlock.frequency n) j := by
  funext x
  exact congrFun (CorrectionStep.ParticularParameters.fromReference_coherent_pressure
    D h gap j n i H hn hr hk) (PhysicalParticularWave.waveEquiv x)

include H in
/-- The phase identity is derived on the full positive-radius lift from
the current-state band coherence and the same integer angular harmonic. -/
theorem bandPhase_eq (j : ℤ) (hj : j ≠ 0) (hf : ∀ m, D.carrierBlock.frequency m ≠ 0)
    {x : Cylinder} (hx : 0 < x.1.1) :
    PhysicalParticularWave.bandPhase D h (ChartScales.Q n) (ChartScales.Q D.reference.band)
      (gap n) ((j : ℝ) * D.carrierBlock.frequency n) j x =
        (raw D h gap j).phase n (PhysicalParticularWave.waveEquiv x) := by
  have hK : (j : ℝ) * D.carrierBlock.frequency n ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hj) (hf n)
  apply mul_left_cancel₀ hK
  have htarget := actualCarrier_phase D.background D.carrierBlock j hf n
    ((PhysicalParticularWave.waveEquiv x).1.1, (PhysicalParticularWave.waveEquiv x).2)
    (PhysicalParticularWave.waveEquiv x).1.2
  have href := actualCarrier_phase D.background D.carrierBlock j hf D.reference.band
    (PhysicalParticularWave.parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band)
      (PhysicalParticularWave.waveEquiv x).1.1, CommonCoverSolve.coverPower (gap n) (PhysicalParticularWave.waveEquiv x).2)
    (PhysicalParticularWave.waveEquiv x).1.2
  have hphase := H.block.phase
    (x := ((PhysicalParticularWave.waveEquiv x).1.1, (PhysicalParticularWave.waveEquiv x).2)) hx
  change D.carrierBlock.frequency n * D.carrierBlock.phase n _ =
    D.carrierBlock.frequency D.reference.band * D.carrierBlock.phase D.reference.band _ at hphase
  change ((j : ℝ) * D.carrierBlock.frequency n) * (raw D h gap j).phase n
    (PhysicalParticularWave.waveEquiv x) = _ at htarget
  change PhysicalParticularWave.referenceFrequency D j * PhysicalParticularWave.liftPhase D j
    (PhysicalParticularWave.cylinderChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) x) = _ at href
  rw [hphase, H.block.angular] at htarget
  unfold PhysicalParticularWave.bandPhase
  calc
    _ = PhysicalParticularWave.referenceFrequency D j * PhysicalParticularWave.liftPhase D j
        (PhysicalParticularWave.cylinderChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) x) := by
          field_simp [hf n]
    _ = _ := href.trans htarget.symm

include H in
theorem bandPhase_germ (j : ℤ) (hj : j ≠ 0) (hf : ∀ m, D.carrierBlock.frequency m ≠ 0)
    {x : Cylinder} (hx : 0 < x.1.1) :
    (fun y => (raw D h gap j).phase n (PhysicalParticularWave.waveEquiv y)) =ᶠ[𝓝 x]
      PhysicalParticularWave.bandPhase D h (ChartScales.Q n) (ChartScales.Q D.reference.band)
        (gap n) ((j : ℝ) * D.carrierBlock.frequency n) j := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst.fst).mem_nhds hx] with y hy
  exact (bandPhase_eq D h gap n i H j hj hf hy).symm

include H hn hr in
theorem corrected_amplitude_pull (T : TargetChart D s h n i) (j : ℤ) :
    (fun x => (corrected D s h gap j).amplitude n (PhysicalParticularWave.waveEquiv x)) =
      realizedCoefficient ((j : ℝ) * D.carrierBlock.frequency n)
        PhysicalResidualBridge.ScaledGraph.radius
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).radial
        PhysicalResidualBridge.ScaledGraph.angular
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).axial
        (fun x => (raw D h gap j).phase n (PhysicalParticularWave.waveEquiv x))
        (PhysicalParticularWave.bandRaw D h (ChartScales.Q_pos n) (ChartScales.Q_pos D.reference.band)
          (gap n) ((j : ℝ) * D.carrierBlock.frequency n) j) := by
  have hp := realizedCoefficient_pull PhysicalParticularWave.waveEquiv
    ((j : ℝ) * D.carrierBlock.frequency n) (D.background.radius n) ((raw D h gap j).phase n)
    (D.directions.radialField n) (fun _ => D.directions.angular)
    (D.directions.axialField (CorrectionStep.ParticularParameters.nativeStrip s) n)
    ((raw D h gap j).amplitude n)
  rw [T.radius, T.radial, T.angular, T.axial, raw_amplitude_pull D h gap n i H hn hr j] at hp
  exact hp.symm

include H hn hr in
theorem corrected_velocity_eq_band (T : TargetChart D s h n i) (j : ℤ) (hj : j ≠ 0)
    (hf : ∀ m, D.carrierBlock.frequency m ≠ 0) {x : Cylinder} (hx : 0 < x.1.1) :
    vectorMode ((corrected D s h gap j).frequency n) ((corrected D s h gap j).phase n)
      ((corrected D s h gap j).amplitude n) (PhysicalParticularWave.waveEquiv x) =
        PhysicalParticularWave.bandVelocity D h (ChartScales.Q_pos n)
          (ChartScales.Q_pos D.reference.band) i (gap n) ((j : ℝ) * D.carrierBlock.frequency n) j x := by
  have hΦ := bandPhase_germ D h gap n i H j hj hf hx
  have ha := congrFun (corrected_amplitude_pull D s h gap n i H hn hr T j) x
  have hg := (realizedCoefficient_phase_germ hΦ ((j : ℝ) * D.carrierBlock.frequency n)
    PhysicalResidualBridge.ScaledGraph.radius
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).radial
    PhysicalResidualBridge.ScaledGraph.angular
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).axial
    (PhysicalParticularWave.bandRaw D h (ChartScales.Q_pos n) (ChartScales.Q_pos D.reference.band)
      (gap n) ((j : ℝ) * D.carrierBlock.frequency n) j)).eq_of_nhds
  funext k
  change (corrected D s h gap j).amplitude n (PhysicalParticularWave.waveEquiv x) k *
    carrier ((j : ℝ) * D.carrierBlock.frequency n) ((raw D h gap j).phase n) (PhysicalParticularWave.waveEquiv x) = _
  rw [ha, hg]
  change _ * carrier ((j : ℝ) * D.carrierBlock.frequency n)
    (fun y => (raw D h gap j).phase n (PhysicalParticularWave.waveEquiv y)) x = _
  exact congrArg₂ (· * ·) rfl (PhysicalCurlCovariance.carrier_eq_of_products
    (congrArg (((j : ℝ) * D.carrierBlock.frequency n) * ·) hΦ.eq_of_nhds))

include H hn hr in
theorem corrected_pressure_eq_band (j : ℤ) (hj : j ≠ 0)
    (hf : ∀ m, D.carrierBlock.frequency m ≠ 0) {x : Cylinder} (hx : 0 < x.1.1) :
    mode ((corrected D s h gap j).frequency n) ((corrected D s h gap j).phase n)
      ((corrected D s h gap j).pressure n) (PhysicalParticularWave.waveEquiv x) =
        PhysicalParticularWave.bandPressureMode D h (ChartScales.Q_pos n)
          (ChartScales.Q_pos D.reference.band) (gap n) ((j : ℝ) * D.carrierBlock.frequency n) j x := by
  have hK : (j : ℝ) * D.carrierBlock.frequency n ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hj) (hf n)
  have hp := congrFun (raw_pressure_pull D h gap n i H hn hr j hK) x
  have hΦ := (bandPhase_eq D h gap n i H j hj hf hx).symm
  change (raw D h gap j).pressure n (PhysicalParticularWave.waveEquiv x) * _ = _
  rw [hp]
  exact congrArg₂ (· * ·) rfl (PhysicalCurlCovariance.carrier_eq_of_products
    (congrArg (((j : ℝ) * D.carrierBlock.frequency n) * ·) hΦ))

end Band

/-! ## The literal finite harmonic block -/

noncomputable def block (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
    (h : ℝ) (gap : ℕ → ℕ) (N : ℕ) : HarmonicBlock Associated :=
  (CorrectionStep.ParticularParameters.fromReference D h gap).updateBlock s
    D.context D.state D.carrierBlock D.gaussianInput D.aliasInput N

/-- Cylindrical coordinates with the cycle's slow-coordinate order and the
association used by the harmonic coefficient block. -/
noncomputable def associatedCylinder : Cylinder ≃ₗᵢ[ℝ] (Associated × ℝ) :=
  StateReindex.cylinder PhysicalResidualNaturality.associatedToLift.symm

theorem angleShuffle_associatedCylinder (x : Cylinder) :
    angleShuffle (associatedCylinder x) = PhysicalParticularWave.waveEquiv x := rfl

section Assembly

variable (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
  (h : ℝ) (gap : ℕ → ℕ)

open CopyAngularInvariance

theorem corrected_amplitude_invariant (j : ℤ)
    (B : BackgroundControl (CorrectionStep.ParticularParameters.nativeStrip s)
      D.directions D.background D.carrierBlock j) (n : ℕ) :
    Invariant (((0 : Parameter), (1 : ℝ)), (0 : Plane))
      ((corrected D s h gap j).amplitude n) := by
  have ha : Invariant D.directions.angular ((raw D h gap j).amplitude n) := by
    rw [B.angular]
    change Invariant _ (((CorrectionStep.ParticularParameters.fromReference D h gap).copyData
      D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j).common.amplitude n)
    rw [CorrectionStep.ParticularParameters.common_amplitude]
    exact angleLift_invariant _
  have hphi := actualCarrier_affine D.background D.carrierBlock j n
  rw [← B.angular] at hphi ⊢
  exact realizedCoefficient_invariant (B.radius_invariant n) (B.radial_invariant n)
    (Invariant.const _) (B.axial_invariant n) hphi ha ((j : ℝ) * D.carrierBlock.frequency n)

theorem corrected_pressure_invariant (j : ℤ)
    (hK : (j : ℝ) * D.carrierBlock.frequency n ≠ 0) :
    Invariant (((0 : Parameter), (1 : ℝ)), (0 : Plane))
      ((corrected D s h gap j).pressure n) := by
  change Invariant _ (((CorrectionStep.ParticularParameters.fromReference D h gap).copyData
    D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j).common.pressure n)
  rw [CorrectionStep.ParticularParameters.common_pressure _ _ _ _ _ _ _ _ hK]
  exact angleLift_invariant _

theorem block_velocity_represents {N : ℕ}
    (B : ∀ j ∈ modes N, BackgroundControl (CorrectionStep.ParticularParameters.nativeStrip s)
      D.directions D.background D.carrierBlock j)
    (hf : ∀ m, D.carrierBlock.frequency m ≠ 0) (n : ℕ) (x : Associated × ℝ) (k : Fin 3) :
    (block D s h gap N).oscillation n x k =
      ∑ j ∈ modes N, (vectorMode ((corrected D s h gap j).frequency n)
        ((corrected D s h gap j).phase n) ((corrected D s h gap j).amplitude n)
          (angleShuffle x) k).re := by
  rw [block, CorrectionStep.ParticularParameters.updateBlock, assembledBlock_value]
  apply Finset.sum_congr rfl
  intro j hj
  have hi := invariant_angleShuffle (corrected_amplitude_invariant D s h gap j (B j hj) n) x.1 x.2
  change Complex.re (_ * _) = ((corrected D s h gap j).amplitude n (angleShuffle x) k *
    carrier ((actualCarrier D.background D.carrierBlock j).frequency n)
      ((actualCarrier D.background D.carrierBlock j).phase n) (angleShuffle x)).re
  rw [actualCarrier_character D.background D.carrierBlock j hf n x, hi]
  rfl

theorem block_pressure_represents {N : ℕ}
    (hj : ∀ j ∈ modes N, j ≠ 0) (hf : ∀ m, D.carrierBlock.frequency m ≠ 0)
    (n : ℕ) (x : Associated × ℝ) :
    (block D s h gap N).oscillatoryPressure n x =
      ∑ j ∈ modes N, (mode ((corrected D s h gap j).frequency n)
        ((corrected D s h gap j).phase n) ((corrected D s h gap j).pressure n) (angleShuffle x)).re := by
  rw [block, CorrectionStep.ParticularParameters.updateBlock, assembledBlock_pressure_value]
  apply Finset.sum_congr rfl
  intro j hmem
  have hK : (j : ℝ) * D.carrierBlock.frequency n ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hj j hmem) (hf n)
  have hi := invariant_angleShuffle (corrected_pressure_invariant D s h gap j hK) x.1 x.2
  change Complex.re (_ * _) = ((corrected D s h gap j).pressure n (angleShuffle x) *
    carrier ((actualCarrier D.background D.carrierBlock j).frequency n)
      ((actualCarrier D.background D.carrierBlock j).phase n) (angleShuffle x)).re
  rw [actualCarrier_character D.background D.carrierBlock j hf n x, hi]
  rfl

variable (n i : ℕ)
  (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
    (ChartScales.Q_pos D.reference.band) i (gap n) n)
  (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
  (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput D.reference.band)

include H hn hr in
theorem block_velocity_eq_band (T : TargetChart D s h n i) {N : ℕ}
    (B : ∀ j ∈ modes N, BackgroundControl (CorrectionStep.ParticularParameters.nativeStrip s)
      D.directions D.background D.carrierBlock j)
    (hj : ∀ j ∈ modes N, j ≠ 0) (hf : ∀ m, D.carrierBlock.frequency m ≠ 0)
    {x : Cylinder} (hx : 0 < x.1.1) (k : Fin 3) :
    (block D s h gap N).oscillation n (associatedCylinder x) k =
      PhysicalParticularWave.labelBandVelocity D h (ChartScales.Q_pos n)
        (ChartScales.Q_pos D.reference.band) i (gap n)
        (fun j => (j : ℝ) * D.carrierBlock.frequency n) N x k := by
  rw [block_velocity_represents D s h gap B hf]
  unfold PhysicalParticularWave.labelBandVelocity
  apply Finset.sum_congr rfl
  intro j hmem
  rw [angleShuffle_associatedCylinder, corrected_velocity_eq_band D s h gap n i H hn hr T j (hj j hmem) hf hx]

include H hn hr in
theorem block_pressure_eq_band {N : ℕ}
    (hj : ∀ j ∈ modes N, j ≠ 0) (hf : ∀ m, D.carrierBlock.frequency m ≠ 0)
    {x : Cylinder} (hx : 0 < x.1.1) :
    (block D s h gap N).oscillatoryPressure n (associatedCylinder x) =
      PhysicalParticularWave.labelBandPressure D h (ChartScales.Q_pos n)
        (ChartScales.Q_pos D.reference.band) (gap n)
        (fun j => (j : ℝ) * D.carrierBlock.frequency n) N x := by
  rw [block_pressure_represents D s h gap hj hf]
  unfold PhysicalParticularWave.labelBandPressure
  apply Finset.sum_congr rfl
  intro j hmem
  rw [angleShuffle_associatedCylinder, corrected_pressure_eq_band D s h gap n i H hn hr j (hj j hmem) hf hx]

end Assembly

/-! ## Primitive frame matching -/

theorem targetChart_of_frameMatch (D : AssemblyData Parameter)
    (s : WeightedClasses.StripData Associated) (h : ℝ) (n i : ℕ)
    (hm : CorrectionStep.WaveFrameMatch D.context (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle D.directions) (reindexCoefficients angleShuffle D.background))
    (hframe : HarmonicResidual.contextFrame D.context n =
      PhysicalResidualNaturality.associatedFrame h (ChartScales.Q n) i) :
    TargetChart D s h n i := by
  have hr : StateReindex.vector (angleShuffle (P := Parameter)) (D.directions.radialField n) =
      CorrectionStep.radialDirection D.context n :=
    (reindex_radialField (angleShuffle (P := Parameter)) D.directions n).symm.trans (hm.radial n)
  have hz : StateReindex.vector (angleShuffle (P := Parameter))
      (D.directions.axialField (CorrectionStep.ParticularParameters.nativeStrip s) n) =
        CorrectionStep.axialDirection D.context n := by
    change reindexVector angleShuffle (D.directions.axialField
      (CorrectionStep.ParticularParameters.nativeStrip s) n) = _
    rw [← reindex_axialField, CorrectionStep.ParticularParameters.angleStrip_nativeStrip]
    exact hm.axial n
  have ht : StateReindex.vector (angleShuffle (P := Parameter)) (fun _ => D.directions.angular) =
      CorrectionStep.angularDirection (D := Associated) := by
    funext y
    exact hm.angular
  constructor
  · funext x
    exact (congrFun (hm.radius n) (associatedCylinder x)).trans
      (congrArg (fun g : HarmonicResidual.Frame Associated => g.radius (associatedCylinder x).1) hframe)
  · change StateReindex.vector associatedCylinder
      (StateReindex.vector angleShuffle (D.directions.radialField n)) = _
    rw [hr]
    change StateReindex.vector associatedCylinder
      (fun y => ((HarmonicResidual.contextFrame D.context n).radial y.1, 0)) = _
    rw [hframe]
    rfl
  · change StateReindex.vector associatedCylinder
      (StateReindex.vector angleShuffle (fun _ => D.directions.angular)) = _
    rw [ht]
    rfl
  · change StateReindex.vector associatedCylinder
      (StateReindex.vector angleShuffle (D.directions.axialField
        (CorrectionStep.ParticularParameters.nativeStrip s) n)) = _
    rw [hz]
    change StateReindex.vector associatedCylinder
      (fun y => ((HarmonicResidual.contextFrame D.context n).axial y.1, 0)) = _
    rw [hframe]
    rfl

/-! ## One fixed Cartesian reference label -/

section Physical

open ProblemStatement PhysicalParticularWave

variable (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
  (h : ℝ) (gap : ℕ → ℕ) (n i : ℕ)
  (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
    (ChartScales.Q_pos D.reference.band) i (gap n) n)
  (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
  (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput D.reference.band)
  (T : TargetChart D s h n i)
  {N : ℕ} {α κ : ℝ} (C : D.controls N α κ)
  (hstrip : D.strip = CorrectionStep.ParticularParameters.nativeStrip s)

include H hn hr T C hstrip in
theorem block_velocity_physical
    (Href : ReferenceChart D h (ChartScales.Q D.reference.band) (i + gap n))
    {U : Set Parameter} (hU : IsOpen U) (R : ∀ j ∈ modes N, ReferenceODE D j U)
    {z : SpaceTime}
    (hz : z ∈ (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).source
      (bandDomain D h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) U))
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) (k : Fin 3) :
    (block D s h gap N).oscillation n
      (associatedCylinder ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).map z)) k =
        (ChartScales.Q n) ^ CoordinateAlgebra.A h * CylindricalResidual.frame (-(z.2 1))
          (labelVelocity D h (ChartScales.Q D.reference.band) (i + gap n) delta N
            (z.1, CylindricalResidual.chart z.2)) k := by
  by_cases hN : N = 0
  · subst N
    simp [block, CorrectionStep.ParticularParameters.updateBlock, assembledBlock_value,
      modes, labelVelocity, labelPotential, SpatialCurl.spatialCurl,
      SpatialCurl.curl, CylindricalResidual.frame]
  have hm : ∃ j, j ∈ modes N := by
    refine ⟨1, ?_⟩
    simp only [modes, Finset.mem_erase, ne_eq, one_ne_zero, not_false_eq_true,
      Finset.mem_Icc, true_and]
    constructor <;> omega
  obtain ⟨j, hj⟩ := hm
  rw [block_velocity_eq_band D s h gap n i H hn hr T
    (fun j hj => hstrip ▸ (C j hj).background)
    (fun j hj => (C j hj).harmonic_ne) (C j hj).frequency_ne hz.2.1 k]
  exact label_physical_velocity D (ChartScales.Q_pos n) (ChartScales.Q_pos D.reference.band)
    i (gap n) Href C (fun j => (j : ℝ) * D.carrierBlock.frequency n)
    (fun j hj => mul_ne_zero (by exact_mod_cast (C j hj).harmonic_ne) ((C j hj).frequency_ne n))
    hU R hz hdelta chart hchart k

include H hn hr C in
theorem block_pressure_physical
    {U : Set Parameter} (R : ∀ j ∈ modes N, ReferenceODE D j U)
    {z : SpaceTime} (hz : 0 < z.2 0)
    (hp : parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band)
      (nativeMap h (ChartScales.Q n) i z).1.1 ∈ U)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    (block D s h gap N).oscillatoryPressure n
      (associatedCylinder ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).map z)) =
        (ChartScales.Q n) ^ (2 * CoordinateAlgebra.A h) *
          labelPressure D h (ChartScales.Q D.reference.band) (i + gap n) delta N
            (z.1, CylindricalResidual.chart z.2) := by
  by_cases hN : N = 0
  · subst N
    simp [block, CorrectionStep.ParticularParameters.updateBlock, assembledBlock_pressure_value,
      modes, labelPressure]
  have hm : ∃ j, j ∈ modes N := by
    refine ⟨1, ?_⟩
    simp only [modes, Finset.mem_erase, ne_eq, one_ne_zero, not_false_eq_true,
      Finset.mem_Icc, true_and]
    constructor <;> omega
  obtain ⟨j, hj⟩ := hm
  rw [block_pressure_eq_band D s h gap n i H hn hr
    (fun j hj => (C j hj).harmonic_ne) (C j hj).frequency_ne
    (mul_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) hz)]
  exact label_physical_pressure D h (ChartScales.Q_pos n) (ChartScales.Q_pos D.reference.band)
    i (gap n) (fun j => (j : ℝ) * D.carrierBlock.frequency n)
    (fun j hj => mul_ne_zero (by exact_mod_cast (C j hj).harmonic_ne) ((C j hj).frequency_ne n))
    (fun j hj => mul_ne_zero (by exact_mod_cast (C j hj).harmonic_ne) ((C j hj).frequency_ne D.reference.band))
    R hz hp hdelta chart hchart

end Physical

/-! ## The cycle's actual coordinate layout -/

noncomputable def cycleBlock (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
    (h : ℝ) (gap : ℕ → ℕ) (N : ℕ) : HarmonicBlock CorrectionStep.CyclePoint :=
  StateReindex.block CorrectionStep.cycleAssoc (block D s h gap N)

theorem cycleBlock_velocity (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
    (h : ℝ) (gap : ℕ → ℕ) (N n : ℕ) (x : Cylinder) :
    (cycleBlock D s h gap N).oscillation n (PhysicalResidualTZ.swapCylinder x) =
      (block D s h gap N).oscillation n (associatedCylinder x) := by
  rw [cycleBlock, StateReindex.block_oscillation]
  rfl

theorem cycleBlock_pressure (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
    (h : ℝ) (gap : ℕ → ℕ) (N n : ℕ) (x : Cylinder) :
    (cycleBlock D s h gap N).oscillatoryPressure n (PhysicalResidualTZ.swapCylinder x) =
      (block D s h gap N).oscillatoryPressure n (associatedCylinder x) := by
  rw [cycleBlock, StateReindex.block_pressure]
  rfl

section CyclePhysical

open ProblemStatement PhysicalParticularWave CyclePhysicalPrefixes

variable (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
  (h : ℝ) (gap : ℕ → ℕ) (n i : ℕ)
  (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
    (ChartScales.Q_pos D.reference.band) i (gap n) n)
  (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
  (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput D.reference.band)
  (T : TargetChart D s h n i)
  {N : ℕ} {α κ : ℝ} (C : D.controls N α κ)
  (hstrip : D.strip = CorrectionStep.ParticularParameters.nativeStrip s)
  {I : ℕ} (hcover : i + gap n = I)
  (Href : ReferenceChart D h (ChartScales.Q D.reference.band) I)
  {U : Set Parameter} (hU : IsOpen U) (R : ∀ j ∈ modes N, ReferenceODE D j U)
  {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)

include H hn hr T C hstrip hcover Href hU R hdelta in
/-- The exact cycle block is the cylindrical view of one fixed reference
curl. The covering index enters only through `i + gap n = I`. -/
theorem cycle_velocity_cylindrical {z : SpaceTime}
    (hz : z ∈ (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).source
      (bandDomain D h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) U))
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    velocityMap (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i)
      ((cycleBlock D s h gap N).oscillation n) z =
        CylindricalResidual.frame (-(z.2 1))
          (labelVelocity D h (ChartScales.Q D.reference.band) I delta N
            (z.1, CylindricalResidual.chart z.2)) := by
  have Href' : ReferenceChart D h (ChartScales.Q D.reference.band) (i + gap n) := hcover.symm ▸ Href
  ext k
  change (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).velocity
    (fun x => (cycleBlock D s h gap N).oscillation n (PhysicalResidualTZ.swapCylinder x)) z k = _
  rw [PhysicalResidualBridge.ScaledGraph.velocity_apply, cycleBlock_velocity,
    block_velocity_physical D s h gap n i H hn hr T C hstrip Href' hU R hz hdelta chart hchart k,
    hcover]
  change (ChartScales.Q n) ^ (-CoordinateAlgebra.A h) *
    ((ChartScales.Q n) ^ CoordinateAlgebra.A h * _) = _
  rw [← mul_assoc, ← Real.rpow_add (ChartScales.Q_pos n)]
  simp

include H hn hr T C hstrip hcover Href hU R hdelta in
/-- Cartesian realization of the literal stored finite harmonic block,
using the same physical potential for every compatible covering. -/
theorem cycle_velocity_realization {z : SpaceTime}
    (hz : z ∈ (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).source
      (bandDomain D h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) U))
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    polarVelocityMap delta chart
      (velocityMap (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i)
        ((cycleBlock D s h gap N).oscillation n)) (z.1, CylindricalResidual.chart z.2) =
      SpatialCurl.spatialCurl (labelPotential D h (ChartScales.Q D.reference.band) I delta N)
        (z.1, CylindricalResidual.chart z.2) := by
  change CylindricalResidual.frame
    (PhysicalCurlCovariance.polarInput delta chart (z.1, CylindricalResidual.chart z.2)).2
    (velocityMap _ ((cycleBlock D s h gap N).oscillation n)
      (PhysicalCurlCovariance.polarCoordinates delta chart (z.1, CylindricalResidual.chart z.2))) = _
  rw [PhysicalCurlCovariance.polarInput_forward hdelta chart hchart,
    PhysicalCurlCovariance.polarCoordinates_forward hdelta chart hchart,
    cycle_velocity_cylindrical D s h gap n i H hn hr T C hstrip hcover Href hU R hdelta chart hz hchart,
    CylindricalResidual.frame_inverse']
  rfl

include H hn hr C hcover R hdelta in
theorem cycle_pressure_realization {z : SpaceTime} (hz : 0 < z.2 0)
    (hp : parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band)
      (nativeMap h (ChartScales.Q n) i z).1.1 ∈ U)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    polarPressureMap delta chart
      (pressureMap (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i)
        ((cycleBlock D s h gap N).oscillatoryPressure n)) (z.1, CylindricalResidual.chart z.2) =
      labelPressure D h (ChartScales.Q D.reference.band) I delta N
        (z.1, CylindricalResidual.chart z.2) := by
  change pressureMap _ ((cycleBlock D s h gap N).oscillatoryPressure n)
    (PhysicalCurlCovariance.polarCoordinates delta chart (z.1, CylindricalResidual.chart z.2)) = _
  rw [PhysicalCurlCovariance.polarCoordinates_forward hdelta chart hchart]
  change ((ChartScales.Q n) ^ (-CoordinateAlgebra.A h)) ^ 2 *
    (cycleBlock D s h gap N).oscillatoryPressure n
      (PhysicalResidualTZ.swapCylinder ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).map z)) = _
  rw [cycleBlock_pressure, block_pressure_physical D s h gap n i H hn hr C R hz hp hdelta chart hchart,
    hcover, ← mul_assoc, ← Real.rpow_mul_natCast (ChartScales.Q_pos n).le,
    ← Real.rpow_add (ChartScales.Q_pos n)]
  have hexp : -CoordinateAlgebra.A h * (2 : ℝ) + 2 * CoordinateAlgebra.A h = 0 := by ring
  norm_num only [Nat.cast_ofNat]
  rw [hexp]
  simp

end CyclePhysical

/-! ## Binding to the current cycle inputs -/

/-- These are equalities of the current input fields and primitive solver
data. There is no equality of a solved field in the interface. -/
structure CurrentInputs {ι : Type} (D : AssemblyData Parameter)
    (p : CorrectionStep.CycleParameters ι) (v : CorrectionStep.CycleCoefficients ι)
    (c : Context CorrectionStep.CyclePoint) (u : State CorrectionStep.CyclePoint)
    (l : ι) (h : ℝ) (gap : ℕ → ℕ) : Prop where
  context : D.context = StateReindex.context CorrectionStep.cycleAssoc.symm c
  state : D.state = StateReindex.state CorrectionStep.cycleAssoc.symm u
  carrier : D.carrierBlock = StateReindex.block CorrectionStep.cycleAssoc.symm (v.blocks l)
  gaussian : D.gaussianInput = StateReindex.blockCoefficients CorrectionStep.cycleAssoc.symm (v.gaussian l)
  aliasError : D.aliasInput = StateReindex.blockCoefficients CorrectionStep.cycleAssoc.symm (v.aliasCoefficients l)
  parameters : p.particular l = CorrectionStep.ParticularParameters.fromReference D h gap

theorem CurrentInputs.particularBlock {ι : Type} {D : AssemblyData Parameter}
    {p : CorrectionStep.CycleParameters ι} {v : CorrectionStep.CycleCoefficients ι}
    {c : Context CorrectionStep.CyclePoint} {u : State CorrectionStep.CyclePoint}
    {l : ι} {h : ℝ} {gap : ℕ → ℕ} (J : CurrentInputs D p v c u l h gap) :
    p.particularBlock v c u l = cycleBlock D
      (reindexStrip CorrectionStep.cycleAssoc.symm p.strip) h gap v.residualBand := by
  unfold CorrectionStep.CycleParameters.particularBlock cycleBlock block
  rw [J.parameters, J.context, J.state, J.carrier, J.gaussian, J.aliasError]

/-! ## Full-variable transport of the curl correction -/

section FullVariable

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Primitive spatial scaling on an open set. Angular differentiation has
unit scale and the two spatial directions have scale `l`. -/
structure SpatialScaling (Γ : E → F) (r : E → ℝ) (R : F → ℝ)
    (Sr Sθ Sz : E → E) (Vr Vθ Vz : F → F) (l : ℝ) (U : Set E) : Prop where
  isOpen : IsOpen U
  scale_ne : l ≠ 0
  radius_ne : ∀ x ∈ U, r x ≠ 0
  differentiable : ∀ x ∈ U, DifferentiableAt ℝ Γ x
  radial : ∀ x ∈ U, fderiv ℝ Γ x (Sr x) = l • Vr (Γ x)
  angular : ∀ x ∈ U, fderiv ℝ Γ x (Sθ x) = Vθ (Γ x)
  axial : ∀ x ∈ U, fderiv ℝ Γ x (Sz x) = l • Vz (Γ x)
  radius : ∀ x ∈ U, R (Γ x) = l * r x

variable {Γ : E → F} {r : E → ℝ} {R : F → ℝ}
  {Sr Sθ Sz : E → E} {Vr Vθ Vz : F → F} {l : ℝ} {U : Set E}
  (G : SpatialScaling Γ r R Sr Sθ Sz Vr Vθ Vz l U)
  {Φ : F → ℝ} {a : F → ComplexVector} {K L b : ℝ} (c : ℝ)
  (hK : K ≠ 0) (hb : b ≠ 0) (hKL : K * b = L)
  (hΦ : ∀ y ∈ U, DifferentiableAt ℝ Φ (Γ y))
  {x : E} (hx : x ∈ U)
  (hB : ∀ k, DifferentiableAt ℝ (fun y => coefficient R Vr Vθ Vz Φ a y k) (Γ x))

include G hK hb hKL hΦ hx hB



end FullVariable

namespace SpatialScaling

open PhysicalParticularWave


end SpatialScaling

section LiftedReference

open ProblemStatement PhysicalParticularWave

variable (D : AssemblyData Parameter) {h Qr : ℝ} {I : ℕ}
  (H : ReferenceChart D h Qr I) {j : ℤ} {α κ : ℝ}
  (C : LocalControl D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j D.background D.copy D.strip D.directions α κ)




end LiftedReference

section FullBand

open ProblemStatement PhysicalParticularWave

variable (D : AssemblyData Parameter) {h Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
  (i gap : ℕ) (H : ReferenceChart D h Qr (i + gap)) {j : ℤ} {α κ : ℝ}
  (C : LocalControl D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j D.background D.copy D.strip D.directions α κ)
  {K : ℝ} (hK : K ≠ 0) {U : Set Parameter} (hU : IsOpen U) (R : ReferenceODE D j U)


end FullBand





section ActualReferenceFields

open ProblemStatement PhysicalParticularWave

variable (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
  (h : ℝ) (gap : ℕ → ℕ) (n i : ℕ)
  (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
    (ChartScales.Q_pos D.reference.band) i (gap n) n)
  (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
  (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput D.reference.band)
  (T : TargetChart D s h n i)
  (Href : ReferenceChart D h (ChartScales.Q D.reference.band) (i + gap n))
  {U : Set Parameter} (hU : IsOpen U)





end ActualReferenceFields

/-! ## Direct consumers for the current correction step -/

section CurrentCycle

open ProblemStatement PhysicalParticularWave CyclePhysicalPrefixes

variable {ι : Type} {D : AssemblyData Parameter}
  {p : CorrectionStep.CycleParameters ι} {v : CorrectionStep.CycleCoefficients ι}
  {c : Context CorrectionStep.CyclePoint} {u : State CorrectionStep.CyclePoint}
  {label : ι} {h : ℝ} {gap : ℕ → ℕ} (J : CurrentInputs D p v c u label h gap)
  (n i : ℕ)
  (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
    (ChartScales.Q_pos D.reference.band) i (gap n) n)
  (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
  (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput D.reference.band)
  {α κ : ℝ} (C : D.controls v.residualBand α κ)

include J H hn hr C in
theorem CurrentInputs.velocity_realization
    (hstrip : D.strip = CorrectionStep.ParticularParameters.nativeStrip
      (reindexStrip CorrectionStep.cycleAssoc.symm p.strip))
    (hm : CorrectionStep.WaveFrameMatch D.context
      (HarmonicWaveInteraction.productStrip (reindexStrip CorrectionStep.cycleAssoc.symm p.strip))
      (reindexDirections angleShuffle D.directions) (reindexCoefficients angleShuffle D.background))
    {I : ℕ} (hcover : i + gap n = I)
    (Href : ReferenceChart D h (ChartScales.Q D.reference.band) I)
    {U : Set Parameter} (hU : IsOpen U) (R : ∀ j ∈ modes v.residualBand, ReferenceODE D j U)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index) {z : SpaceTime}
    (hz : z ∈ (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).source
      (bandDomain D h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) U))
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    polarVelocityMap delta chart
      (velocityMap (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i)
        ((p.particularBlock v c u label).oscillation n)) (z.1, CylindricalResidual.chart z.2) =
      SpatialCurl.spatialCurl (labelPotential D h (ChartScales.Q D.reference.band) I delta v.residualBand)
        (z.1, CylindricalResidual.chart z.2) := by
  rw [J.particularBlock]
  exact cycle_velocity_realization D (reindexStrip CorrectionStep.cycleAssoc.symm p.strip) h gap n i
    H hn hr (targetChart_of_frameMatch D _ h n i hm H.targetFrame) C hstrip hcover Href hU R
    hdelta chart hz hchart

include J H hn hr C in
theorem CurrentInputs.pressure_realization
    {I : ℕ} (hcover : i + gap n = I)
    {U : Set Parameter} (R : ∀ j ∈ modes v.residualBand, ReferenceODE D j U)
    {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index) {z : SpaceTime}
    (hz : 0 < z.2 0)
    (hp : parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band)
      (nativeMap h (ChartScales.Q n) i z).1.1 ∈ U)
    (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart) :
    polarPressureMap delta chart
      (pressureMap (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i)
        ((p.particularBlock v c u label).oscillatoryPressure n)) (z.1, CylindricalResidual.chart z.2) =
      labelPressure D h (ChartScales.Q D.reference.band) I delta v.residualBand
        (z.1, CylindricalResidual.chart z.2) := by
  rw [J.particularBlock]
  exact cycle_pressure_realization D (reindexStrip CorrectionStep.cycleAssoc.symm p.strip) h gap n i
    H hn hr C hcover R hdelta chart hz hp hchart

end CurrentCycle

/-- The Cartesian image of the actual common-chart domain and valid
polar branch; no extension of the raw formulas beyond this set is used. -/
noncomputable def physicalDomain (D : AssemblyData Parameter) (h : ℝ) (n i gap : ℕ)
    (U : Set Parameter) (delta : ℝ) (chart : PolarCharts.Index) : Set ProblemStatement.SpaceTime :=
  (fun z : ProblemStatement.SpaceTime => (z.1, CylindricalResidual.chart z.2)) ''
    ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).source
      (PhysicalParticularWave.bandDomain D h (ChartScales.Q n) (ChartScales.Q D.reference.band) gap U) ∩
        PhysicalCurlCovariance.validCylindrical delta chart)

section LocalIdentity

open ProblemStatement PhysicalParticularWave CyclePhysicalPrefixes

variable (D : AssemblyData Parameter) (s : WeightedClasses.StripData Associated)
  (h : ℝ) (gap : ℕ → ℕ) (n i : ℕ)
  (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
    (ChartScales.Q_pos D.reference.band) i (gap n) n)
  (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
  (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput D.reference.band)
  (T : TargetChart D s h n i)
  {N : ℕ} {α κ : ℝ} (C : D.controls N α κ)
  (hstrip : D.strip = CorrectionStep.ParticularParameters.nativeStrip s)
  {I : ℕ} (hcover : i + gap n = I)
  (Href : ReferenceChart D h (ChartScales.Q D.reference.band) I)
  {U : Set Parameter} (hU : IsOpen U) (R : ∀ j ∈ modes N, ReferenceODE D j U)
  {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)



end LocalIdentity

end NavierStokes.ActualParticularRealization

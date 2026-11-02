import NavierStokes.AssembledSlowBase
import NavierStokes.GlobalStressSupport
import NavierStokes.BaseResidual
import NavierStokes.SlowDivergence
import NavierStokes.PreparedOutgoing
import NavierStokes.BaseExterior
import NavierStokes.TerminalHistoryBridge
import NavierStokes.ModulatedProfileAssembly
import NavierStokes.FirstOrderBaseEdge

/-!
# The actual constructed slow base

The finite residual identities, regular axis descriptors, and stress support
used here are derived from the same repaired coefficient sequence.  No
residual estimate or infinite-dimensional output certificate is an input.
-/
/-! Merged from `NavierStokes.BasePrefixIdentity` (in a section, so its `open`s cannot leak). -/
section
/-!
# The curl of the finite slow potentials

The finite Borel prefixes use the average of the axial coefficient and the
primitive of the angular coefficient.  Their curl is identified here with
the finite slow field, using the actual radial flux formula and FTC.
-/

noncomputable section

namespace NavierStokes.BasePrefixIdentity

open Set Filter
open scoped Topology ContDiff


open SlowBorelBase (Inner Chart Coefficients SmoothCoefficients)

/-- Differentiating the actual primitive gives the radial average identity. -/
theorem average_radial_identity {U : Inner → ℝ} (hU : ContDiff ℝ ∞ U) (w : Inner) :
    ProfileHistories.average U w + w.1 * SimilarityProfile.partialX (ProfileHistories.average U) w =
      U w := by
  have he : ProfileHistories.primitive U =
      fun y => y.1 * ProfileHistories.average U y :=
    funext (ProfileHistories.primitive_eq_mul_average U)
  have hf : HasFDerivAt (fun y : Inner => y.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) w :=
    hasFDerivAt_fst
  have hd := hf.fun_mul
    ((SlowBorelBase.average_smooth hU).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hi := congrFun (SlowBorelBase.partialX_primitive hU) w
  rw [he] at hi
  unfold SimilarityProfile.partialX at hi ⊢
  rw [hd.fderiv] at hi
  simpa [add_comm] using hi

/-- The flux computed from histories is the axial derivative of the averaged
stream coefficient, with its exact exponent.  No divergence equation is assumed. -/
theorem radialFlux_eq_neg_X_Z_average {U : Inner → ℝ} (hU : ContDiff ℝ ∞ U)
    (h lam : ℝ) (w : Inner) :
    SlowDivergence.radialFlux h lam U w =
      -w.1 * SimilarityProfile.Z h (-CoordinateAlgebra.A h + lam) (ProfileHistories.average U) w := by
  have hi := average_radial_identity hU w
  unfold SlowDivergence.radialFlux SimilarityProfile.Z CoordinateAlgebra.axialCoeff
  rw [← hi]
  simp only [CoordinateAlgebra.A, CoordinateAlgebra.D, div_eq_mul_inv]
  ring

/-- The direct finite profile and the finite Borel prefix have the same local
germ throughout the past-time chart. -/
theorem physicalUncutPrefix_germ {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (b : ℝ) (f : ℕ → Inner → ℝ) (J : ℕ) {p : Chart} (hp : p.1 < 1) :
    SlowBorelBase.physicalUncutPrefix h b f J =ᶠ[𝓝 p] SlowExpansionResidual.finiteProfile J h b f := by
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hp] with y hy
  exact SlowBorelBase.physicalUncutPrefix_eq_finiteProfile hh hh1 b f J hy

theorem partialS_physicalUncutPrefix {h b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (J : ℕ) (f : ℕ → Inner → ℝ) {p : Chart} (hp : p.1 < 1)
    (hf : ∀ n ≤ J, DifferentiableAt ℝ (f n) (SimilarityProfile.inner h p)) :
    AxisymmetricFields.partialS (SlowBorelBase.physicalUncutPrefix h b f J) p =
      SlowExpansionResidual.finiteProfile J h (b - 1) (fun n => SimilarityProfile.partialX (f n)) p := by
  change fderiv ℝ _ p (0, (1, 0)) = _
  rw [(physicalUncutPrefix_germ hh hh1 b f J hp).fderiv_eq]
  exact SlowExpansionResidual.partialS_finiteProfile hh hh1 J f hp hf

theorem partialZ_physicalUncutPrefix {h b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (J : ℕ) (f : ℕ → Inner → ℝ) {p : Chart} (hp : p.1 < 1)
    (hf : ∀ n ≤ J, DifferentiableAt ℝ (f n) (SimilarityProfile.inner h p)) :
    AxisymmetricFields.partialZ (SlowBorelBase.physicalUncutPrefix h b f J) p =
      SlowExpansionResidual.finiteProfile J h (b - CoordinateAlgebra.D h)
        (fun n => SimilarityProfile.Z h (b + SlowExpansionResidual.slowOrder h n) (f n)) p := by
  change fderiv ℝ _ p (0, (0, 1)) = _
  rw [(physicalUncutPrefix_germ hh hh1 b f J hp).fderiv_eq]
  exact SlowExpansionResidual.partialZ_finiteProfile hh hh1 J f hp hf

/-- The coefficient family whose flux is constructed from its axial history. -/
noncomputable def profiles (h : ℝ) (d : Coefficients) : SlowExpansionResidual.SlowProfiles where
  phi := d.phi
  axial := d.axial
  pressure := d.pressure
  flux n := SlowDivergence.radialFlux h (SlowExpansionResidual.slowOrder h n) (d.axial n)

theorem prefixStream_axial {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) (J : ℕ) (C : ℝ)
    {p : Chart} (hp : p.1 < 1) :
    BaseResidual.prefixStream J h C d p + p.2.1 * AxisymmetricFields.partialS (BaseResidual.prefixStream J h C d) p =
      SlowExpansionResidual.slowAxial J h (profiles h d) p := by
  have hq := SimilarityProfile.q_pos hh hh1 hp
  rw [BaseResidual.prefixStream, SlowBorelBase.physicalUncutPrefix_eq_finiteProfile hh hh1 _ _ _ hp]
  rw [partialS_physicalUncutPrefix hh hh1 J _ hp
    (fun n _ => ((SlowBorelBase.bundleComponent_smooth hd C 0 n).differentiable (by simp)).differentiableAt)]
  simp only [SlowExpansionResidual.slowAxial, SlowExpansionResidual.axialExponent, profiles, SlowExpansionResidual.finiteProfile,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  change SimilarityProfile.pullback h (-CoordinateAlgebra.A h + SlowExpansionResidual.slowOrder h n)
      (ProfileHistories.average (d.axial n)) p +
      p.2.1 * SimilarityProfile.pullback h (-CoordinateAlgebra.A h - 1 + SlowExpansionResidual.slowOrder h n)
        (SimilarityProfile.partialX (ProfileHistories.average (d.axial n))) p =
    SimilarityProfile.pullback h (-CoordinateAlgebra.A h + SlowExpansionResidual.slowOrder h n) (d.axial n) p
  have hi := average_radial_identity (hd.axial n) (SimilarityProfile.inner h p)
  rw [show -CoordinateAlgebra.A h - 1 + SlowExpansionResidual.slowOrder h n =
    (-CoordinateAlgebra.A h + SlowExpansionResidual.slowOrder h n) - 1 by ring]
  simp only [SimilarityProfile.pullback, Real.rpow_sub_one hq.ne']
  rw [← hi]
  simp only [SimilarityProfile.inner, SimilarityProfile.X]
  ring

theorem prefixSwirl_radial {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) (J : ℕ) (C : ℝ)
    {p : Chart} (hp : p.1 < 1) :
    -AxisymmetricFields.partialS (BaseResidual.prefixSwirl J h C d) p =
      SlowExpansionResidual.slowSwirl J h C (profiles h d) p := by
  rw [BaseResidual.prefixSwirl, partialS_physicalUncutPrefix hh hh1 J _ hp
    (fun n _ => ((SlowBorelBase.bundleComponent_smooth hd C 1 n).differentiable (by simp)).differentiableAt)]
  have he : (fun n => SimilarityProfile.partialX (SlowBorelBase.bundleComponent C d 1 n)) =
      fun n w => -C⁻¹ * d.phi n w := by
    funext n
    exact SlowBorelBase.partialX_swirl_primitive (hd.phi n) C
  rw [he]
  simp only [SlowExpansionResidual.slowSwirl, SlowExpansionResidual.angularExponent, profiles, SlowExpansionResidual.finiteProfile,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [SimilarityProfile.pullback]
  rw [show 1 / 2 - CoordinateAlgebra.A h - 1 + SlowExpansionResidual.slowOrder h n =
    -CoordinateAlgebra.A h - 1 / 2 + SlowExpansionResidual.slowOrder h n by ring]
  ring

theorem prefixStream_flux {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) (J : ℕ) (C : ℝ)
    {p : Chart} (hp : p.1 < 1) :
    -p.2.1 * AxisymmetricFields.partialZ (BaseResidual.prefixStream J h C d) p =
      SlowExpansionResidual.slowFlux J h (profiles h d) p := by
  have hq := SimilarityProfile.q_pos hh hh1 hp
  rw [BaseResidual.prefixStream, partialZ_physicalUncutPrefix hh hh1 J _ hp
    (fun n _ => ((SlowBorelBase.bundleComponent_smooth hd C 0 n).differentiable (by simp)).differentiableAt)]
  simp only [SlowExpansionResidual.slowFlux, profiles, SlowExpansionResidual.finiteProfile, Finset.mul_sum, zero_add]
  apply Finset.sum_congr rfl
  intro n hn
  change -p.2.1 * SimilarityProfile.pullback h
      (-CoordinateAlgebra.A h - CoordinateAlgebra.D h + SlowExpansionResidual.slowOrder h n)
      (SimilarityProfile.Z h (-CoordinateAlgebra.A h + SlowExpansionResidual.slowOrder h n)
        (ProfileHistories.average (d.axial n))) p =
    SimilarityProfile.pullback h (SlowExpansionResidual.slowOrder h n)
      (SlowDivergence.radialFlux h (SlowExpansionResidual.slowOrder h n) (d.axial n)) p
  rw [show -CoordinateAlgebra.A h - CoordinateAlgebra.D h + SlowExpansionResidual.slowOrder h n =
    SlowExpansionResidual.slowOrder h n - 1 by unfold CoordinateAlgebra.A CoordinateAlgebra.D; ring]
  simp only [SimilarityProfile.pullback, Real.rpow_sub_one hq.ne',
    radialFlux_eq_neg_X_Z_average (hd.axial n)]
  simp only [SimilarityProfile.inner, SimilarityProfile.X]
  ring

/-- The actual finite curl is the slow field with the flux constructed above. -/
theorem prefixVelocity_eq_profiles {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) (J : ℕ) (C : ℝ)
    {t : ℝ} (ht : t < 1) (x : ProblemStatement.Space)
    (hs : 0 < AxisymmetricFields.radialEnergy x) :
    BaseResidual.prefixVelocity J h C d (t, x) =
      SlowExpansionResidual.slowVelocity J h C (profiles h d) (t, x) := by
  have hH := (SlowBorelBase.physicalUncutPrefix_smoothAt hh hh1
    (SlowBorelBase.bundleComponent_smooth hd C 0) (-CoordinateAlgebra.A h) J
    (p := AxisymmetricFields.profilePoint t x) ht).differentiableAt (by simp)
  have hK := (SlowBorelBase.physicalUncutPrefix_smoothAt hh hh1
    (SlowBorelBase.bundleComponent_smooth hd C 1) (1 / 2 - CoordinateAlgebra.A h) J
    (p := AxisymmetricFields.profilePoint t x) ht).differentiableAt (by simp)
  change DifferentiableAt ℝ (BaseResidual.prefixStream J h C d)
    (AxisymmetricFields.profilePoint t x) at hH
  change DifferentiableAt ℝ (BaseResidual.prefixSwirl J h C d)
    (AxisymmetricFields.profilePoint t x) at hK
  have hu := prefixStream_axial hh hh1 hd J C (p := AxisymmetricFields.profilePoint t x) ht
  have hf := prefixSwirl_radial hh hh1 hd J C (p := AxisymmetricFields.profilePoint t x) ht
  have hv := prefixStream_flux hh hh1 hd J C (p := AxisymmetricFields.profilePoint t x) ht
  change AxisymmetricFields.velocity (BaseResidual.prefixStream J h C d)
    (BaseResidual.prefixSwirl J h C d) (t, x) = _
  rw [SlowExpansionResidual.slowVelocity_components]
  ext i
  fin_cases i
  · change AxisymmetricFields.velocity (BaseResidual.prefixStream J h C d)
      (BaseResidual.prefixSwirl J h C d) (t, x) 0 = _
    rw [AxisymmetricFields.velocity_zero _ _ _ _ hH hK, ← hf, ← hv]
    norm_num [AxisymmetricResidual.pack, ProblemStatement.coordinateVector, PiLp.single_apply]
    norm_num [Fin.ext_iff]
    dsimp only [AxisymmetricFields.profilePoint]
    field_simp [hs.ne']
  · change AxisymmetricFields.velocity (BaseResidual.prefixStream J h C d)
      (BaseResidual.prefixSwirl J h C d) (t, x) 1 = _
    rw [AxisymmetricFields.velocity_one _ _ _ _ hH hK, ← hf, ← hv]
    norm_num [AxisymmetricResidual.pack, ProblemStatement.coordinateVector, PiLp.single_apply]
    norm_num [Fin.ext_iff]
    dsimp only [AxisymmetricFields.profilePoint]
    field_simp [hs.ne'] ; ring
  · change AxisymmetricFields.velocity (BaseResidual.prefixStream J h C d)
      (BaseResidual.prefixSwirl J h C d) (t, x) 2 = _
    rw [AxisymmetricFields.velocity_two _ _ _ _ hH hK]
    simp [AxisymmetricResidual.pack, ProblemStatement.coordinateVector] at hu ⊢
    exact hu

/-- The physical similarity coordinates range inside this open half strip. -/
noncomputable def profileWindow : Set Inner := Ioi 0 ×ˢ Ioo (-1) 1

theorem profileWindow_open : IsOpen profileWindow := isOpen_Ioi.prod isOpen_Ioo

theorem inner_mem_profileWindow {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Chart} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    SimilarityProfile.inner h p ∈ profileWindow := by
  refine ⟨LeadingStress.inner_X_pos hh hh1 ht hs, ?_⟩
  have he := SimilarityProfile.eta_sq_lt_one hh hh1 ht
  change -1 < SimilarityProfile.eta h p ∧ SimilarityProfile.eta h p < 1
  constructor <;> nlinarith [sq_nonneg (SimilarityProfile.eta h p + 1),
    sq_nonneg (SimilarityProfile.eta h p - 1)]

/-- Only scalar coefficient values and the actual flux identity are needed
to identify the reconstructed velocity. -/
structure VelocityMatches (h : ℝ) (d : Coefficients)
    (f : SlowExpansionResidual.SlowProfiles) : Prop where
  phi : ∀ n, EqOn (d.phi n) (f.phi n) profileWindow
  axial : ∀ n, EqOn (d.axial n) (f.axial n) profileWindow
  flux : ∀ n, EqOn
    (SlowDivergence.radialFlux h (SlowExpansionResidual.slowOrder h n) (d.axial n))
    (f.flux n) profileWindow

theorem finiteProfile_eq_of_values (J : ℕ) (h b : ℝ)
    {f g : ℕ → Inner → ℝ} {p : Chart}
    (he : ∀ n ≤ J, f n (SimilarityProfile.inner h p) = g n (SimilarityProfile.inner h p)) :
    SlowExpansionResidual.finiteProfile J h b f p =
      SlowExpansionResidual.finiteProfile J h b g p := by
  apply Finset.sum_congr rfl
  intro n hn
  unfold SimilarityProfile.pullback
  rw [he n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))]

theorem prefixVelocity_eq_slowVelocity {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : VelocityMatches h d f) (J : ℕ) (C : ℝ)
    {t : ℝ} (ht : t < 1) (x : ProblemStatement.Space)
    (hs : 0 < AxisymmetricFields.radialEnergy x) :
    BaseResidual.prefixVelocity J h C d (t, x) =
      SlowExpansionResidual.slowVelocity J h C f (t, x) := by
  rw [prefixVelocity_eq_profiles hh hh1 hd J C ht x hs]
  have hw := inner_mem_profileWindow hh hh1 (p := AxisymmetricFields.profilePoint t x) ht hs
  have hv : SlowExpansionResidual.slowFlux J h (profiles h d)
      (AxisymmetricFields.profilePoint t x) =
      SlowExpansionResidual.slowFlux J h f (AxisymmetricFields.profilePoint t x) :=
    finiteProfile_eq_of_values J h 0 (fun n _ => hm.flux n hw)
  have hu : SlowExpansionResidual.slowAxial J h (profiles h d)
      (AxisymmetricFields.profilePoint t x) =
      SlowExpansionResidual.slowAxial J h f (AxisymmetricFields.profilePoint t x) :=
    finiteProfile_eq_of_values J h _ (fun n _ => hm.axial n hw)
  have hf : SlowExpansionResidual.slowSwirl J h C (profiles h d)
      (AxisymmetricFields.profilePoint t x) =
      SlowExpansionResidual.slowSwirl J h C f (AxisymmetricFields.profilePoint t x) := by
    exact congrArg (fun r : ℝ => C⁻¹ * r)
      (finiteProfile_eq_of_values J h _ (fun n _ => hm.phi n hw))
  rw [SlowExpansionResidual.slowVelocity_components, SlowExpansionResidual.slowVelocity_components,
    hv, hu, hf]

theorem prefixVelocity_germ {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : VelocityMatches h d f) (J : ℕ) (C : ℝ) {z : ProblemStatement.SpaceTime}
    (hz : z ∈ BaseResidual.annularPast) :
    BaseResidual.prefixVelocity J h C d =ᶠ[𝓝 z] SlowExpansionResidual.slowVelocity J h C f := by
  filter_upwards [BaseResidual.annularPast_isOpen.mem_nhds hz] with w hw
  exact prefixVelocity_eq_slowVelocity hh hh1 hd hm J C hw.1 w.2 hw.2


/-- The remaining agreements concern scalar pressure and the actual canonical
stress primitives.  No finite-field or residual identity is an input. -/
structure CoefficientMatches (h C : ℝ) (d : Coefficients)
    (f : SlowExpansionResidual.SlowProfiles) : Prop extends VelocityMatches h d f where
  pressure : ∀ n, EqOn (d.pressure n) (f.pressure n) profileWindow
  stressTheta : ∀ n, EqOn (d.stressTheta n) (SlowResidualMatching.thetaStress h C f n) profileWindow
  stressAxial : ∀ n, EqOn (d.stressAxial n) (SlowResidualMatching.zStress h f n) profileWindow

theorem coefficient_germ {f g : Inner → ℝ} (he : EqOn f g profileWindow)
    {w : Inner} (hw : w ∈ profileWindow) : f =ᶠ[𝓝 w] g := by
  filter_upwards [profileWindow_open.mem_nhds hw] with y hy
  exact he hy

theorem prefixProfile_germ_of_coefficients {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (J : ℕ) (b : ℝ) {f g : ℕ → Inner → ℝ}
    (he : ∀ n, EqOn (f n) (g n) profileWindow)
    {p : Chart} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    SlowBorelBase.physicalUncutPrefix h b f J =ᶠ[𝓝 p]
      SlowExpansionResidual.finiteProfile J h b g := by
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds ht,
    (isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).mem_nhds hs]
    with y hyt hys
  rw [SlowBorelBase.physicalUncutPrefix_eq_finiteProfile hh hh1 b f J hyt]
  exact finiteProfile_eq_of_values J h b (fun n _ => he n (inner_mem_profileWindow hh hh1 hyt hys))

theorem prefixPressure_germ {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} {f : SlowExpansionResidual.SlowProfiles}
    (hm : CoefficientMatches h C d f) (J : ℕ) {z : ProblemStatement.SpaceTime}
    (hz : z ∈ BaseResidual.annularPast) :
    BaseResidual.prefixPressure J h C d =ᶠ[𝓝 z] SlowExpansionResidual.slowPressureField J h f := by
  have he := prefixProfile_germ_of_coefficients hh hh1 J (-2 * CoordinateAlgebra.A h)
    (f := SlowBorelBase.bundleComponent C d 2) hm.pressure
    (p := AxisymmetricFields.profilePoint z.1 z.2) hz.1 hz.2
  exact he.comp_tendsto (AxisymmetricFields.contDiff_profilePoint (n := ∞)).continuous.continuousAt

theorem radialDivergence_congr_germ (k : ℝ) {f g : Chart → ℝ} {p : Chart}
    (he : f =ᶠ[𝓝 p] g) :
    LeadingStress.radialDivergence k f p = LeadingStress.radialDivergence k g p := by
  unfold LeadingStress.radialDivergence SimilarityProfile.partialS
  rw [he.eq_of_nhds, he.fderiv_eq]

theorem prefixStressForce_eq {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} {f : SlowExpansionResidual.SlowProfiles}
    (hm : CoefficientMatches h C d f) (J : ℕ) {z : ProblemStatement.SpaceTime}
    (hz : z ∈ BaseResidual.annularPast) :
    BaseResidual.prefixStressForce J h C d z =
      SlowResidualMatching.tangentialStressForce
        (SlowResidualMatching.physicalThetaStress J h C f)
        (SlowResidualMatching.physicalZStress J h f) z.1 z.2 := by
  have htheta := prefixProfile_germ_of_coefficients hh hh1 J (-CoordinateAlgebra.A h - 1 / 2)
    (f := SlowBorelBase.bundleComponent C d 3) hm.stressTheta
    (p := AxisymmetricFields.profilePoint z.1 z.2) hz.1 hz.2
  have haxial := prefixProfile_germ_of_coefficients hh hh1 J (-CoordinateAlgebra.A h - 1 / 2)
    (f := SlowBorelBase.bundleComponent C d 4) hm.stressAxial
    (p := AxisymmetricFields.profilePoint z.1 z.2) hz.1 hz.2
  change BaseResidual.prefixStressTheta J h C d =ᶠ[𝓝 (AxisymmetricFields.profilePoint z.1 z.2)]
    SlowResidualMatching.physicalThetaStress J h C f at htheta
  change BaseResidual.prefixStressAxial J h C d =ᶠ[𝓝 (AxisymmetricFields.profilePoint z.1 z.2)]
    SlowResidualMatching.physicalZStress J h f at haxial
  unfold BaseResidual.prefixStressForce BaseResidual.stressForce
    SlowResidualMatching.tangentialStressForce
  rw [radialDivergence_congr_germ 2 htheta, radialDivergence_congr_germ 1 haxial]

theorem VelocityMatches.phi_contDiffAt {h : ℝ} {d : Coefficients}
    (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : VelocityMatches h d f) (n : ℕ) {w : Inner} (hw : w ∈ profileWindow) :
    ContDiffAt ℝ ∞ (f.phi n) w :=
  (hd.phi n).contDiffAt.congr_of_eventuallyEq (coefficient_germ (hm.phi n) hw).symm

theorem VelocityMatches.axial_contDiffAt {h : ℝ} {d : Coefficients}
    (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : VelocityMatches h d f) (n : ℕ) {w : Inner} (hw : w ∈ profileWindow) :
    ContDiffAt ℝ ∞ (f.axial n) w :=
  (hd.axial n).contDiffAt.congr_of_eventuallyEq (coefficient_germ (hm.axial n) hw).symm

theorem VelocityMatches.flux_contDiffAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : VelocityMatches h d f) (n : ℕ) {w : Inner} (hw : w ∈ profileWindow) :
    ContDiffAt ℝ ∞ (f.flux n) w := by
  have hs : w.2 ^ 2 ≤ 1 := by
    have h1 := hw.2.1
    have h2 := hw.2.2
    nlinarith [mul_nonneg (show 0 ≤ 1 - w.2 by linarith) (show 0 ≤ 1 + w.2 by linarith)]
  have hL := (CoordinateAlgebra.L_pos hh.le hh1 hs).ne'
  exact (SlowDivergence.radialFlux_smoothAt SlowBorelBase.globalRadialDomain
    (hd.axial n).contDiffOn h (SlowExpansionResidual.slowOrder h n) (mem_univ _) hL).congr_of_eventuallyEq
      (coefficient_germ (hm.flux n) hw).symm

theorem CoefficientMatches.pressure_contDiffAt {h C : ℝ} {d : Coefficients}
    (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : CoefficientMatches h C d f) (n : ℕ) {w : Inner} (hw : w ∈ profileWindow) :
    ContDiffAt ℝ ∞ (f.pressure n) w :=
  (hd.pressure n).contDiffAt.congr_of_eventuallyEq (coefficient_germ (hm.pressure n) hw).symm

/-- The finite identity required by the Borel residual estimates, now derived
from the actual finite potentials and scalar recurrence data. -/
theorem finiteIdentities_of_coefficients {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : CoefficientMatches h C d f)
    (hTheta : ∀ n, SlowStressSupport.Smooth (Ioo (-1) 1) (SlowResidualMatching.thetaDensity h C f n))
    (hZ : ∀ n, SlowStressSupport.Smooth (Ioo (-1) 1) (SlowResidualMatching.zDensity h f n))
    (hp : ∀ n, ∀ w ∈ profileWindow, SlowExpansionResidual.pressureCoefficient h C f n w = 0) :
    BaseResidual.FiniteIdentities h C d f := by
  intro J z hz
  have hw := inner_mem_profileWindow hh hh1 (p := AxisymmetricFields.profilePoint z.1 z.2) hz.1 hz.2
  rw [ResidualRegularity.residual_congr (prefixVelocity_germ hh hh1 hd hm.toVelocityMatches J C hz)
    (prefixPressure_germ hh hh1 hm J hz), prefixStressForce_eq hh hh1 hm J hz]
  exact SlowResidualMatching.navierStokesResidual_eq_stress_add_truncation isOpen_Ioo hh hh1 J C f
    (fun n _ => hTheta n) (fun n _ => hZ n) hz.1 hz.2 hw.2
    (fun n _ => (hm.toVelocityMatches.flux_contDiffAt hh hh1 hd n hw).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (fun n _ => (hm.toVelocityMatches.phi_contDiffAt hd n hw).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (fun n _ => (hm.toVelocityMatches.axial_contDiffAt hd n hw).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (fun n _ => (hm.pressure_contDiffAt hd n hw).differentiableAt (by simp))
    (fun n _ => hp n _ hw)

end NavierStokes.BasePrefixIdentity
end


noncomputable section

open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace NavierStokes.ConstructedSlowBase

open GlobalSlowProfiles AssembledSlowBase SlowBorelBase

private theorem parameter_abs_le {eta : ℝ} (h : eta ∈ Ioo (-1 : ℝ) 1) :
    |eta| ≤ 1 := (abs_lt.mpr h).le

/-- Restricting the compact set preserves the very same cutoff schedule. -/
theorem admissibleScales_mono {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a : ℕ → ℕ} {h : ℝ} {f : ℕ → Inner → V} {K K' : Set Inner}
    (ha : AdmissibleScales h f K a) (hK : K' ⊆ K) : AdmissibleScales h f K' a where
  positive := ha.positive
  doubling := ha.doubling
  strictMono := ha.strictMono
  ordinary := fun j hj m hm q hq hq1 w hw => ha.ordinary j hj m hm q hq hq1 w (hK hw)
  blown := fun j hj m hm q hq hq1 w hw => ha.blown j hj m hm q hq hq1 w (hK hw)

/-- The genuine smooth vector potential of the summed base. -/
noncomputable def potential (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) :
    ProblemStatement.VelocityField :=
  AxisymmetricFields.potential (streamFactor a h C d) (swirlPotential a h C d)


theorem potential_smooth {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d) (C : ℝ) :
    ContDiffOn ℝ ∞ (potential a h C d) BaseResidual.past :=
  AxisymmetricFields.contDiffOn_potential
    (physicalProfile_smoothOn ha hh hh1 (bundleComponent_smooth hd C 0) _)
    (physicalProfile_smoothOn ha hh hh1 (bundleComponent_smooth hd C 1) _)

section RepairedFamily

variable {S : Set ℝ} {h C rho inner : ℝ} {U : Set ℂ}
  {base : Fin 5 → SimilarityProfile.InnerProfile} {s : Scheme S h C}
  {A : SlowRecursion.LocalHierarchy rho U h C base}
  (L : Localization s A inner) (B0 : BaseAgreement s A inner)
  (Z0 : ZeroOrderSolved s inner) (hI : Icc (-1 : ℝ) 1 ⊆ S)

/-- The only base flux premise is the actual mass reconstruction.  Every
positive-order flux is reconstructed by the global recursion itself. -/
theorem repaired_coefficientMatches
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial) :
    BasePrefixIdentity.CoefficientMatches h C (coefficients L B0 Z0 hI) (asSlowProfiles s) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro n w hw
    exact (coefficients_fields_eq L B0 Z0 hI n hw.1.le (parameter_abs_le hw.2)).1
  · intro n w hw
    exact (coefficients_fields_eq L B0 Z0 hI n hw.1.le (parameter_abs_le hw.2)).2.1
  · intro n w hw
    have hb : w.1 * extendedCoefficient s hI n 2 w =
        SlowDivergence.radialFlux h (SlowExpansionResidual.slowOrder h n)
          ((coefficients L B0 Z0 hI).axial n) w := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have he := extended_flux_zero s hI hbase hw.1.le (parameter_abs_le hw.2)
        simp only [SlowExpansionResidual.slowOrder, Nat.cast_zero, mul_zero, zero_mul] at he ⊢
        exact he
      · exact extended_flux s hI hn hw.1.le (parameter_abs_le hw.2)
    rw [← hb]
    change w.1 * extendedCoefficient s hI n 2 w = w.1 * xProfile (profiles s n).beta w
    rw [extendedCoefficient_eq s hI n 2 hw.1.le (parameter_abs_le hw.2)]
    rfl
  · intro n w hw
    exact (coefficients_fields_eq L B0 Z0 hI n hw.1.le (parameter_abs_le hw.2)).2.2
  · intro n w hw
    exact (coefficients_stress_eq L B0 Z0 hI n hw.1.le (parameter_abs_le hw.2)).1
  · intro n w hw
    exact (coefficients_stress_eq L B0 Z0 hI n hw.1.le (parameter_abs_le hw.2)).2

/-- The finite Cartesian PDE identity is derived from scalar equations and
the actual stream primitives, using the proved finite-prefix bridge. -/
theorem repaired_finiteIdentities (hh : 0 < h) (hh1 : h < 1 / 2)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial)
    (hp : ∀ n, ∀ w ∈ BasePrefixIdentity.profileWindow,
      SlowExpansionResidual.pressureCoefficient h C (asSlowProfiles s) n w = 0) :
    BaseResidual.FiniteIdentities h C (coefficients L B0 Z0 hI) (asSlowProfiles s) := by
  apply BasePrefixIdentity.finiteIdentities_of_coefficients hh hh1
    (coefficients_smooth L B0 Z0 hI) (repaired_coefficientMatches L B0 Z0 hI hbase)
  · intro n
    exact (thetaDensity_smooth L B0 Z0 n).mono
      (fun _ hw => ⟨hw.1, hI ⟨hw.2.1.le, hw.2.2.le⟩⟩)
  · intro n
    exact (zDensity_smooth L B0 Z0 n).mono
      (fun _ hw => ⟨hw.1, hI ⟨hw.2.1.le, hw.2.2.le⟩⟩)
  · exact hp

theorem repaired_stressZeroCore :
    BaseResidual.StressZeroCore (coefficients L B0 Z0 hI) (inner / 8) := by
  intro n X hX eta _
  exact coefficients_stress_zero_left L B0 Z0 hI n hX.2.le

/-- One open coefficient neighborhood contains the whole physical parameter
band and avoids the coordinate denominator's zeros. -/
noncomputable def regularDomain (s : Scheme S h C) (hI : Icc (-1 : ℝ) 1 ⊆ S) : Set Inner :=
  {w | |w.2| < (commonWindow s hI).inner ∧ CoordinateAlgebra.L h w.2 ≠ 0}

theorem regularDomain_open : IsOpen (regularDomain s hI) := by
  have hL : Continuous (fun w : Inner => CoordinateAlgebra.L h w.2) :=
    continuous_const.sub (continuous_const.mul (continuous_snd.pow 2))
  exact (isOpen_lt continuous_snd.abs continuous_const).inter
    (isOpen_ne_fun hL continuous_const)

theorem innerBox_subset_regularDomain (hh : 0 < h) (hh1 : h < 1 / 2) (lo hi : ℝ) :
    innerBox lo hi ⊆ regularDomain s hI := by
  intro w hw
  have he : |w.2| ≤ 1 := abs_le.mpr hw.2
  exact ⟨he.trans_lt (commonWindow s hI).one_lt_inner,
    (CoordinateAlgebra.L_pos hh.le hh1 ((sq_le_one_iff_abs_le_one w.2).mpr he)).ne'⟩

theorem regular_fields_eq (n : ℕ) {w : Inner} (hw : w ∈ regularDomain s hI) (hX : 0 ≤ w.1) :
    (asSlowProfiles s).phi n w = extendedCoefficient s hI n 0 w ∧
    (asSlowProfiles s).axial n w = extendedCoefficient s hI n 1 w ∧
    (asSlowProfiles s).flux n w = w.1 * extendedCoefficient s hI n 2 w := by
  refine ⟨?_, ?_, ?_⟩
  · exact (extendEven_eq (commonWindow s hI) (profiles s n).phi hX hw.1.le).symm
  · exact (extendEven_eq (commonWindow s hI) (profiles s n).axial hX hw.1.le).symm
  · exact congrArg (w.1 * ·)
      (extendEven_eq (commonWindow s hI) (profiles s n).beta hX hw.1.le).symm

/-- Every fixed physical derivative has every requested power of decay,
including on approaches that meet the symmetry axis. -/
theorem repaired_jetRate {l : Filter ProblemStatement.SpaceTime} {a : ℕ → ℕ} {hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (P : BaseResidual.PhysicalApproach l h 0 hi)
    (ha : AdmissibleScales h (coefficientBundle C (coefficients L B0 Z0 hI)) (innerBox 0 hi) a)
    (hf : BaseResidual.FiniteIdentities h C (coefficients L B0 Z0 hI) (asSlowProfiles s))
    (m : ℕ) (n : ℝ) (hn : 0 ≤ n) :
    DiagonalResidual.JetRate l (fun z => (cartesianChart h z).1)
      (BaseResidual.baseResidual a h C (coefficients L B0 Z0 hI)) m n := by
  exact BaseResidual.baseResidual_jetRate_axis hh hh1 P
    (div_pos L.inner_pos (by norm_num)) (coefficients_smooth L B0 Z0 hI)
    (repaired_stressZeroCore L B0 Z0 hI) ha (asSlowProfiles s) hf
    (regularDomain_open hI) (innerBox_subset_regularDomain hI hh hh1 0 hi)
    (fun j => extendedCoefficient s hI j 0) (fun j => extendedCoefficient s hI j 1)
    (fun j => extendedCoefficient s hI j 2)
    (fun j => (extendedCoefficient_contDiff s hI j 0).contDiffOn)
    (fun j => (extendedCoefficient_contDiff s hI j 1).contDiffOn)
    (fun j => (extendedCoefficient_contDiff s hI j 2).contDiffOn)
    (fun j _ hw hx => (regular_fields_eq hI j hw hx).2.2)
    (fun j _ hw hx => (regular_fields_eq hI j hw hx).2.1)
    (fun j _ hw hx => (regular_fields_eq hI j hw hx).1)
    (fun _ hw => hw.2) m n hn

theorem repaired_allJetsFlat {l : Filter ProblemStatement.SpaceTime} {a : ℕ → ℕ} {hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (P : BaseResidual.PhysicalApproach l h 0 hi)
    (ha : AdmissibleScales h (coefficientBundle C (coefficients L B0 Z0 hI)) (innerBox 0 hi) a)
    (hf : BaseResidual.FiniteIdentities h C (coefficients L B0 Z0 hI) (asSlowProfiles s)) :
    ResidualStability.AllJetsFlat l (fun z => (cartesianChart h z).1)
      (BaseResidual.baseResidual a h C (coefficients L B0 Z0 hI)) := by
  exact BaseResidual.baseResidual_allJetsFlat_axis hh hh1 P
    (div_pos L.inner_pos (by norm_num)) (coefficients_smooth L B0 Z0 hI)
    (repaired_stressZeroCore L B0 Z0 hI) ha (asSlowProfiles s) hf
    (regularDomain_open hI) (innerBox_subset_regularDomain hI hh hh1 0 hi)
    (fun j => extendedCoefficient s hI j 0) (fun j => extendedCoefficient s hI j 1)
    (fun j => extendedCoefficient s hI j 2)
    (fun j => (extendedCoefficient_contDiff s hI j 0).contDiffOn)
    (fun j => (extendedCoefficient_contDiff s hI j 1).contDiffOn)
    (fun j => (extendedCoefficient_contDiff s hI j 2).contDiffOn)
    (fun j _ hw hx => (regular_fields_eq hI j hw hx).2.2)
    (fun j _ hw hx => (regular_fields_eq hI j hw hx).2.1)
    (fun j _ hw hx => (regular_fields_eq hI j hw hx).1)
    (fun _ hw => hw.2)

/-- Exterior confinement is a consequence of the five repaired rows, not
an extra hypothesis on higher-order stress coefficients. -/
theorem repaired_higherInteriorSupport
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial)
    {left right : ℝ} (hl : Real.exp left < inner / 8) (hr : s.B ^ 2 / 2 < Real.exp right) :
    BaseResidual.HigherInteriorSupport (coefficients L B0 Z0 hI) left right := by
  intro n hn
  have he := GlobalStressSupport.raw_stresses_exterior s hbase hn
  have hs := coefficients_stress_support L B0 Z0 hI n s.B_pos.le he.1 he.2
  have hz {w : Inner} (hw : w.1 ∉ Icc (inner / 8) (s.B ^ 2 / 2)) :
      ((coefficients L B0 Z0 hI).stressTheta n w,
        (coefficients L B0 Z0 hI).stressAxial n w) = 0 := by
    by_contra hh
    exact hw (hs (subset_closure hh)).1
  refine ⟨inner / 8, s.B ^ 2 / 2, fun _ hw => ⟨hl.trans_le hw.1, hw.2.trans_lt hr⟩, ?_, ?_⟩
  · intro eta _ X hX
    exact congrArg Prod.fst (hz hX)
  · intro eta _ X hX
    exact congrArg Prod.snd (hz hX)

end RepairedFamily

section Nominal

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

include W

theorem height_pos : 0 < F.data.h := W.axis.small.h_pos

theorem height_lt_half : F.data.h < 1 / 2 := by linarith [W.axis.small.h_le]







/-- The leading coefficient retains the actual natural axis datum. -/
theorem nominal_leading_axis {eta : ℝ} (heta : eta ∈ Icc (-1 : ℝ) 1) :
    (nominalCoefficients W).axial 0 (0, eta) = 4 * eta + W.axis.j := by
  have h0 : (0 : ℝ) ≤ 4 / W.axis.scale := (div_pos (by norm_num) W.axis.scale_pos).le
  calc
    _ = W.U (0, eta) := (nominalCoefficients_zero_fields W (p := (0, eta)) le_rfl (abs_le.mpr heta)).2.1
    _ = W.controls.seedU (0, eta) :=
      (W.seed_agreement (p := (0, eta)) le_rfl NominalProfile.Xi_pos.le).2.1
    _ = W.axis.natural.profile.family.U (0, eta) := (W.controls.seed_initial h0).2
    _ = _ := W.axis.natural.profile.family.natural.U_axis eta
      (NaturalAxisCoefficients.original_interval_interior heta)










end Nominal

section Modified

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
  {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
  {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)

include M


theorem modified_finiteIdentities :
    BaseResidual.FiniteIdentities F.data.h W.axis.normalization
      (modifiedCoefficients W Q M) (asSlowProfiles (modifiedScheme W Q M)) := by
  apply repaired_finiteIdentities (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
    (modifiedZeroOrder W Q M) M.contains (height_pos W) (height_lt_half W) rfl
  intro n w hw
  exact modified_pressureCoefficient W Q M n hw.1 (M.contains ⟨hw.2.1.le, hw.2.2.le⟩)



theorem modified_allJetsFlat {l : Filter ProblemStatement.SpaceTime} {a : ℕ → ℕ} {upper : ℝ}
    (P : BaseResidual.PhysicalApproach l F.data.h 0 upper)
    (ha : AdmissibleScales F.data.h
      (coefficientBundle W.axis.normalization (modifiedCoefficients W Q M)) (innerBox 0 upper) a) :
    ResidualStability.AllJetsFlat l (fun z => (cartesianChart F.data.h z).1)
      (BaseResidual.baseResidual a F.data.h W.axis.normalization (modifiedCoefficients W Q M)) :=
  repaired_allJetsFlat (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
    (modifiedZeroOrder W Q M) M.contains (height_pos W) (height_lt_half W) P ha
    (modified_finiteIdentities W Q M)

theorem modified_higherInteriorSupport {left right : ℝ}
    (hl : Real.exp left < nominalInner W / 8) (hr : nominalOuterX W < Real.exp right) :
    BaseResidual.HigherInteriorSupport (modifiedCoefficients W Q M) left right := by
  apply repaired_higherInteriorSupport (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
    (modifiedZeroOrder W Q M) M.contains rfl hl
  change nominalOuterRadius W ^ 2 / 2 < Real.exp right
  rwa [nominalOuterRadius_square]

theorem modified_leading_axis {eta : ℝ} (heta : eta ∈ Icc (-1 : ℝ) 1) :
    (modifiedCoefficients W Q M).axial 0 (0, eta) = 4 * eta + W.axis.j := by
  calc
    _ = Q.U (0, eta) := (modifiedCoefficients_zero_fields W Q M (p := (0, eta)) le_rfl (abs_le.mpr heta)).2.1
    _ = W.U (0, eta) := (M.fields (0, eta) le_rfl (M.contains heta)
      (Or.inl ((nominalInner_pos W).le.trans M.inner))).2
    _ = (nominalCoefficients W).axial 0 (0, eta) :=
      (nominalCoefficients_zero_fields W (p := (0, eta)) le_rfl (abs_le.mpr heta)).2.1.symm
    _ = _ := nominal_leading_axis W heta

theorem modified_leading_origin : (modifiedCoefficients W Q M).axial 0 (0, 0) = W.axis.j := by
  simpa using modified_leading_axis W Q M (eta := 0) (by constructor <;> norm_num)

theorem modified_origin {a : ℕ → ℕ} (ha : StrictMono a) {t : ℝ} (ht : t < 1) :
    baseVelocity a F.data.h W.axis.normalization (modifiedCoefficients W Q M) (t, 0) =
      ((1 - t) ^ (-CoordinateAlgebra.A F.data.h) * W.axis.j) •
        ProblemStatement.coordinateVector 2 := by
  rw [BaseResidual.baseVelocity_at_origin ha (height_pos W) (height_lt_half W)
    (modifiedCoefficients_smooth W Q M) W.axis.normalization
    (fun _ hn => (modifiedCoefficients_axis W Q M hn (by norm_num : |(0 : ℝ)| ≤ 1)).2.1) ht,
    modified_leading_origin]

theorem modified_axis_tendsto {a : ℕ → ℕ} (ha : StrictMono a) :
    Tendsto (fun t : ℝ =>
      ‖baseVelocity a F.data.h W.axis.normalization (modifiedCoefficients W Q M) (t, 0)‖)
      (𝓝[<] 1) atTop := by
  apply BaseResidual.baseVelocity_axis_tendsto_atTop ha (height_pos W) (height_lt_half W)
    (modifiedCoefficients_smooth W Q M) W.axis.normalization
    (fun _ hn => (modifiedCoefficients_axis W Q M hn (by norm_num : |(0 : ℝ)| ≤ 1)).2.1)
  rw [modified_leading_origin]
  exact W.axis.small.j_pos

theorem modified_speedUnbounded {a : ℕ → ℕ} (ha : StrictMono a) :
    ProblemStatement.SpeedUnboundedAtOne
      (baseVelocity a F.data.h W.axis.normalization (modifiedCoefficients W Q M)) :=
  NaturalCore.speedUnbounded_of_axis_tendsto (modified_axis_tendsto W Q M ha)

end Modified

section CommonWeightedSchedule

open BaseResidual ActiveAnnulusWeight

/-- The actual two-slot, all-order weighted estimate, used only as an output
of the coefficient construction and common schedule selection. -/
def WeightedStressBound (a : ℕ → ℕ) (h : ℝ) (d : Coefficients) (c left right : ℝ) : Prop :=
  ∀ m : ℕ, ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ q : ℝ, 0 < q → q ≤ 1 →
    ∀ w ∈ activeWindow left right,
      ‖blownJet m (fun v => normalizedTensor a h d v - stressPair d 0 v.2) (q, w)‖ ≤
        D * q ^ h * activeZeta c left right w * (activeDelta left right w)⁻¹ ^ N

/-- This form uses actual derivative bounds on the closed parameter band.
It requires no ambient germ equality to an auxiliary extension at eta=±1. -/
theorem weighted_on_actual_scales {a : ℕ → ℕ} {h C : ℝ} (hh : 0 < h)
    {d : Coefficients} (hd : SmoothCoefficients d) {c left right inner cut : ℝ}
    (hc : 0 < c) (hl : Real.exp left < inner) (hi : inner ≤ cut) (hr : cut < Real.exp right)
    (hs : HigherInteriorSupport d left right)
    (hz : ∀ w : Inner, w.1 < inner → stressPair d 1 w = 0)
    (ho : PolynomialEdgeJets (outerWindow cut right) (activeZeta c left right)
      (activeDelta left right) (stressPair d 1))
    {K : Set Inner} (hK : IsCompact K) (hWK : activeWindow left right ⊆ K)
    (ha : AdmissibleScales h (weightedBundle C d (activeZeta c left right)) K a) :
    WeightedStressBound a h d c left right := by
  let O : Set Inner := Ioo (Real.exp left) (Real.exp right) ×ˢ univ
  have hO : IsOpen O := isOpen_Ioo.prod isOpen_univ
  have hWO : activeWindow left right ⊆ O := fun _ hw => ⟨hw.1, mem_univ _⟩
  exact normalizedTensor_weighted_bound hh hd hK hWK hO hWO
    (activeZeta_smooth hc left right) (fun _ hw => radialWeight_pos hw.1)
    (fun _ hw => activeDelta_bounds hw)
    (edgeJets_of_outer_collar (stressPair_smooth hd 1) hc hl hi hr hz ho)
    (activeZeta_edgeJets (Real.exp_lt_exp.mp ((hl.trans_le hi).trans hr)) hc)
    (higherStressQuotient_smooth_of_support hd hc hs) ha



end CommonWeightedSchedule

section FixedGeometry

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

noncomputable def activeLeft : ℝ := Real.log (nominalInner W / 16)

noncomputable def terminalShift : ℝ := TerminalHistoryBridge.shift F W.controls.radius

noncomputable def activeRight : ℝ := terminalShift W + 3

noncomputable def activeUpper : ℝ := Real.exp (activeRight W)

noncomputable def scaleUpper (upper : ℝ) : ℝ := max upper (activeUpper W)

theorem exp_activeLeft : Real.exp (activeLeft W) = nominalInner W / 16 :=
  Real.exp_log (div_pos (nominalInner_pos W) (by norm_num))

theorem activeLeft_margin : Real.exp (activeLeft W) < nominalInner W / 8 := by
  rw [exp_activeLeft]
  linarith [nominalInner_pos W]

theorem core_before_outer : nominalInner W / 8 < nominalOuterX W := by
  have hi := (nominalInner_lt_stop W).trans (nominalStop_lt_initial W)
  have ho := (W.controls.Xi_lt_heatJoin W.separated).trans
    (W.controls.heatJoin_lt_radius.trans (nominalOuterX_gt_radius W))
  have hxi := nominalInitial_le_Xi W
  linarith [nominalInner_pos W]

theorem switch_before_collar : BaseExterior.nominalHeatSwitch W < Real.exp (terminalShift W + 2) := by
  change BaseExterior.nominalHeatSwitch W <
    Real.exp (Real.log (BaseExterior.nominalHeatSwitch W) - 1 / 5 + 2)
  calc
    _ = Real.exp (Real.log (BaseExterior.nominalHeatSwitch W)) :=
      (Real.exp_log (BaseExterior.nominalHeatSwitch_pos W)).symm
    _ < _ := Real.exp_lt_exp.mpr (by linarith)

theorem outer_before_collar : nominalOuterX W < Real.exp (terminalShift W + 2) :=
  (nominalOuterX_lt_switch W).trans (switch_before_collar W)

theorem collar_before_upper : Real.exp (terminalShift W + 2) < activeUpper W :=
  Real.exp_lt_exp.mpr (by dsimp [activeUpper, activeRight]; linarith)

theorem outer_before_upper : nominalOuterX W < activeUpper W :=
  (outer_before_collar W).trans (collar_before_upper W)

theorem core_before_collar : nominalInner W / 8 ≤ Real.exp (terminalShift W + 3 - 1) := by
  have hh := (core_before_outer W).trans (outer_before_collar W)
  simpa only [show terminalShift W + 3 - 1 = terminalShift W + 2 by ring] using hh.le

theorem activeLeft_before_collar : activeLeft W < terminalShift W + 2 :=
  Real.exp_lt_exp.mp ((activeLeft_margin W).trans
    ((core_before_outer W).trans (outer_before_collar W)))



theorem activeWindow_subset_box (upper : ℝ) :
    BaseResidual.activeWindow (activeLeft W) (activeRight W) ⊆ innerBox 0 (scaleUpper W upper) := by
  intro w hw
  exact ⟨⟨(Real.exp_pos _).le.trans hw.1.1.le,
    hw.1.2.le.trans (le_max_right upper (activeUpper W))⟩, hw.2⟩



theorem modified_higher_support {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
    {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi) :
    BaseResidual.HigherInteriorSupport (modifiedCoefficients W Q M) (activeLeft W) (activeRight W) :=
  modified_higherInteriorSupport W Q M (activeLeft_margin W) (outer_before_upper W)

theorem modified_quotients_smooth {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
    {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi) {c : ℝ} (hc : 0 < c) (j : ℕ) :
    ContDiff ℝ ∞ (BaseResidual.higherStressQuotient (modifiedCoefficients W Q M)
      (BaseResidual.activeZeta c (activeLeft W) (activeRight W)) j) :=
  BaseResidual.higherStressQuotient_smooth_of_support (modifiedCoefficients_smooth W Q M) hc
    (modified_higher_support W Q M) j

end FixedGeometry

section SelectedSchedules

open BaseResidual

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
  (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ)














variable {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
  {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)

/-- The modified family gets one schedule, derived from its actual repaired
coefficients. No stress estimate enters this definition. -/
noncomputable def modifiedScales : ℕ → ℕ :=
  Classical.choose (exists_admissibleScales
    (weightedBundle_smooth (modifiedCoefficients_smooth W Q M) (modified_quotients_smooth W Q M hc)
      W.axis.normalization) (height_pos W) (innerBox_isCompact 0 (scaleUpper W upper)) B)

theorem modifiedScales_spec : B ≤ modifiedScales W c hc upper B Q M 0 ∧
    AdmissibleScales F.data.h
      (weightedBundle W.axis.normalization (modifiedCoefficients W Q M)
        (activeZeta c (activeLeft W) (activeRight W)))
      (innerBox 0 (scaleUpper W upper)) (modifiedScales W c hc upper B Q M) :=
  Classical.choose_spec (exists_admissibleScales
    (weightedBundle_smooth (modifiedCoefficients_smooth W Q M) (modified_quotients_smooth W Q M hc)
      W.axis.normalization) (height_pos W) (innerBox_isCompact 0 (scaleUpper W upper)) B)

theorem modifiedScales_admissible :
    AdmissibleScales F.data.h (coefficientBundle W.axis.normalization (modifiedCoefficients W Q M))
      (innerBox 0 (scaleUpper W upper)) (modifiedScales W c hc upper B Q M) :=
  weightedBundle_base_scales (modifiedCoefficients_smooth W Q M) (modified_quotients_smooth W Q M hc)
    (modifiedScales_spec W c hc upper B Q M).2

theorem modifiedScales_strictMono : StrictMono (modifiedScales W c hc upper B Q M) :=
  (modifiedScales_spec W c hc upper B Q M).2.strictMono

theorem modifiedScales_allJetsFlat {l : Filter ProblemStatement.SpaceTime} {radius : ℝ}
    (P : PhysicalApproach l F.data.h 0 radius) (hr : radius ≤ scaleUpper W upper) :
    ResidualStability.AllJetsFlat l (fun z => (cartesianChart F.data.h z).1)
      (baseResidual (modifiedScales W c hc upper B Q M) F.data.h W.axis.normalization
        (modifiedCoefficients W Q M)) :=
  modified_allJetsFlat W Q M P (admissibleScales_mono (modifiedScales_admissible W c hc upper B Q M)
    (fun _ hw => ⟨⟨hw.1.1, hw.1.2.trans hr⟩, hw.2⟩))

theorem modifiedScales_origin {t : ℝ} (ht : t < 1) :
    baseVelocity (modifiedScales W c hc upper B Q M) F.data.h W.axis.normalization
      (modifiedCoefficients W Q M) (t, 0) =
      ((1 - t) ^ (-CoordinateAlgebra.A F.data.h) * W.axis.j) •
        ProblemStatement.coordinateVector 2 :=
  modified_origin W Q M (modifiedScales_strictMono W c hc upper B Q M) ht

theorem modifiedScales_speedUnbounded :
    ProblemStatement.SpeedUnboundedAtOne
      (baseVelocity (modifiedScales W c hc upper B Q M) F.data.h W.axis.normalization
        (modifiedCoefficients W Q M)) :=
  modified_speedUnbounded W Q M (modifiedScales_strictMono W c hc upper B Q M)


theorem modifiedScales_potential_smooth :
    ContDiffOn ℝ ∞
      (potential (modifiedScales W c hc upper B Q M) F.data.h W.axis.normalization
        (modifiedCoefficients W Q M)) past :=
  potential_smooth (modifiedScales_strictMono W c hc upper B Q M) (height_pos W) (height_lt_half W)
    (modifiedCoefficients_smooth W Q M) W.axis.normalization

end SelectedSchedules

section ActualWeightedStress

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
  (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ)


variable {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
  {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)

/-- A finite modification additionally retains its literal angular history.
This fixes the first-order integration constant; the actual modulation
witness proves this equality from its five restored rows. -/
theorem modifiedScales_weighted_bound
    (hI : ∀ eta ∈ S, Q.I (nominalOuterX W, eta) = W.profiles.I (nominalOuterX W, eta)) :
    WeightedStressBound (modifiedScales W c hc upper B Q M) F.data.h (modifiedCoefficients W Q M)
      c (activeLeft W) (activeRight W) := by
  refine weighted_on_actual_scales (height_pos W) (modifiedCoefficients_smooth W Q M) hc
    (activeLeft_margin W) (core_before_collar W) ?_ (modified_higher_support W Q M) ?_
    (FirstOrderBaseEdge.modified_first_edgeJets W Q M hI hc (activeLeft_before_collar W))
    (innerBox_isCompact 0 (scaleUpper W upper)) (activeWindow_subset_box W upper)
    (modifiedScales_spec W c hc upper B Q M).2
  · apply Real.exp_lt_exp.mpr
    change terminalShift W + 3 - 1 < terminalShift W + 3
    linarith
  · intro w hw
    have hz := coefficients_stress_zero_left (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
      (modifiedZeroOrder W Q M) M.contains 1 hw.le
    exact Prod.ext hz.1 hz.2

end ActualWeightedStress

namespace Modulated

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  {ld : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness ld)

/-- The coefficients are rebuilt from this particular solved finite
modulation, using its preserved histories and its original nominal witness. -/
noncomputable def coefficients : Coefficients :=
  modifiedCoefficients W v.profiles v.finiteModification

theorem coefficients_smooth : SmoothCoefficients (coefficients v) :=
  modifiedCoefficients_smooth W v.profiles v.finiteModification

noncomputable def scales (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) : ℕ → ℕ :=
  modifiedScales W c hc upper B v.profiles v.finiteModification

theorem scales_spec (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    B ≤ scales v c hc upper B 0 ∧
    AdmissibleScales F.data.h
      (BaseResidual.weightedBundle W.axis.normalization (coefficients v)
        (BaseResidual.activeZeta c (activeLeft W) (activeRight W)))
      (innerBox 0 (scaleUpper W upper)) (scales v c hc upper B) :=
  modifiedScales_spec W c hc upper B v.profiles v.finiteModification

theorem scales_admissible (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    AdmissibleScales F.data.h (coefficientBundle W.axis.normalization (coefficients v))
      (innerBox 0 (scaleUpper W upper)) (scales v c hc upper B) :=
  modifiedScales_admissible W c hc upper B v.profiles v.finiteModification

theorem scales_strictMono (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    StrictMono (scales v c hc upper B) := (scales_spec v c hc upper B).2.strictMono

noncomputable def velocity (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.VelocityField :=
  baseVelocity (scales v c hc upper B) F.data.h W.axis.normalization (coefficients v)

noncomputable def pressure (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.PressureField :=
  basePressure (scales v c hc upper B) F.data.h W.axis.normalization (coefficients v)

noncomputable def stressForce (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.SpaceTime → ProblemStatement.Space :=
  BaseResidual.baseStressForce (scales v c hc upper B) F.data.h W.axis.normalization (coefficients v)

noncomputable def error (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.SpaceTime → ProblemStatement.Space :=
  BaseResidual.baseResidual (scales v c hc upper B) F.data.h W.axis.normalization (coefficients v)

noncomputable def vectorPotential (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.VelocityField :=
  potential (scales v c hc upper B) F.data.h W.axis.normalization (coefficients v)

theorem velocity_eq_curl (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    velocity v c hc upper B = SpatialCurl.spatialCurl (vectorPotential v c hc upper B) := rfl

theorem vectorPotential_smooth (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ContDiffOn ℝ ∞ (vectorPotential v c hc upper B) BaseResidual.past :=
  modifiedScales_potential_smooth W c hc upper B v.profiles v.finiteModification


theorem origin (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) {t : ℝ} (ht : t < 1) :
    velocity v c hc upper B (t, 0) =
      ((1 - t) ^ (-CoordinateAlgebra.A F.data.h) * W.axis.j) • ProblemStatement.coordinateVector 2 :=
  modifiedScales_origin W c hc upper B v.profiles v.finiteModification ht

theorem speedUnbounded (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.SpeedUnboundedAtOne (velocity v c hc upper B) :=
  modifiedScales_speedUnbounded W c hc upper B v.profiles v.finiteModification

theorem finiteIdentities :
    BaseResidual.FiniteIdentities F.data.h W.axis.normalization (coefficients v)
      (asSlowProfiles (modifiedScheme W v.profiles v.finiteModification)) :=
  modified_finiteIdentities W v.profiles v.finiteModification

theorem residual_identity (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) (z : ProblemStatement.SpaceTime) :
    ProblemStatement.navierStokesResidual (velocity v c hc upper B) (pressure v c hc upper B) z.1 z.2 =
      stressForce v c hc upper B z + error v c hc upper B z :=
  BaseResidual.baseResidual_identity _ _ _ _ z

theorem error_allJetsFlat (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ)
    {l : Filter ProblemStatement.SpaceTime} {radius : ℝ}
    (P : BaseResidual.PhysicalApproach l F.data.h 0 radius) (hr : radius ≤ scaleUpper W upper) :
    ResidualStability.AllJetsFlat l (fun z => (cartesianChart F.data.h z).1) (error v c hc upper B) :=
  modifiedScales_allJetsFlat W c hc upper B v.profiles v.finiteModification P hr

/-- Every finite identity and support input of this weighted estimate is
proved for the same actual modulation witness. -/
theorem weighted_bound (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    WeightedStressBound (scales v c hc upper B) F.data.h (coefficients v)
      c (activeLeft W) (activeRight W) :=
  modifiedScales_weighted_bound W c hc upper B v.profiles v.finiteModification
    (fun _ heta => v.slow_outer_angular heta)

end Modulated


end NavierStokes.ConstructedSlowBase

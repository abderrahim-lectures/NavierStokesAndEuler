import NavierStokes.R3.PressureRecoveryHelpers
import NavierStokes.R3.PressureFunctionals
import NavierStokes.R3.ComparisonTimeAverages
import NavierStokes.R3.CompactTimeIntegral
import NavierStokes.R3.ComparisonCutoffs
import Mathlib.Analysis.Normed.Group.ZeroAtInfty
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos
import NavierStokes.R3.FourierTestDerivatives
import NavierStokes.R3.FourierSobolevWeights
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import NavierStokes.R3.WeakFourierUniqueness
import NavierStokes.R3.SchwartzCompactApproximation
import NavierStokes.R3.RieszTestOperators
import NavierStokes.R3.RieszLinearityDecay

/-!
# Pressure recovery for smooth finite-energy comparisons

The physical pressure is tested only against compact smooth functions. Its
canonical representative is recovered from the conservative equation, time
averaging, and the vanishing theorem for harmonic Sobolev-bounded functionals.
-/
/-! Merged from `NavierStokes.R3.WeakTimeContinuity` (in a section, so its `open`s cannot leak). -/
section
/-!
# Weak time continuity from uniform spatial `L¹` bounds

A jointly continuous scalar field with uniformly bounded spatial `L¹` norm
has continuous pairings with every continuous test vanishing at infinity.
Only the test is approximated by compactly supported functions; no support or
derivative bound is imposed on the field.
-/


noncomputable section

open Set Filter MeasureTheory
open scoped Topology ZeroAtInfty

namespace NavierStokesR3.WeakTimeContinuity

open ProblemStatement ComparisonCutoffs

/-- A test function vanishing at infinity is bounded. -/
theorem exists_test_bound {ψ : Space → ℂ} (hψ : Continuous ψ)
    (hψzero : Tendsto ψ (cocompact Space) (𝓝 0)) :
    ∃ C : ℝ, ∀ x : Space, ‖ψ x‖ ≤ C := by
  let ψ₀ : C₀(Space, ℂ) :=
    { toFun := ψ, continuous_toFun := hψ, zero_at_infty' := hψzero }
  obtain ⟨C, hC⟩ := ψ₀.isBounded_range.exists_norm_le
  exact ⟨C, fun x => hC (ψ x) ⟨x, rfl⟩⟩

/-- Pairing an `L¹` scalar field with a bounded continuous complex test is
integrable. -/
theorem integrable_pairing_of_bounded {f : Space → ℝ} (hf : Integrable f volume)
    {ψ : Space → ℂ} (hψ : Continuous ψ) (hbound : ∃ C : ℝ, ∀ x, ‖ψ x‖ ≤ C) :
    Integrable (fun x : Space => (f x : ℂ) * ψ x) volume := by
  have hfC : Integrable (fun x : Space => (f x : ℂ)) volume := hf.ofReal
  obtain ⟨C, hC⟩ := hbound
  simpa only [mul_comm] using! hfC.bdd_mul hψ.aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- The original, untruncated pairing is a genuine Bochner integral. -/
theorem integrable_pairing {f : Space → ℝ} (hf : Integrable f volume)
    {ψ : Space → ℂ} (hψ : Continuous ψ)
    (hψzero : Tendsto ψ (cocompact Space) (𝓝 0)) :
    Integrable (fun x : Space => (f x : ℂ) * ψ x) volume :=
  integrable_pairing_of_bounded hf hψ (exists_test_bound hψ hψzero)

/-- The compact approximation to the spatial test. -/
def cutoffTest (R : ℝ) (ψ : Space → ℂ) (x : Space) : ℂ :=
  (cutoff R x : ℂ) * ψ x

theorem cutoffTest_continuous {ψ : Space → ℂ} (hψ : Continuous ψ) (R : ℝ) :
    Continuous (cutoffTest R ψ) :=
  (Complex.continuous_ofReal.comp (cutoff_smooth R).continuous).mul hψ

theorem norm_cutoffTest_le (R : ℝ) (ψ : Space → ℂ) (x : Space) :
    ‖cutoffTest R ψ x‖ ≤ ‖ψ x‖ := by
  simp only [cutoffTest, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (cutoff_nonneg R x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one R x)

theorem integrable_cutoff_pairing {f : Space → ℝ} (hf : Integrable f volume)
    {ψ : Space → ℂ} (hψ : Continuous ψ)
    (hψzero : Tendsto ψ (cocompact Space) (𝓝 0)) (R : ℝ) :
    Integrable (fun x : Space => (f x : ℂ) * cutoffTest R ψ x) volume := by
  obtain ⟨C, hC⟩ := exists_test_bound hψ hψzero
  exact integrable_pairing_of_bounded hf (cutoffTest_continuous hψ R)
    ⟨C, fun x => (norm_cutoffTest_le R ψ x).trans (hC x)⟩

/-- Cutting off the test cannot enlarge its pointwise error beyond its norm. -/
theorem norm_sub_cutoffTest_le (R : ℝ) (ψ : Space → ℂ) (x : Space) :
    ‖ψ x - cutoffTest R ψ x‖ ≤ ‖ψ x‖ := by
  have heq : ψ x - cutoffTest R ψ x = ((1 - cutoff R x : ℝ) : ℂ) * ψ x := by
    simp only [cutoffTest, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (cutoff_le_one R x))]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [cutoff_nonneg R x])

/-- The compact approximations converge uniformly on all of space. -/
theorem tendstoUniformly_cutoffTest {ψ : Space → ℂ} (hψ : Continuous ψ)
    (hψzero : Tendsto ψ (cocompact Space) (𝓝 0)) :
    TendstoUniformly (fun R : ℝ => cutoffTest R ψ) ψ atTop := by
  let ψ₀ : C₀(Space, ℂ) :=
    { toFun := ψ, continuous_toFun := hψ, zero_at_infty' := hψzero }
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  obtain ⟨A, hA⟩ := ZeroAtInftyContinuousMapClass.norm_le ψ₀ ε hε
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop A] with R hR hAR
  intro x
  rw [dist_eq_norm]
  by_cases hx : ‖x‖ ≤ R
  · simp only [cutoffTest, cutoff_eq_one hR hx, Complex.ofReal_one, one_mul,
      sub_self, norm_zero]
    exact hε
  · exact (norm_sub_cutoffTest_le R ψ x).trans_lt
      (hA x (lt_of_le_of_lt hAR (lt_of_not_ge hx)))

/-- Uniform error in the test controls error in its pairing by the `L¹`
norm of the scalar field. -/
theorem norm_pairing_sub_le {f : Space → ℝ} (hf : Integrable f volume)
    {ψ φ : Space → ℂ}
    (hψ : Integrable (fun x : Space => (f x : ℂ) * ψ x) volume)
    (hφ : Integrable (fun x : Space => (f x : ℂ) * φ x) volume)
    {ε : ℝ} (herror : ∀ x : Space, ‖ψ x - φ x‖ ≤ ε) :
    ‖(∫ x : Space, (f x : ℂ) * ψ x) - (∫ x : Space, (f x : ℂ) * φ x)‖ ≤
      ε * ∫ x : Space, ‖f x‖ := by
  rw [← integral_sub hψ hφ]
  calc
    ‖∫ x : Space, (f x : ℂ) * ψ x - (f x : ℂ) * φ x‖
        ≤ ∫ x : Space, ε * ‖f x‖ := by
      apply norm_integral_le_of_norm_le (hf.norm.const_mul ε)
      apply ae_of_all
      intro x
      rw [← mul_sub, norm_mul, Complex.norm_real]
      exact (mul_le_mul_of_nonneg_left (herror x) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = ε * ∫ x : Space, ‖f x‖ := integral_const_mul _ _

/-- Compactly truncated pairings are continuous on an arbitrary time set. -/
theorem continuousOn_cutoff_pairing {s : Set ℝ} {g : SpaceTime → ℝ}
    (hg : ContinuousOn g (s ×ˢ univ)) {ψ : Space → ℂ} (hψ : Continuous ψ)
    {R : ℝ} (hR : 0 < R) :
    ContinuousOn (fun t => ∫ x : Space, (g (t, x) : ℂ) * cutoffTest R ψ x) s := by
  apply CompactTimeIntegral.continuousOn_integral
    (F := fun z : SpaceTime => (g z : ℂ) * cutoffTest R ψ z.2)
    (isCompact_closedBall (0 : Space) (2 * R))
  · exact (Complex.continuous_ofReal.comp_continuousOn hg).mul
      ((cutoffTest_continuous hψ R).comp continuous_snd).continuousOn
  · intro t _ x hx
    have hxnorm : 2 * R ≤ ‖x‖ := by
      have : ¬ ‖x‖ ≤ 2 * R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
      exact (lt_of_not_ge this).le
    simp only [cutoffTest, cutoff_eq_zero hR hxnorm, Complex.ofReal_zero, zero_mul, mul_zero]

/-- Uniform spatial `L¹` bounds upgrade compact-test continuity to continuity
for every continuous test vanishing at infinity. -/
theorem continuousOn_pairing {s : Set ℝ} {g : SpaceTime → ℝ} {M : ℝ}
    (hg : ContinuousOn g (s ×ˢ univ))
    (hints : ∀ t ∈ s, Integrable (fun x : Space => g (t, x)) volume)
    (hbound : ∀ t ∈ s, (∫ x : Space, ‖g (t, x)‖) ≤ M)
    {ψ : Space → ℂ} (hψ : Continuous ψ)
    (hψzero : Tendsto ψ (cocompact Space) (𝓝 0)) :
    ContinuousOn (fun t => ∫ x : Space, (g (t, x) : ℂ) * ψ x) s := by
  have happrox := tendstoUniformly_cutoffTest hψ hψzero
  have hpair : TendstoUniformlyOn
      (fun R : ℝ => fun t => ∫ x : Space, (g (t, x) : ℂ) * cutoffTest R ψ x)
      (fun t => ∫ x : Space, (g (t, x) : ℂ) * ψ x) atTop s := by
    apply Metric.tendstoUniformlyOn_iff.2
    intro ε hε
    have hden : 0 < max M 0 + 1 := by positivity
    have hδ : 0 < ε / (max M 0 + 1) := div_pos hε hden
    filter_upwards [Metric.tendstoUniformly_iff.1 happrox (ε / (max M 0 + 1)) hδ]
      with R hR
    intro t ht
    have herror := norm_pairing_sub_le (hints t ht)
      (integrable_pairing (hints t ht) hψ hψzero)
      (integrable_cutoff_pairing (hints t ht) hψ hψzero R)
      (fun x => (show ‖ψ x - cutoffTest R ψ x‖ < ε / (max M 0 + 1) by
        simpa only [dist_eq_norm] using hR x).le)
    calc
      dist (∫ x : Space, (g (t, x) : ℂ) * ψ x)
          (∫ x : Space, (g (t, x) : ℂ) * cutoffTest R ψ x)
          ≤ ε / (max M 0 + 1) * ∫ x : Space, ‖g (t, x)‖ := by
        simpa only [dist_eq_norm] using herror
      _ ≤ ε / (max M 0 + 1) * max M 0 :=
        mul_le_mul_of_nonneg_left ((hbound t ht).trans (le_max_left _ _)) hδ.le
      _ < ε / (max M 0 + 1) * (max M 0 + 1) :=
        mul_lt_mul_of_pos_left (lt_add_one _) hδ
      _ = ε := div_mul_cancel₀ ε hden.ne'
  exact hpair.continuousOn ((eventually_gt_atTop (0 : ℝ)).mono
    (fun _ hR => continuousOn_cutoff_pairing hg hψ hR)).frequently

end NavierStokesR3.WeakTimeContinuity
end

/-! Merged from `NavierStokes.R3.HarmonicTestFunctionals` (in a section, so its `open`s cannot leak). -/
section
/-!
# Harmonic functionals bounded in an inhomogeneous Fourier Sobolev norm

A complex-linear Schwartz functional bounded by the Fourier `H³` norm is
represented in polynomially weighted `L²`. If it annihilates Laplacians, its
representing function vanishes away from the origin. Since volume has no atom
at the origin, the whole functional vanishes.
-/

/-! Merged from `NavierStokes.R3.HilbertFunctionalExtension`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# Hilbert-space representation of a functional bounded through an embedding

A linear functional on a complex vector space that is bounded in the norm of an
injective linear map into a Hilbert space is represented by an inner product in
that Hilbert space. No topology on the source vector space is needed.
-/

namespace NavierStokesR3.HilbertFunctionalExtension

universe u v

variable {E : Type u} [AddCommGroup E] [Module ℂ E]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Transfer a functional to the range of an injective linear map, extend it by
Hahn–Banach, and represent the extension by the Hilbert-space inner product. -/
theorem exists_inner_representation (B : E →ₗ[ℂ] H)
    (hB : Function.Injective B) (F : E →ₗ[ℂ] ℂ) {C : ℝ}
    (hbound : ∀ x : E, ‖F x‖ ≤ C * ‖B x‖) :
    ∃ q : H, ∀ x : E, F x = @inner ℂ H _ q (B x) := by
  classical
  let e : E ≃ₗ[ℂ] LinearMap.range B := LinearEquiv.ofInjective B hB
  let f : LinearMap.range B →ₗ[ℂ] ℂ := F.comp e.symm.toLinearMap
  have he (z : LinearMap.range B) : B (e.symm z) = (z : H) := by
    change ((e (e.symm z) : LinearMap.range B) : H) = (z : H)
    rw [e.apply_symm_apply]
  have hf : ∀ z : LinearMap.range B, ‖f z‖ ≤ C * ‖z‖ := by
    intro z
    change ‖F (e.symm z)‖ ≤ C * ‖(z : H)‖
    simpa only [he] using hbound (e.symm z)
  let fc : LinearMap.range B →L[ℂ] ℂ := f.mkContinuous C hf
  obtain ⟨G, hG, _⟩ := exists_extension_norm_eq (LinearMap.range B) fc
  refine ⟨(InnerProductSpace.toDual ℂ H).symm G, ?_⟩
  intro x
  rw [InnerProductSpace.toDual_symm_apply]
  calc
    F x = fc (e x) := by simp [fc, f]
    _ = G ((e x : LinearMap.range B) : H) := (hG (e x)).symm
    _ = G (B x) := rfl

end NavierStokesR3.HilbertFunctionalExtension


end



noncomputable section

open MeasureTheory

namespace NavierStokesR3.HarmonicTestFunctionals

open ProblemStatement Comparison

abbrev FrequencyL2 := Lp ℂ 2 (volume : Measure Space)

/-- The `H³` bound supplies a Hilbert-space representative after a polynomial
Fourier embedding. No Fourier transform of arbitrary `L²` functions is needed. -/
theorem exists_inner_representation_of_fourierHNormSq_bound
    (F : ComplexTest →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ψ : ComplexTest, ‖F ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ)) :
    ∃ q : FrequencyL2, ∀ ψ : ComplexTest,
      F ψ = @inner ℂ FrequencyL2 _ q (FourierSobolevWeights.B ψ) := by
  apply HilbertFunctionalExtension.exists_inner_representation
    FourierSobolevWeights.B FourierSobolevWeights.B_injective F
  intro ψ
  exact (hbound ψ).trans (mul_le_mul_of_nonneg_left
    (FourierSobolevWeights.sqrt_fourierHNormSq_three_le_norm_B ψ) hC)

/-- In particular, a functional with the stated Fourier bound is continuous
for the Schwartz topology. -/
theorem continuous_of_fourierHNormSq_bound
    (F : ComplexTest →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ψ : ComplexTest, ‖F ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ)) :
    Continuous F := by
  obtain ⟨q, hq⟩ := exists_inner_representation_of_fourierHNormSq_bound F hC hbound
  have hc : Continuous (fun ψ : ComplexTest =>
      @inner ℂ FrequencyL2 _ q (FourierSobolevWeights.B ψ)) :=
    continuous_const.inner FourierSobolevWeights.continuous_B
  exact hc.congr fun ψ => (hq ψ).symm

/-- A weighted `L²` representative that annihilates ordinary Laplacians is zero. -/
theorem representative_eq_zero_of_harmonic
    (q : FrequencyL2)
    (hq : ∀ ψ : ComplexTest,
      @inner ℂ FrequencyL2 _ q (FourierSobolevWeights.B (laplacianCLM ψ)) = 0) :
    q = 0 := by
  apply WeakFourierUniqueness.eq_zero_of_integral_weight_normSq_test_eq_zero q
  intro φ
  let ψ : ComplexTest := (FourierTransform.fourierCLE ℂ ComplexTest).symm φ
  have hzero := hq ψ
  rw [FourierSobolevWeights.inner_B_eq_integral] at hzero
  let c : ℂ := -(4 * (Real.pi : ℂ) ^ 2)
  have hc : c ≠ 0 := by
    dsimp [c]
    apply neg_ne_zero.mpr
    apply mul_ne_zero (by norm_num)
    exact pow_ne_zero 2 (by exact_mod_cast Real.pi_ne_zero)
  have hi : (fun ξ : Space => star (q ξ) *
      (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) *
        FourierTransform.fourierCLE ℂ ComplexTest (laplacianCLM ψ) ξ) =
      (fun ξ : Space => c • (star (q ξ) *
        (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ) * φ ξ)) := by
    funext ξ
    rw [fourier_laplacianCLM_apply]
    simp only [ψ, ContinuousLinearEquiv.apply_symm_apply, smul_eq_mul, c]
    ring
  rw [hi, integral_smul] at hzero
  change c * (∫ ξ : Space, star (q ξ) *
    (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ) * φ ξ) = 0 at hzero
  exact (mul_eq_zero.mp hzero).resolve_left hc

/-- A harmonic Schwartz functional bounded in Fourier `H⁻³` vanishes. -/
theorem eq_zero_of_harmonic
    (F : ComplexTest →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ψ : ComplexTest, ‖F ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ))
    (hharmonic : ∀ ψ : ComplexTest, F (laplacianCLM ψ) = 0) : F = 0 := by
  obtain ⟨q, hq⟩ := exists_inner_representation_of_fourierHNormSq_bound F hC hbound
  have hqzero : q = 0 := representative_eq_zero_of_harmonic q (fun ψ => by
    rw [← hq]
    exact hharmonic ψ)
  ext ψ
  change F ψ = 0
  rw [hq, hqzero]
  simp

/-- The pressure-recovery form: harmonicity need only be known against compactly
supported tests. The Fourier bound supplies the continuity needed to pass to
all Schwartz tests. No pressure pairing outside compact support is assumed. -/
theorem eq_zero_of_compact_harmonic
    (F : ComplexTest →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ψ : ComplexTest, ‖F ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ))
    (hharmonic : ∀ ψ : ComplexTest, HasCompactSupport (ψ : Space → ℂ) →
      F (laplacianCLM ψ) = 0) : F = 0 := by
  apply eq_zero_of_harmonic F hC hbound
  intro ψ
  exact SchwartzCompactApproximation.continuous_zero_of_compactSupport
    (fun φ : ComplexTest => F (laplacianCLM φ))
    ((continuous_of_fourierHNormSq_bound F hC hbound).comp laplacianCLM.continuous)
    hharmonic ψ

end NavierStokesR3.HarmonicTestFunctionals
end


/-! Merged from `NavierStokes.R3.TemporalTestUniqueness`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Pointwise recovery from compact temporal tests -/


noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokesR3.TemporalTestUniqueness

/-- Continuity turns the distributional fundamental lemma into equality at
every time of the open interval. The tests are real, and values may be complex. -/
theorem eq_zero_on_open_of_tests {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℂ}
    (hf : ContinuousOn f U)
    (htest : ∀ a : ℝ → ℝ, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ U →
      (∫ t : ℝ, a t • f t) = 0) :
    ∀ t ∈ U, f t = 0 := by
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hf.locallyIntegrableOn hU.measurableSet) htest
  have hrestr : f =ᵐ[volume.restrict U] (fun _ => (0 : ℂ)) := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hU.measurableSet] with t ht htU
    exact ht htU
  exact Measure.eqOn_open_of_ae_eq hrestr hU hf continuousOn_const

/-- A compact temporal test supported in `(0,T)` has the same integral over
`[0,T]` as over the line. No integrability of the untested function is needed. -/
theorem integral_eq_setIntegral {T : ℝ} {a : ℝ → ℝ} {f : ℝ → ℂ}
    (hs : tsupport a ⊆ Ioo (0 : ℝ) T) :
    (∫ t : ℝ, a t • f t) = ∫ t in Icc (0 : ℝ) T, a t • f t := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have ha : a t = 0 := image_eq_zero_of_notMem_tsupport fun h =>
    ht (Ioo_subset_Icc_self (hs h))
  simp only [ha, zero_smul]

theorem eq_zero_on_Ioo_of_setIntegral_tests {T : ℝ} {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioo (0 : ℝ) T))
    (htest : ∀ a : ℝ → ℝ, ContDiff ℝ ∞ a → HasCompactSupport a →
      tsupport a ⊆ Ioo (0 : ℝ) T →
      (∫ t in Icc (0 : ℝ) T, a t • f t) = 0) :
    ∀ t ∈ Ioo (0 : ℝ) T, f t = 0 := by
  apply eq_zero_on_open_of_tests isOpen_Ioo hf
  intro a ha hc hs
  rw [integral_eq_setIntegral hs]
  exact htest a ha hc hs

end NavierStokesR3.TemporalTestUniqueness


end



noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace NavierStokesR3.PressureRecovery

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness
open Comparison ConservativeDifference HarmonicTestFunctionals PressureFunctionals

/-- These are exactly the local smooth equation and uniform finite-energy
hypotheses of the comparison argument. -/
structure Hypotheses (T : ℝ) (u v : VelocityField) (p q : PressureField) : Prop where
  positive : 0 < T
  smooth_u : ContDiffOn ℝ ∞ u (Comparison.slab 0 T)
  smooth_v : ContDiffOn ℝ ∞ v (Comparison.slab 0 T)
  smooth_p : ContDiffOn ℝ ∞ p (Comparison.slab 0 T)
  smooth_q : ContDiffOn ℝ ∞ q (Comparison.slab 0 T)
  div_u : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence u t x = 0
  div_v : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence v t x = 0
  equation : ∀ t ∈ Ioo 0 T, ∀ x,
    navierStokesResidual u p t x = navierStokesResidual v q t x
  energy_u : NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) u
  energy_v : NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v

def velocityAverage (T : ℝ) (a : ℝ → ℝ) (u v : VelocityField) (k : Fin 3) : Space → ℝ :=
  timeAverage T a (fun z => (u - v) z k)

def tensorAverage (T : ℝ) (a : ℝ → ℝ) (u v : VelocityField)
    (i j : Fin 3) : Space → ℝ :=
  timeAverage T a (fun z => tensorDiff u v z.1 i j z.2)

theorem continuous_deriv_of_smooth {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) :
    Continuous (deriv a) := by
  have hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
    simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)
  change Continuous (fun t => fderiv ℝ a t 1)
  exact ((ha.fderiv_right hinf).clm_apply contDiff_const).continuous

theorem Hypotheses.velocityAverage_memLp {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T)) (k : Fin 3) :
    MemLp (velocityAverage T a u v k) 2 :=
  timeAverage_difference_component_memLp_two ha H.smooth_u.continuousOn H.smooth_v.continuousOn
    H.energy_u H.energy_v k

theorem Hypotheses.tensorAverage_integrable {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T)) (i j : Fin 3) :
    Integrable (tensorAverage T a u v i j) :=
  timeAverage_tensorDiff_integrable ha H.smooth_u.continuousOn H.smooth_v.continuousOn
    H.energy_u H.energy_v i j

theorem Hypotheses.tensor_bound {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, ∀ i j : Fin 3,
      Integrable (tensorDiff u v t i j) ∧ (∫ x, ‖tensorDiff u v t i j x‖) ≤ M :=
  uniformFiniteEnergy_tensorDiff_bound
    (fun _t ht => (spatial_smooth H.smooth_u ht).continuous.aestronglyMeasurable)
    (fun _t ht => (spatial_smooth H.smooth_v ht).continuous.aestronglyMeasurable)
    H.energy_u H.energy_v

theorem velocityAverage_pairing {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T))
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, velocityAverage T a u v k x * ψ x) =
      ∫ t in Icc 0 T, a t * (∫ x, (u - v) (t, x) k * ψ x) := by
  obtain ⟨M, _, hM⟩ := uniformFiniteEnergy_difference_component_l2Sq_bound
    H.smooth_u.continuousOn H.smooth_v.continuousOn H.energy_u H.energy_v k
  have hf : ContinuousOn (fun z => (u - v) z k) (Comparison.slab 0 T) :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_continuousOn
      (H.smooth_u.continuousOn.sub H.smooth_v.continuousOn)
  have h := timeAverage_complex_pairing_of_memLp_two
    (f := fun z => (u - v) z k) (ψ := (realTest ψ hψ hcψ : Space → ℂ)) ha hf
    (fun t ht => (hM t ht).1) (fun t ht => (hM t ht).2)
    (realTest ψ hψ hcψ).continuous ((realTest ψ hψ hcψ).memLp 2)
  apply Complex.ofReal_injective
  simpa only [velocityAverage, realTest_apply, ← Complex.ofReal_mul, integral_complex_ofReal] using h

theorem tensorAverage_pairing {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T))
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (i j : Fin 3) :
    (∫ x, tensorAverage T a u v i j x * ψ x) =
      ∫ t in Icc 0 T, a t * (∫ x, tensorDiff u v t i j x * ψ x) := by
  obtain ⟨M, _, hM⟩ := H.tensor_bound
  obtain ⟨C, hC⟩ := hcψ.exists_bound_of_continuous hψ.continuous
  have h := timeAverage_complex_pairing_of_bounded
    (f := fun z => tensorDiff u v z.1 i j z.2)
    (ψ := (realTest ψ hψ hcψ : Space → ℂ)) ha
    (continuousOn_tensorDiff_field H.smooth_u.continuousOn H.smooth_v.continuousOn i j)
    (fun t ht => (hM t ht i j).1) (fun t ht => (hM t ht i j).2)
    (realTest ψ hψ hcψ).continuous ⟨C, fun x => by simpa using hC x⟩
  apply Complex.ofReal_injective
  simpa only [tensorAverage, realTest_apply, ← Complex.ofReal_mul, integral_complex_ofReal] using h

/-- Fubini for the actual canonical pressure pairing. The Riesz test is
bounded, so the uniform tensor `L¹` bound controls the whole product. -/
theorem pressurePair_tensorAverage {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T))
    (i j : Fin 3) (ψ : ComplexTest) :
    pressurePair i j (tensorAverage T a u v i j) ψ =
      ∫ t in Icc 0 T, (a t : ℂ) * pressurePair i j (tensorDiff u v t i j) ψ := by
  obtain ⟨M, _, hM⟩ := H.tensor_bound
  obtain ⟨C, _, hC⟩ := RieszTestOperators.exists_bound_rieszTest i j ψ
  exact timeAverage_complex_pairing_of_bounded ha
    (continuousOn_tensorDiff_field H.smooth_u.continuousOn H.smooth_v.continuousOn i j)
    (fun t ht => (hM t ht i j).1) (fun t ht => (hM t ht i j).2)
    (RieszTestOperators.continuous_rieszTest i j ψ)
    ⟨C, hC⟩

theorem noncanonical_average_identity {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, (velocityAverage T a u v k x : ℂ) * laplacianCLM (realTest ψ hψ hcψ) x) +
      (∫ x, (velocityAverage T (deriv a) u v k x : ℂ) * realTest ψ hψ hcψ x) +
      (∑ i : Fin 3, ∫ x, (tensorAverage T a u v k i x : ℂ) *
        partialCLM i (realTest ψ hψ hcψ) x) =
      ((∫ t in Icc 0 T, a t *
        (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) : ℝ) : ℂ) := by
  have hsum : (∑ i : Fin 3, ∫ x, tensorAverage T a u v k i x * spatialPartial i ψ x) =
      ∫ t in Icc 0 T, a t * (∑ i : Fin 3, ∫ x, tensorDiff u v t k i x * spatialPartial i ψ x) := by
    have hpair : (∑ i : Fin 3, ∫ x, tensorAverage T a u v k i x * spatialPartial i ψ x) =
        ∑ i : Fin 3, ∫ t in Icc 0 T, a t * (∫ x, tensorDiff u v t k i x * spatialPartial i ψ x) := by
      apply Finset.sum_congr rfl
      intro i _
      exact tensorAverage_pairing (ψ := spatialPartial i ψ) H ha.continuous.continuousOn
        (spatial_partial_contDiff hψ i) (CompactEnergy.compact_partial hcψ i) k i
    rw [hpair]
    simp only [Finset.mul_sum]
    exact (integral_finsetSum _ (fun i _ =>
      (ha.continuous.continuousOn.mul
        (PressureTemporalIdentity.tensor_test_continuousOn H.smooth_u.continuousOn
          H.smooth_v.continuousOn (spatial_partial_contDiff hψ i).continuous
            (CompactEnergy.compact_partial hcψ i) k i)).integrableOn_Icc)).symm
  have hreal : (∫ x, velocityAverage T a u v k x * scalarLaplacian ψ x) +
      (∫ x, velocityAverage T (deriv a) u v k x * ψ x) +
      (∑ i : Fin 3, ∫ x, tensorAverage T a u v k i x * spatialPartial i ψ x) =
      ∫ t in Icc 0 T, a t *
        (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) := by
    rw [velocityAverage_pairing H ha.continuous.continuousOn (scalarLaplacian_contDiff hψ)
        (compact_scalarLaplacian hcψ) k,
      velocityAverage_pairing H (continuous_deriv_of_smooth ha).continuousOn hψ hcψ k, hsum]
    exact (PressureTemporalIdentity.pressure_time_identity H.positive H.smooth_u H.smooth_v
      H.smooth_p H.smooth_q H.div_u H.div_v H.equation ha hsupp hψ hcψ k).symm
  simp only [laplacianCLM_realTest, partialCLM_realTest, realTest_apply,
    ← Complex.ofReal_mul, integral_complex_ofReal]
  change ((∫ x, velocityAverage T a u v k x * scalarLaplacian ψ x : ℝ) : ℂ) +
      ((∫ x, velocityAverage T (deriv a) u v k x * ψ x : ℝ) : ℂ) +
      (∑ i : Fin 3, ∫ x, (tensorAverage T a u v k i x : ℂ) *
        ((spatialPartial i ψ x : ℝ) : ℂ)) = _
  simpa only [← Complex.ofReal_mul, integral_complex_ofReal, Complex.ofReal_add,
    Complex.ofReal_sum] using congrArg Complex.ofReal hreal

theorem averaged_value_realTest {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    averagedPressureDifferenceValue (velocityAverage T a u v k)
      (velocityAverage T (deriv a) u v k) (tensorAverage T a u v) k (realTest ψ hψ hcψ) =
      ((∫ t in Icc 0 T, a t *
        (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) : ℝ) : ℂ) +
      ∑ i : Fin 3, ∑ j : Fin 3,
        pressurePair i j (tensorAverage T a u v i j) (partialCLM k (realTest ψ hψ hcψ)) := by
  unfold averagedPressureDifferenceValue
  rw [noncanonical_average_identity H ha hsupp hψ hcψ k]

/-- Averaging the differentiated Poisson equation commutes with each compact
tensor pairing. All derivatives remain on the compact test. -/
theorem averaged_gradient_poisson {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ t in Icc 0 T, a t *
      (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * scalarLaplacian ψ x)) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, tensorAverage T a u v i j x *
        spatialPartial i (spatialPartial j (spatialPartial k ψ)) x := by
  have hD (i j : Fin 3) :
      ContDiff ℝ ∞ (spatialPartial i (spatialPartial j (spatialPartial k ψ))) :=
    spatial_partial_contDiff (spatial_partial_contDiff (spatial_partial_contDiff hψ k) j) i
  have hC (i j : Fin 3) :
      HasCompactSupport (spatialPartial i (spatialPartial j (spatialPartial k ψ))) :=
    CompactEnergy.compact_partial
      (CompactEnergy.compact_partial (CompactEnergy.compact_partial hcψ k) j) i
  have hi (i j : Fin 3) : IntegrableOn (fun t => a t * (∫ x, tensorDiff u v t i j x *
      spatialPartial i (spatialPartial j (spatialPartial k ψ)) x)) (Icc 0 T) :=
    (ha.continuous.continuousOn.mul
      (PressureTemporalIdentity.tensor_test_continuousOn H.smooth_u.continuousOn
        H.smooth_v.continuousOn (hD i j).continuous (hC i j) i j)).integrableOn_Icc
  have hpoint : (fun t => a t *
      (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * scalarLaplacian ψ x)) =
      (fun t => a t * (∑ i : Fin 3, ∑ j : Fin 3, ∫ x, tensorDiff u v t i j x *
        spatialPartial i (spatialPartial j (spatialPartial k ψ)) x)) := by
    funext t
    by_cases ht : t ∈ Ioo 0 T
    · rw [gradient_poisson_test H.smooth_u H.smooth_v H.smooth_p H.smooth_q ht
        H.div_u H.div_v (H.equation t ht) hψ hcψ k]
    · have hat : a t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (hsupp h))
      simp only [hat, zero_mul]
  rw [hpoint]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact (tensorAverage_pairing (ψ := spatialPartial i (spatialPartial j (spatialPartial k ψ)))
    H ha.continuous.continuousOn (hD i j) (hC i j) i j).symm

theorem averaged_gradient_poisson_complex {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    ((∫ t in Icc 0 T, a t *
      (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * scalarLaplacian ψ x) : ℝ) : ℂ) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, (tensorAverage T a u v i j x : ℂ) *
        partialCLM i (partialCLM j (partialCLM k (realTest ψ hψ hcψ))) x := by
  have htest (i j : Fin 3) :
      partialCLM i (partialCLM j (partialCLM k (realTest ψ hψ hcψ))) =
        realTest (spatialPartial i (spatialPartial j (spatialPartial k ψ)))
          (spatial_partial_contDiff (spatial_partial_contDiff
            (spatial_partial_contDiff hψ k) j) i)
          (CompactEnergy.compact_partial (CompactEnergy.compact_partial
            (CompactEnergy.compact_partial hcψ k) j) i) :=
    (congrArg (fun t => partialCLM i (partialCLM j t))
      (partialCLM_realTest ψ hψ hcψ k)).trans
      ((congrArg (partialCLM i) (partialCLM_realTest (spatialPartial k ψ)
        (spatial_partial_contDiff hψ k) (CompactEnergy.compact_partial hcψ k) j)).trans
        (partialCLM_realTest (spatialPartial j (spatialPartial k ψ))
          (spatial_partial_contDiff (spatial_partial_contDiff hψ k) j)
          (CompactEnergy.compact_partial (CompactEnergy.compact_partial hcψ k) j) i))
  simp only [htest]
  change _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, (tensorAverage T a u v i j x : ℂ) *
    ((spatialPartial i (spatialPartial j (spatialPartial k ψ)) x : ℝ) : ℂ)
  simpa only [← Complex.ofReal_mul, integral_complex_ofReal, Complex.ofReal_sum] using
    congrArg Complex.ofReal (averaged_gradient_poisson H ha hsupp hψ hcψ k)

/-- The averaged physical-minus-canonical pressure-gradient functional is
harmonic on every compact real test, by the two actual Poisson identities. -/
theorem averaged_value_real_harmonic {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    averagedPressureDifferenceValue (velocityAverage T a u v k)
      (velocityAverage T (deriv a) u v k) (tensorAverage T a u v) k
        (laplacianCLM (realTest ψ hψ hcψ)) = 0 := by
  calc
    _ = ((∫ t in Icc 0 T, a t *
        (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * scalarLaplacian ψ x) : ℝ) : ℂ) +
        ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorAverage T a u v i j)
          (partialCLM k (laplacianCLM (realTest ψ hψ hcψ))) := by
      simpa only [laplacianCLM_realTest] using
        averaged_value_realTest H ha hsupp (scalarLaplacian_contDiff hψ)
          (compact_scalarLaplacian hcψ) k
    _ = ((∫ t in Icc 0 T, a t *
        (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * scalarLaplacian ψ x) : ℝ) : ℂ) -
        (∑ i : Fin 3, ∑ j : Fin 3, ∫ x, (tensorAverage T a u v i j x : ℂ) *
          partialCLM i (partialCLM j (partialCLM k (realTest ψ hψ hcψ))) x) := by
      simp only [partial_laplacian_realTest, RieszTestOperators.pressurePair_laplacianCLM,
        Finset.sum_neg_distrib, sub_eq_add_neg]
    _ = 0 := by
      rw [averaged_gradient_poisson_complex H ha hsupp hψ hcψ k, sub_self]

/-- The genuine `H³` bound and compact harmonicity force the whole averaged
functional to vanish. No representative of the physical pressure on Schwartz
tests has been introduced. -/
theorem averaged_value_zero {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T) (k : Fin 3) (ψ : ComplexTest) :
    averagedPressureDifferenceValue (velocityAverage T a u v k)
      (velocityAverage T (deriv a) u v k) (tensorAverage T a u v) k ψ = 0 := by
  have hW0 := H.velocityAverage_memLp ha.continuous.continuousOn k
  have hW1 := H.velocityAverage_memLp (continuous_deriv_of_smooth ha).continuousOn k
  have hG := H.tensorAverage_integrable ha.continuous.continuousOn
  let F : ComplexTest →ₗ[ℂ] ℂ := averagedPressureDifference (velocityAverage T a u v k)
    (velocityAverage T (deriv a) u v k) (tensorAverage T a u v) hW0 hW1 hG k
  obtain ⟨C, hC, hbound⟩ := averagedPressureDifference_bound hW0 hW1 hG k
  have hharmonic : ∀ φ : ComplexTest, HasCompactSupport (φ : Space → ℂ) →
      F (laplacianCLM φ) = 0 := by
    apply compact_harmonic_of_real F
    intro φ hφ hcφ
    simpa only [F, averagedPressureDifference_apply] using
      averaged_value_real_harmonic H ha hsupp hφ hcφ k
  have hz : F = 0 := eq_zero_of_compact_harmonic F hC hbound hharmonic
  have hvalue : F ψ = 0 := by rw [hz]; rfl
  simpa only [F, averagedPressureDifference_apply] using hvalue

/-- The uniform tensor bound and spatial decay of a Riesz test give
continuity of its canonical pairing in time, including the slab endpoints. -/
theorem pressurePair_continuousOn {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (i j : Fin 3) (ψ : ComplexTest) :
    ContinuousOn (fun t => pressurePair i j (tensorDiff u v t i j) ψ) (Icc 0 T) := by
  obtain ⟨M, _, hM⟩ := H.tensor_bound
  exact WeakTimeContinuity.continuousOn_pairing
    (continuousOn_tensorDiff_field H.smooth_u.continuousOn H.smooth_v.continuousOn i j)
    (fun t ht => (hM t ht i j).1) (fun t ht => (hM t ht i j).2)
    (RieszTestOperators.continuous_rieszTest i j ψ)
    (RieszTestOperators.rieszTest_tendsto_zero i j ψ)

theorem canonical_sum_continuousOn {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ψ : ComplexTest) :
    ContinuousOn (fun t => ∑ i : Fin 3, ∑ j : Fin 3,
      pressurePair i j (tensorDiff u v t i j) ψ) (Icc 0 T) :=
  continuousOn_finsetSum _ (fun i _ =>
    continuousOn_finsetSum _ (fun j _ => pressurePair_continuousOn H i j ψ))

theorem canonical_sum_timeAverage {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T))
    (ψ : ComplexTest) :
    (∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorAverage T a u v i j) ψ) =
      ∫ t in Icc 0 T, (a t : ℂ) *
        (∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorDiff u v t i j) ψ) := by
  have hi (i j : Fin 3) : IntegrableOn (fun t =>
      (a t : ℂ) * pressurePair i j (tensorDiff u v t i j) ψ) (Icc 0 T) :=
    ((Complex.continuous_ofReal.comp_continuousOn ha).mul
      (pressurePair_continuousOn H i j ψ)).integrableOn_Icc
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorAverage T a u v i j) ψ) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ t in Icc 0 T,
        (a t : ℂ) * pressurePair i j (tensorDiff u v t i j) ψ := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact pressurePair_tensorAverage H ha i j ψ
  rw [hsum]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_finsetSum _ (fun j _ => hi i j)).symm

/-- Every compact temporal test annihilates the difference between the
physical and canonical pressure gradients, at a fixed compact spatial test. -/
theorem time_test_gradient_difference_zero {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ t in Icc 0 T, a t •
      (((∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x : ℝ) : ℂ) +
        ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorDiff u v t i j)
          (partialCLM k (realTest ψ hψ hcψ)))) = 0 := by
  let P : ℝ → ℝ := fun t => ∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x
  let Ψ := partialCLM k (realTest ψ hψ hcψ)
  let Q : ℝ → ℂ := fun t => ∑ i : Fin 3, ∑ j : Fin 3,
    pressurePair i j (tensorDiff u v t i j) Ψ
  have hP : ContinuousOn P (Ioo 0 T) :=
    pressure_gradient_pairing_continuousOn H.smooth_u H.smooth_v H.smooth_p H.smooth_q
      H.div_u H.div_v H.equation hψ hcψ k
  have hPweight : Continuous (fun t => a t * P t) :=
    PressureTemporalIdentity.continuous_cutoff_mul ha.continuous hP isOpen_Ioo hsupp
  have hiP : IntegrableOn (fun t => (a t : ℂ) * (P t : ℂ)) (Icc 0 T) := by
    have hi : IntegrableOn (fun t => ((a t * P t : ℝ) : ℂ)) (Icc 0 T) :=
      (Complex.continuous_ofReal.comp hPweight).continuousOn.integrableOn_Icc
    simpa only [Complex.ofReal_mul] using hi
  have hQ : ContinuousOn Q (Icc 0 T) := canonical_sum_continuousOn H Ψ
  have hiQ : IntegrableOn (fun t => (a t : ℂ) * Q t) (Icc 0 T) :=
    ((Complex.continuous_ofReal.comp_continuousOn ha.continuous.continuousOn).mul hQ).integrableOn_Icc
  have hz := averaged_value_zero H ha hsupp k (realTest ψ hψ hcψ)
  rw [averaged_value_realTest H ha hsupp hψ hcψ k] at hz
  change (((∫ t in Icc 0 T, a t * P t : ℝ) : ℂ) +
    ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorAverage T a u v i j) Ψ) = 0 at hz
  rw [canonical_sum_timeAverage H ha.continuous.continuousOn Ψ] at hz
  change (∫ t in Icc 0 T, a t • ((P t : ℂ) + Q t)) = 0
  simp only [Complex.real_smul, mul_add]
  rw [integral_add hiP hiQ]
  simp only [← Complex.ofReal_mul, integral_complex_ofReal]
  exact hz

/-- Actual pressure-gradient recovery at every interior time. This equality
is obtained from the equation and uniform finite energy, rather than assumed
as a pressure normalization. -/
theorem gradient_recovery_complex {T t : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ht : t ∈ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    ((∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x : ℝ) : ℂ) =
      -(∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorDiff u v t i j)
        (partialCLM k (realTest ψ hψ hcψ))) := by
  have hP := pressure_gradient_pairing_continuousOn
    H.smooth_u H.smooth_v H.smooth_p H.smooth_q H.div_u H.div_v H.equation hψ hcψ k
  have hQ := canonical_sum_continuousOn H (partialCLM k (realTest ψ hψ hcψ))
  have hcontinuous := (Complex.continuous_ofReal.comp_continuousOn hP).add
    (hQ.mono Ioo_subset_Icc_self)
  have hzero := TemporalTestUniqueness.eq_zero_on_Ioo_of_setIntegral_tests hcontinuous (by
    intro a ha _hca hsupp
    exact time_test_gradient_difference_zero H ha hsupp hψ hcψ k)
  exact eq_neg_of_add_eq_zero_left (hzero t ht)

theorem gradient_recovery {T t : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ht : t ∈ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) =
      -(∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorDiff u v t i j)
        (partialCLM k (realTest ψ hψ hcψ))).re := by
  simpa only [Complex.ofReal_re, Complex.neg_re] using
    congrArg Complex.re (gradient_recovery_complex H ht hψ hcψ k)


end NavierStokesR3.PressureRecovery

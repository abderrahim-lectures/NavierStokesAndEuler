import NavierStokes.PowerMomentMatrix
import NavierStokes.ParametricRephase
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Matrix.Normed

/-!
# Smooth parameter families of exponential bump moments

This is the logarithmic-coordinate clause of `outgoing:moment-rank`. Exponents,
bumps and support intervals may vary with the parameter. The actual integrated
matrix and its nonsingular inverse are smooth, with all fixed inverse jets
bounded on compact parameter sets.
-/
/-! Merged from `NavierStokes.SmoothPowerMomentMatrix` (in a section, so its `open`s cannot leak). -/
section
/-!
# Smooth families of actual power moment matrices

The integration intervals may move with the parameter. Locally uniform compact
support is derived from their continuous endpoints. Smoothness of the integral
matrix and its actual inverse is then proved from the primitive data, and
compactness bounds every fixed parameter jet of that inverse.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Interval BigOperators Matrix.Norms.Elementwise

namespace NavierStokes.SmoothPowerMomentMatrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A moving compact support can be replaced locally by a fixed finite interval. -/
theorem integral_contDiffOn_of_moving_support [ProperSpace E]
    (U : Set E) (hU : IsOpen U) (F : E × ℝ → ℝ)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ)) (l u : E → ℝ)
    (hl : ContinuousOn l U) (hu : ContinuousOn u U)
    (hs : ∀ p ∈ U, support (fun t => F (p, t)) ⊆ Icc (l p) (u p)) :
    ContDiffOn ℝ ∞ (fun p => ∫ t, F (p, t)) U := by
  intro p hp
  let a := min (l p) (u p) - 1
  let b := max (l p) (u p) + 1
  have ha : a < l p := by dsimp [a]; linarith [min_le_left (l p) (u p)]
  have hb : u p < b := by dsimp [b]; linarith [le_max_right (l p) (u p)]
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith [show min (l p) (u p) ≤ max (l p) (u p) from min_le_max]
  have hi := ParametricRephase.intervalIntegral_contDiffOn_of_joint F U hU hF a b hab
  have heq : (fun q => ∫ t, F (q, t)) =ᶠ[𝓝 p]
      (fun q => ∫ t in a..b, F (q, t)) := by
    filter_upwards [hU.mem_nhds hp,
      (hl.continuousAt (hU.mem_nhds hp)).eventually (lt_mem_nhds ha),
      (hu.continuousAt (hU.mem_nhds hp)).eventually (gt_mem_nhds hb)] with q hq hql hqu
    symm
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro t ht
    exact ⟨lt_of_lt_of_le hql (hs q hq ht).1, (hs q hq ht).2.trans hqu.le⟩
  exact ((hi.contDiffAt (hU.mem_nhds hp)).congr_of_eventuallyEq heq).contDiffWithinAt

/-- Determinants are finite polynomials in their entries. -/
theorem determinant_contDiffOn {n : ℕ} {U : Set E}
    (M : E → Matrix (Fin n) (Fin n) ℝ)
    (hM : ContDiffOn ℝ ∞ M U) : ContDiffOn ℝ ∞ (fun p => (M p).det) U := by
  classical
  simp only [Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ _
  apply contDiffOn_const.mul
  apply contDiffOn_prod
  intro i _
  exact (contDiffOn_pi.mp (contDiffOn_pi.mp hM (σ i)) i)

/-- The ordinary nonsingular matrix inverse is smooth wherever its determinant
is nonzero. The proof uses the explicit cofactor formula. -/
theorem inverse_contDiffOn {n : ℕ} {U : Set E}
    (M : E → Matrix (Fin n) (Fin n) ℝ)
    (hM : ContDiffOn ℝ ∞ M U) (hdet : ∀ p ∈ U, (M p).det ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => (M p)⁻¹) U := by
  classical
  have hd := (determinant_contDiffOn M hM).inv hdet
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  apply hd.mul
  apply determinant_contDiffOn
  apply contDiffOn_pi.mpr
  intro k
  apply contDiffOn_pi.mpr
  intro t
  by_cases hkj : k = j
  · subst k
    simp only [Matrix.updateRow_self]
    exact contDiffOn_const
  · simpa only [Matrix.updateRow_ne hkj] using
      (contDiffOn_pi.mp (contDiffOn_pi.mp hM k) t)

/-- Primitive smooth data for separated positive bump moments. Endpoint
continuity suffices; in particular smoothly moving intervals are allowed. -/
structure Family (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (U : Set E) where
  exponent : E → Fin n → ℝ
  lower : E → Fin n → ℝ
  upper : E → Fin n → ℝ
  bump : E → Fin n → ℝ → ℝ
  exponent_smooth : ∀ i, ContDiffOn ℝ ∞ (fun p => exponent p i) U
  lower_continuous : ∀ j, ContinuousOn (fun p => lower p j) U
  upper_continuous : ∀ j, ContinuousOn (fun p => upper p j) U
  bump_smooth : ∀ j, ContDiffOn ℝ ∞ (fun z : E × ℝ => bump z.1 j z.2) (U ×ˢ univ)
  exponent_injective : ∀ p ∈ U, Injective (exponent p)
  lower_pos : ∀ p ∈ U, ∀ j, 0 < lower p j
  separated : ∀ p ∈ U, ∀ i j, i < j → upper p i < lower p j
  bump_nonnegative : ∀ p ∈ U, ∀ j t, 0 ≤ bump p j t
  bump_nonzero : ∀ p ∈ U, ∀ j, ∃ t, bump p j t ≠ 0
  bump_support : ∀ p ∈ U, ∀ j, support (bump p j) ⊆ Icc (lower p j) (upper p j)

namespace Family

variable {n : ℕ} {U : Set E} (D : Family E n U)

/-- Exactly the ordinary integral matrix in `PowerMomentMatrix`. -/
def matrix (p : E) : Matrix (Fin n) (Fin n) ℝ :=
  PowerMomentMatrix.bumpMomentMatrix (D.exponent p) (D.bump p)


theorem integrand_contDiffOn (hU : IsOpen U) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun z : E × ℝ => z.2 ^ D.exponent z.1 i * D.bump z.1 j z.2)
      (U ×ˢ univ) := by
  intro z hz
  have hopen : IsOpen (U ×ˢ (univ : Set ℝ)) := hU.prod isOpen_univ
  have he : ContDiffAt ℝ ∞ (fun z : E × ℝ => D.exponent z.1 i) z :=
    (D.exponent_smooth i |>.contDiffAt (hU.mem_nhds hz.1)).comp z contDiffAt_fst
  by_cases ht : z.2 = 0
  · have hl : ContinuousAt (fun y : E × ℝ => D.lower y.1 j) z :=
      (D.lower_continuous j |>.continuousAt (hU.mem_nhds hz.1)).comp continuousAt_fst
    have hlt : z.2 < D.lower z.1 j := by rw [ht]; exact D.lower_pos z.1 hz.1 j
    have heq : (fun y : E × ℝ => y.2 ^ D.exponent y.1 i * D.bump y.1 j y.2)
        =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hz,
        (continuousAt_snd.eventually_lt hl hlt)] with y hy hyl
      have hb : D.bump y.1 j y.2 = 0 := by
        by_contra hb
        exact (not_le_of_gt hyl) (D.bump_support y.1 hy.1 j hb).1
      rw [hb, mul_zero]
    exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt
  · exact ((contDiffAt_snd.rpow he ht).mul
      (D.bump_smooth j |>.contDiffAt (hopen.mem_nhds hz))).contDiffWithinAt

theorem matrix_contDiffOn [ProperSpace E] (hU : IsOpen U) :
    ContDiffOn ℝ ∞ D.matrix U := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  apply integral_contDiffOn_of_moving_support U hU _ (D.integrand_contDiffOn hU i j)
    (fun p => D.lower p j) (fun p => D.upper p j)
    (D.lower_continuous j) (D.upper_continuous j)
  intro p hp t ht
  apply D.bump_support p hp j
  intro hb
  exact ht (by dsimp only; rw [hb, mul_zero])

theorem matrix_det_ne_zero (p : E) (hp : p ∈ U) : (D.matrix p).det ≠ 0 := by
  apply PowerMomentMatrix.bumpMomentMatrix_det_ne_zero
    (D.exponent p) (D.lower p) (D.upper p) (D.bump p)
    (D.exponent_injective p hp) (D.lower_pos p hp) (D.separated p hp)
  · intro j
    exact contDiffOn_univ.mp ((D.bump_smooth j).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun t _ => ⟨hp, mem_univ t⟩)) |>.continuous
  · exact D.bump_nonnegative p hp
  · exact D.bump_nonzero p hp
  · exact D.bump_support p hp

theorem matrix_inverse_contDiffOn [ProperSpace E] (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (fun p => (D.matrix p)⁻¹) U :=
  inverse_contDiffOn D.matrix (D.matrix_contDiffOn hU) D.matrix_det_ne_zero

/-- Every fixed full parameter derivative of the actual inverse matrix is
uniformly bounded on an arbitrary compact subset of the parameter domain. -/
theorem compact_inverse_jet_bound [ProperSpace E] (hU : IsOpen U)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U) (m : ℕ) :
    ∃ C ≥ 0, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ m (fun q => (D.matrix q)⁻¹) p‖ ≤ C := by
  have hj : ContinuousOn (iteratedFDeriv ℝ m (fun q => (D.matrix q)⁻¹)) U := by
    intro p hp
    exact (((D.matrix_inverse_contDiffOn hU).contDiffAt (hU.mem_nhds hp)).iteratedFDeriv_right
      (m := 0) (by simp)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hj.mono hKU)
  exact ⟨max C 0, le_max_right _ _, fun p hp => (hC p hp).trans (le_max_left _ _)⟩

/-- A common bound also controls the inverse and all jets up to any prescribed
finite order, uniformly over the compact parameter set. -/
theorem compact_inverse_jets_bound [ProperSpace E] (hU : IsOpen U)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U) (m : ℕ) :
    ∃ C ≥ 0, ∀ k ≤ m, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k (fun q => (D.matrix q)⁻¹) p‖ ≤ C := by
  choose C hC hbound using fun k : Fin (m + 1) =>
    D.compact_inverse_jet_bound hU K hK hKU k.val
  refine ⟨∑ k, C k, Finset.sum_nonneg (fun k _ => hC k), ?_⟩
  intro k hk p hp
  exact (hbound ⟨k, by omega⟩ p hp).trans
    (Finset.single_le_sum (fun t _ => hC t)
      (Finset.mem_univ (⟨k, by omega⟩ : Fin (m + 1))))

end Family
end NavierStokes.SmoothPowerMomentMatrix
end

/-! Merged from `NavierStokes.ExponentialMomentMatrix` (in a section, so its `open`s cannot leak). -/
section
/-!
# Exponential moments on separated intervals

The logarithmic-coordinate clause of `outgoing:moment-rank` concerns actual
integrals against positive bumps. The intervals may lie anywhere on the real
line. The proof uses the existing Rolle induction for exponential sums.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace NavierStokes.ExponentialMomentMatrix

open PowerMomentMatrix

/-- Exponential moments against finite positive measures on real intervals. -/
def expIntervalMomentMatrix {n : ℕ} (a l u : Fin n → ℝ)
    (μ : Fin n → Measure ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ t in Set.Icc (l j) (u j), Real.exp (a i * t) ∂μ j

theorem integral_expSum {n : ℕ} (a c : Fin n → ℝ) (l u : ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (∫ t in Set.Icc l u, expSum a c t ∂μ) =
      ∑ i, c i * ∫ t in Set.Icc l u, Real.exp (a i * t) ∂μ := by
  unfold expSum
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro i _
    apply ContinuousOn.integrableOn_Icc
    exact (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn

/-- Distinct exponents and strictly separated positive masses give an
invertible integrated matrix. No sign restriction is imposed on the interval
endpoints in the logarithmic coordinate. -/
theorem expIntervalMomentMatrix_det_ne_zero {n : ℕ} (a l u : Fin n → ℝ)
    (μ : Fin n → Measure ℝ) [∀ j, IsFiniteMeasure (μ j)]
    (ha : Function.Injective a) (hsep : ∀ i j, i < j → u i < l j)
    (hmass : ∀ j, μ j (Set.Icc (l j) (u j)) ≠ 0) :
    (expIntervalMomentMatrix a l u μ).det ≠ 0 := by
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.vecMul_injective_iff_isUnit.mp
  intro c d hcd
  dsimp only at hcd
  have hzero : (expIntervalMomentMatrix a l u μ).vecMul (c - d) = 0 := by
    rw [Matrix.sub_vecMul, hcd, sub_self]
  have hroots : ∀ j, ∃ t ∈ Set.Icc (l j) (u j), expSum a (c - d) t = 0 := by
    intro j
    apply exists_zero_of_setIntegral_eq_zero (μ j) (l j) (u j) _ (hmass j)
    · exact (continuous_iff_continuousAt.mpr
        (fun t => (expSum_hasDerivAt a (c - d) t).continuousAt)).continuousOn
    · rw [integral_expSum]
      exact congrFun hzero j
  choose x hx hroot using hroots
  have hxmono : StrictMono x := by
    intro i j hij
    exact lt_of_le_of_lt (hx i).2 (lt_of_lt_of_le (hsep i j hij) (hx j).1)
  exact sub_eq_zero.mp (expSum_coefficients_zero n a (c - d) x ha hxmono hroot)

/-- The actual Lebesgue moment matrix for exponential weights and bumps. -/
def expBumpMomentMatrix {n : ℕ} (a : Fin n → ℝ) (β : Fin n → ℝ → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => ∫ t, Real.exp (a i * t) * β j t

/-- The logarithmic-coordinate moment-rank assertion for arbitrary distinct
real exponents and separated nonnegative nonzero bumps. Continuity suffices;
the manuscript's smooth bump hypotheses are stronger than required. -/
theorem expBumpMomentMatrix_det_ne_zero {n : ℕ} (a l u : Fin n → ℝ)
    (β : Fin n → ℝ → ℝ) (ha : Function.Injective a)
    (hsep : ∀ i j, i < j → u i < l j)
    (hcont : ∀ j, Continuous (β j)) (hnonneg : ∀ j t, 0 ≤ β j t)
    (hnonzero : ∀ j, ∃ t, β j t ≠ 0)
    (hsupp : ∀ j, Function.support (β j) ⊆ Set.Icc (l j) (u j)) :
    (expBumpMomentMatrix a β).det ≠ 0 := by
  have hcompact : ∀ j, HasCompactSupport (β j) := fun j =>
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (hsupp j)
  have hintegrable : ∀ j, Integrable (β j) := fun j =>
    (hcont j).integrable_of_hasCompactSupport (hcompact j)
  have hout : ∀ j t, t ∉ Set.Icc (l j) (u j) → β j t = 0 := by
    intro j t ht
    by_contra h
    exact ht (hsupp j h)
  let μ : Fin n → Measure ℝ := fun j => volume.withDensity (fun t => ENNReal.ofReal (β j t))
  let : ∀ j, IsFiniteMeasure (μ j) := fun j =>
    isFiniteMeasure_withDensity_ofReal (hintegrable j).2
  have hdensity : ∀ j (f : ℝ → ℝ),
      (∫ t in Set.Icc (l j) (u j), f t ∂μ j) =
        ∫ t in Set.Icc (l j) (u j), β j t * f t := by
    intro j f
    dsimp [μ]
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
      (hcont j).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top) f measurableSet_Icc]
    simp only [ENNReal.toReal_ofReal (hnonneg j _), smul_eq_mul]
  have hmass : ∀ j, μ j (Set.Icc (l j) (u j)) ≠ 0 := by
    intro j hzero
    have hr : (μ j).restrict (Set.Icc (l j) (u j)) = 0 :=
      Measure.restrict_eq_zero.mpr hzero
    have heq := hdensity j (fun _ => (1 : ℝ))
    rw [hr, integral_zero_measure] at heq
    simp only [mul_one] at heq
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hout j)] at heq
    obtain ⟨t, ht⟩ := hnonzero j
    have hpos : 0 < ∫ t, β j t := (hcont j).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hcompact j) (hnonneg j) ht
    linarith
  have hmatrix : expBumpMomentMatrix a β = expIntervalMomentMatrix a l u μ := by
    ext i j
    change (∫ t, Real.exp (a i * t) * β j t) =
      ∫ t in Set.Icc (l j) (u j), Real.exp (a i * t) ∂μ j
    rw [hdensity]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht => by rw [hout j t ht, zero_mul])]
    congr 1
    ext t
    exact mul_comm _ _
  rw [hmatrix]
  exact expIntervalMomentMatrix_det_ne_zero a l u μ ha hsep hmass

end NavierStokes.ExponentialMomentMatrix
end


noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Interval BigOperators Matrix.Norms.Elementwise

namespace NavierStokes.SmoothExponentialMomentMatrix

/-- Primitive data on an open parameter domain. Logarithmic-coordinate support
intervals may lie anywhere on the real line. -/
structure Family (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (U : Set E) where
  exponent : E → Fin n → ℝ
  lower : E → Fin n → ℝ
  upper : E → Fin n → ℝ
  bump : E → Fin n → ℝ → ℝ
  exponent_smooth : ∀ i, ContDiffOn ℝ ∞ (fun p => exponent p i) U
  lower_continuous : ∀ j, ContinuousOn (fun p => lower p j) U
  upper_continuous : ∀ j, ContinuousOn (fun p => upper p j) U
  bump_smooth : ∀ j, ContDiffOn ℝ ∞ (fun z : E × ℝ => bump z.1 j z.2) (U ×ˢ univ)
  exponent_injective : ∀ p ∈ U, Injective (exponent p)
  separated : ∀ p ∈ U, ∀ i j, i < j → upper p i < lower p j
  bump_nonnegative : ∀ p ∈ U, ∀ j t, 0 ≤ bump p j t
  bump_nonzero : ∀ p ∈ U, ∀ j, ∃ t, bump p j t ≠ 0
  bump_support : ∀ p ∈ U, ∀ j, support (bump p j) ⊆ Icc (lower p j) (upper p j)

namespace Family

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} {U : Set E} (D : Family E n U)

/-- Actual integrated exponential weights against the given bump profiles. -/
def matrix (p : E) : Matrix (Fin n) (Fin n) ℝ :=
  ExponentialMomentMatrix.expBumpMomentMatrix (D.exponent p) (D.bump p)

theorem integrand_contDiffOn (i j : Fin n) :
    ContDiffOn ℝ ∞
      (fun z : E × ℝ => Real.exp (D.exponent z.1 i * z.2) * D.bump z.1 j z.2)
      (U ×ˢ univ) := by
  have he : ContDiffOn ℝ ∞ (fun z : E × ℝ => D.exponent z.1 i) (U ×ˢ univ) :=
    (D.exponent_smooth i).comp contDiffOn_fst (fun z hz => hz.1)
  exact (he.mul contDiffOn_snd).exp.mul (D.bump_smooth j)

theorem matrix_contDiffOn [ProperSpace E] (hU : IsOpen U) :
    ContDiffOn ℝ ∞ D.matrix U := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  apply SmoothPowerMomentMatrix.integral_contDiffOn_of_moving_support U hU _
    (D.integrand_contDiffOn i j) (fun p => D.lower p j) (fun p => D.upper p j)
    (D.lower_continuous j) (D.upper_continuous j)
  intro p hp t ht
  apply D.bump_support p hp j
  intro hb
  exact ht (by dsimp only; rw [hb, mul_zero])

theorem matrix_det_ne_zero (p : E) (hp : p ∈ U) : (D.matrix p).det ≠ 0 := by
  apply ExponentialMomentMatrix.expBumpMomentMatrix_det_ne_zero
    (D.exponent p) (D.lower p) (D.upper p) (D.bump p)
    (D.exponent_injective p hp) (D.separated p hp)
  · intro j
    exact contDiffOn_univ.mp ((D.bump_smooth j).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun t _ => ⟨hp, mem_univ t⟩)) |>.continuous
  · exact D.bump_nonnegative p hp
  · exact D.bump_nonzero p hp
  · exact D.bump_support p hp

theorem matrix_inverse_contDiffOn [ProperSpace E] (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (fun p => (D.matrix p)⁻¹) U :=
  SmoothPowerMomentMatrix.inverse_contDiffOn D.matrix
    (D.matrix_contDiffOn hU) D.matrix_det_ne_zero

/-- Every full parameter jet of the actual inverse has a uniform compact bound. -/
theorem compact_inverse_jet_bound [ProperSpace E] (hU : IsOpen U)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U) (m : ℕ) :
    ∃ C ≥ 0, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ m (fun q => (D.matrix q)⁻¹) p‖ ≤ C := by
  have hj : ContinuousOn (iteratedFDeriv ℝ m (fun q => (D.matrix q)⁻¹)) U := by
    intro p hp
    exact (((D.matrix_inverse_contDiffOn hU).contDiffAt (hU.mem_nhds hp)).iteratedFDeriv_right
      (m := 0) (by simp)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hj.mono hKU)
  exact ⟨max C 0, le_max_right _ _, fun p hp => (hC p hp).trans (le_max_left _ _)⟩

/-- One common constant controls all inverse derivatives up to a fixed order. -/
theorem compact_inverse_jets_bound [ProperSpace E] (hU : IsOpen U)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U) (m : ℕ) :
    ∃ C ≥ 0, ∀ k ≤ m, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k (fun q => (D.matrix q)⁻¹) p‖ ≤ C := by
  choose C hC hbound using fun k : Fin (m + 1) =>
    D.compact_inverse_jet_bound hU K hK hKU k.val
  refine ⟨∑ k, C k, Finset.sum_nonneg (fun k _ => hC k), ?_⟩
  intro k hk p hp
  exact (hbound ⟨k, by omega⟩ p hp).trans
    (Finset.single_le_sum (fun t _ => hC t)
      (Finset.mem_univ (⟨k, by omega⟩ : Fin (m + 1))))

end Family
end NavierStokes.SmoothExponentialMomentMatrix

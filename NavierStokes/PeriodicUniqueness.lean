import Mathlib.Analysis.Calculus.TangentCone.Prod
import NavierStokes.ProblemStatement
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Classical uniqueness for periodic Navier--Stokes fields

The differential operators are those of `ProblemStatement`. The energy
estimate is derived from the equations and periodic integration by parts.
-/
/-! Merged from `NavierStokes.PeriodicIntegration` (in a section, so its `open`s cannot leak). -/
section
/-!
# Integration of periodic fields on the unit cube

The integral is product Lebesgue measure in the usual three coordinates, pulled
back along the standard continuous linear equivalence to Euclidean space.
Integration by parts is derived from Mathlib's proved box divergence theorem.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology

namespace NavierStokes.PeriodicIntegration

open ProblemStatement

abbrev Coords := Fin 3 → ℝ

def toSpace : Coords ≃L[ℝ] Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm

def cube : Set Coords := Icc 0 1

def cubeMeasure : Measure Coords := volume.restrict cube

instance : IsFiniteMeasure cubeMeasure := by
  change IsFiniteMeasure (volume.restrict (Icc (0 : Coords) 1))
  exact isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne

def cubeIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Space → E) : E := ∫ y, f (toSpace y) ∂cubeMeasure

def UnitPeriods {E : Type*} (f : Space → E) : Prop :=
  ∀ x i, f (x + coordinateVector i) = f x

def spatialPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (f : Space → E) (x : Space) : E :=
  fderiv ℝ f x (coordinateVector i)

@[simp] theorem toSpace_apply (y : Coords) (i : Fin 3) : toSpace y i = y i := rfl

@[simp] theorem toSpace_single (i : Fin 3) :
    toSpace (Pi.single i 1) = coordinateVector i := rfl

theorem continuous_partial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hf : ContDiff ℝ 1 f) (i : Fin 3) : Continuous (spatialPartial i f) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem integrable_cube {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hf : Continuous f) : Integrable (fun y => f (toSpace y)) cubeMeasure :=
  (hf.comp toSpace.continuous).integrableOn_Icc

@[simp] theorem cubeIntegral_zero : cubeIntegral (fun _ : Space => (0 : ℝ)) = 0 := by
  simp [cubeIntegral]

theorem cubeIntegral_add {f g : Space → ℝ} (hf : Continuous f) (hg : Continuous g) :
    cubeIntegral (fun x => f x + g x) = cubeIntegral f + cubeIntegral g := by
  exact integral_add (integrable_cube hf) (integrable_cube hg)

theorem cubeIntegral_sub {f g : Space → ℝ} (hf : Continuous f) (hg : Continuous g) :
    cubeIntegral (fun x => f x - g x) = cubeIntegral f - cubeIntegral g := by
  exact integral_sub (integrable_cube hf) (integrable_cube hg)

theorem cubeIntegral_neg (f : Space → ℝ) :
    cubeIntegral (fun x => -f x) = -cubeIntegral f := by
  exact integral_neg _

theorem cubeIntegral_const_mul (c : ℝ) (f : Space → ℝ) :
    cubeIntegral (fun x => c * f x) = c * cubeIntegral f := by
  exact integral_const_mul _ _

theorem cubeIntegral_sum {ι : Type*} (s : Finset ι) (f : ι → Space → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    cubeIntegral (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, cubeIntegral (f i) := by
  exact MeasureTheory.integral_finsetSum s (fun i hi => integrable_cube (hf i hi))

theorem cubeIntegral_nonneg {f : Space → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ cubeIntegral f := integral_nonneg fun y => hf (toSpace y)



theorem cubeIntegral_mono_on_cube {f g : Space → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ y ∈ cube, f (toSpace y) ≤ g (toSpace y)) : cubeIntegral f ≤ cubeIntegral g := by
  apply integral_mono_ae (integrable_cube hf) (integrable_cube hg)
  filter_upwards [ae_restrict_mem (show MeasurableSet cube from measurableSet_Icc)] with y hy
  exact hfg y hy

private theorem insertNth_one_eq (i : Fin 3) (y : Fin 2 → ℝ) :
    i.insertNth (1 : ℝ) y = (i.insertNth (0 : ℝ) y : Coords) + Pi.single i (1 : ℝ) := by
  ext k
  by_cases hk : k = i
  · subst k
    simp
  · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
    simp

private theorem coord_partial_eq {f : Space → ℝ} (hf : ContDiff ℝ 1 f)
    (i : Fin 3) (y : Coords) :
    fderiv ℝ (fun z : Coords => f (toSpace z)) y (Pi.single i 1) =
      spatialPartial i f (toSpace y) := by
  have hd := ((hf.differentiable (by norm_num) (toSpace y)).hasFDerivAt.comp y
    toSpace.hasFDerivAt).fderiv
  change fderiv ℝ (f ∘ toSpace) y (Pi.single i 1) = _
  rw [hd]
  rfl

/-- A genuine coordinate derivative integrates to zero for a `C¹` unit-periodic field. -/
theorem cubeIntegral_partial_eq_zero {f : Space → ℝ} (hf : ContDiff ℝ 1 f)
    (hp : UnitPeriods f) (i : Fin 3) : cubeIntegral (spatialPartial i f) = 0 := by
  let g : Coords → ℝ := fun y => f (toSpace y)
  have hg : ContDiff ℝ 1 g := hf.comp toSpace.contDiff
  let F : Fin 3 → Coords → ℝ := fun k y => if k = i then g y else 0
  let F' : Fin 3 → Coords → Coords →L[ℝ] ℝ :=
    fun k y => if k = i then fderiv ℝ g y else 0
  have hsum (y : Coords) :
      (∑ k : Fin 3, F' k y (Pi.single k 1)) = fderiv ℝ g y (Pi.single i 1) := by
    rw [Finset.sum_eq_single i]
    · simp [F']
    · intro k _ hki
      simp [F', hki]
    · intro hi
      exact (hi (Finset.mem_univ _)).elim
  have Hc : ∀ k, ContinuousOn (F k) (Icc (0 : Coords) 1) := by
    intro k
    by_cases hk : k = i
    · simpa [F, hk] using hg.continuous.continuousOn
    · simpa [F, hk] using (continuous_const : Continuous (fun _ : Coords => (0 : ℝ))).continuousOn
  have Hd : ∀ y ∈ (univ.pi fun k : Fin 3 => Ioo ((0 : Coords) k) ((1 : Coords) k)) \ ∅,
      ∀ k, HasFDerivAt (F k) (F' k y) y := by
    intro y _ k
    by_cases hk : k = i
    · simpa [F, F', hk] using (hg.differentiable (by norm_num) y).hasFDerivAt
    · simpa [F, F', hk] using (hasFDerivAt_const (0 : ℝ) y)
  have Hi : IntegrableOn (fun y => ∑ k : Fin 3, F' k y (Pi.single k 1))
      (Icc (0 : Coords) 1) := by
    simp_rw [hsum]
    have hc : Continuous (fun y : Coords => fderiv ℝ g y (Pi.single i 1)) :=
      (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact hc.integrableOn_Icc
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable'
    (n := 2) (E := ℝ) (0 : Coords) 1 (by intro k; exact zero_le_one)
    F F' ∅ countable_empty Hc Hd Hi
  have hboundary : ∀ k : Fin 3, ∀ y : Fin 2 → ℝ,
      F k (k.insertNth 1 y) = F k (k.insertNth 0 y) := by
    intro k y
    by_cases hk : k = i
    · subst k
      simp only [F, ite_eq_left rfl, g]
      rw [insertNth_one_eq, map_add, toSpace_single]
      exact hp _ i
    · simp [F, hk]
  have hzero : (∫ y in Icc (0 : Coords) 1,
      fderiv ℝ g y (Pi.single i 1)) = 0 := by
    simpa [hsum, hboundary] using hdiv
  change (∫ y in Icc (0 : Coords) 1, spatialPartial i f (toSpace y)) = 0
  simpa only [g, coord_partial_eq hf i] using hzero

theorem partial_mul {f g : Space → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (i : Fin 3) (x : Space) :
    spatialPartial i (fun y => f y * g y) x =
      f x * spatialPartial i g x + g x * spatialPartial i f x := by
  simp only [spatialPartial, fderiv_fun_mul (hf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x),
    _root_.add_apply, _root_.smul_apply, smul_eq_mul]

/-- Integration by parts for actual coordinate partial derivatives on the unit torus. -/
theorem cubeIntegral_mul_partial {f g : Space → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (hpf : UnitPeriods f) (hpg : UnitPeriods g) (i : Fin 3) :
    cubeIntegral (fun x => f x * spatialPartial i g x) =
      -cubeIntegral (fun x => g x * spatialPartial i f x) := by
  have hp : UnitPeriods (fun x => f x * g x) := by
    intro x k
    change f (x + coordinateVector k) * g (x + coordinateVector k) = f x * g x
    rw [hpf x k, hpg x k]
  have hz := cubeIntegral_partial_eq_zero (hf.mul hg) hp i
  have hmul : spatialPartial i (fun y => f y * g y) =
      fun x => f x * spatialPartial i g x + g x * spatialPartial i f x :=
    funext (partial_mul hf hg i)
  rw [hmul] at hz
  rw [cubeIntegral_add (hf.continuous.fun_mul (continuous_partial hg i))
    (hg.continuous.fun_mul (continuous_partial hf i))] at hz
  exact eq_neg_of_add_eq_zero_left hz

private theorem cube_subset_closure_interior : cube ⊆ closure (interior cube) := by
  have h : closure (interior cube) = cube := by
    simp only [cube, ← pi_univ_Icc, interior_pi_set (Set.toFinite univ), interior_Icc,
      closure_pi_set, Pi.zero_apply, Pi.one_apply, closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]
  exact h.symm.subset

/-- Zero integral of a continuous nonnegative field implies zero at every point
of the closed cube, including its faces. -/
theorem eq_zero_on_cube_of_nonneg_of_integral_eq_zero {f : Space → ℝ}
    (hf : Continuous f) (hn : ∀ x, 0 ≤ f x) (hz : cubeIntegral f = 0) :
    ∀ y ∈ cube, f (toSpace y) = 0 := by
  have hae : (fun y => f (toSpace y)) =ᵐ[cubeMeasure] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun y => hn (toSpace y)) (integrable_cube hf)).mp hz
  exact Measure.eqOn_of_ae_eq hae (hf.comp toSpace.continuous).continuousOn
    continuousOn_const cube_subset_closure_interior

theorem eq_zero_on_cube_of_integral_norm_sq_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : Space → E}
    (hu : Continuous u) (hz : cubeIntegral (fun x => ‖u x‖ ^ 2) = 0) :
    ∀ y ∈ cube, u (toSpace y) = 0 := by
  have h := eq_zero_on_cube_of_nonneg_of_integral_eq_zero (hu.norm.pow 2)
    (fun _ => sq_nonneg _) hz
  intro y hy
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (h y hy))

section TimeDependent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {I : Set ℝ} {F : ℝ × Space → E}

omit [NormedSpace ℝ E] in
private theorem continuous_space_slice
    (hF : ContinuousOn F (I ×ˢ (univ : Set Space))) {t : ℝ} (ht : t ∈ I) :
    Continuous (fun x : Space => F (t, x)) := by
  rw [← continuousOn_univ]
  exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ _ => ⟨ht, mem_univ _⟩)

omit [NormedSpace ℝ E] in
private theorem continuousOn_time_slice
    (hF : ContinuousOn F (I ×ˢ (univ : Set Space))) (x : Space) :
    ContinuousOn (fun t : ℝ => F (t, x)) I :=
  hF.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ ht => ⟨ht, mem_univ _⟩)

omit [NormedSpace ℝ E] in
private theorem continuousOn_time_cube
    (hF : ContinuousOn F (I ×ˢ (univ : Set Space))) :
    ContinuousOn (fun z : ℝ × Coords => F (z.1, toSpace z.2)) (I ×ˢ cube) :=
  hF.comp (continuous_fst.prodMk (toSpace.continuous.comp continuous_snd)).continuousOn
    (fun _ hz => ⟨hz.1, mem_univ _⟩)

/-- Joint continuity on a compact time interval gives continuity of the actual
cube integral, including at the endpoints. -/
theorem cubeIntegral_continuousOn (hI : IsCompact I)
    (hF : ContinuousOn F (I ×ˢ (univ : Set Space))) :
    ContinuousOn (fun t => cubeIntegral (fun x => F (t, x))) I := by
  obtain ⟨C, hC⟩ := (hI.prod (show IsCompact cube from isCompact_Icc)).exists_bound_of_continuousOn
    (continuousOn_time_cube hF)
  unfold cubeIntegral
  apply continuousOn_of_dominated (bound := fun _ : Coords => C)
  · intro t ht
    exact ((continuous_space_slice hF ht).comp toSpace.continuous).aestronglyMeasurable
  · intro t ht
    filter_upwards [ae_restrict_mem (show MeasurableSet cube from measurableSet_Icc)] with y hy
    exact hC (t, y) ⟨ht, hy⟩
  · exact integrable_const C
  · exact Eventually.of_forall fun y => continuousOn_time_slice hF (toSpace y)

theorem cubeIntegral_continuousOn_Icc {a b : ℝ}
    (hF : ContinuousOn F (Icc a b ×ˢ (univ : Set Space))) :
    ContinuousOn (fun t => cubeIntegral (fun x => F (t, x))) (Icc a b) :=
  cubeIntegral_continuousOn isCompact_Icc hF

/-- Compactness of the cube supplies the local integrable derivative majorant.
The derivative premise is the ordinary pointwise derivative of the integrand. -/
theorem hasDerivAt_cubeIntegral_of_hasDerivAt
    {G : ℝ × Space → E} (hI : IsOpen I)
    (hF : ContinuousOn F (I ×ˢ (univ : Set Space)))
    (hG : ContinuousOn G (I ×ˢ (univ : Set Space)))
    (hd : ∀ t ∈ I, ∀ x : Space, HasDerivAt (fun s => F (s, x)) (G (t, x)) t)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => cubeIntegral (fun x => F (s, x)))
      (cubeIntegral (fun x => G (t, x))) t := by
  obtain ⟨ε, hε, hεI⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hI.mem_nhds ht)
  have hcompact : IsCompact (Metric.closedBall t ε ×ˢ cube) :=
    (isCompact_closedBall t ε).prod (show IsCompact cube from isCompact_Icc)
  have hc : ContinuousOn (fun z : ℝ × Coords => G (z.1, toSpace z.2))
      (Metric.closedBall t ε ×ˢ cube) :=
    (continuousOn_time_cube hG).mono (Set.prod_mono hεI Subset.rfl)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hc
  unfold cubeIntegral
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (x₀ := t) (μ := cubeMeasure)
    (F := fun s y => F (s, toSpace y)) (F' := fun s y => G (s, toSpace y))
    (bound := fun _ : Coords => C) (Metric.ball_mem_nhds _ hε) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hI.mem_nhds ht] with s hs
    exact ((continuous_space_slice hF hs).comp toSpace.continuous).aestronglyMeasurable
  · exact integrable_cube (f := fun x : Space => F (t, x)) (continuous_space_slice hF ht)
  · exact ((continuous_space_slice hG ht).comp toSpace.continuous).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (show MeasurableSet cube from measurableSet_Icc)] with y hy
    intro s hs
    exact hC (s, y) ⟨Metric.ball_subset_closedBall hs, hy⟩
  · exact integrable_const C
  · exact Eventually.of_forall fun y s hs => hd s (hεI (Metric.ball_subset_closedBall hs)) (toSpace y)

/-- Differentiation under the cube integral for a jointly `C¹` field on an open
time domain. The integrated quantity is its actual time-slice derivative. -/
theorem hasDerivAt_cubeIntegral_of_contDiffOn (hI : IsOpen I)
    (hF : ContDiffOn ℝ 1 F (I ×ˢ (univ : Set Space))) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => cubeIntegral (fun x => F (s, x)))
      (cubeIntegral (fun x => deriv (fun s => F (s, x)) t)) t := by
  let G : ℝ × Space → E := fun z => fderiv ℝ F z (1, 0)
  have hprod : IsOpen (I ×ˢ (univ : Set Space)) := hI.prod isOpen_univ
  have hG : ContinuousOn G (I ×ˢ (univ : Set Space)) :=
    (hF.continuousOn_fderiv_of_isOpen hprod le_rfl).clm_apply continuousOn_const
  have hd : ∀ s ∈ I, ∀ x : Space,
      HasDerivAt (fun r => F (r, x)) (G (s, x)) s := by
    intro s hs x
    have hsx : (s, x) ∈ I ×ˢ (univ : Set Space) := ⟨hs, mem_univ x⟩
    have hfd : DifferentiableAt ℝ F (s, x) :=
      (hF.contDiffAt (hprod.mem_nhds hsx)).differentiableAt (by norm_num)
    exact hfd.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have heq : (fun x => deriv (fun s => F (s, x)) t) = fun x => G (t, x) :=
    funext fun x => (hd t ht x).deriv
  rw [heq]
  exact hasDerivAt_cubeIntegral_of_hasDerivAt hI hF.continuousOn hG hd ht

end TimeDependent

end NavierStokes.PeriodicIntegration
end


noncomputable section

open Set Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

namespace NavierStokes.PeriodicUniqueness

open ProblemStatement

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

private theorem infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)

noncomputable def slab (a b : ℝ) : Set SpaceTime := Icc a b ×ˢ univ

theorem spatial_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b t : ℝ} {u : SpaceTime → V} (hu : ContDiffOn ℝ ∞ u (slab a b))
    (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (fun x : Space => u (t, x)) :=
  hu.comp_contDiff (contDiff_const.prodMk contDiff_id)
    (fun x => show (t, x) ∈ slab a b from ⟨ht, mem_univ x⟩)

theorem smooth_at_interior {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b t : ℝ} {u : SpaceTime → V} (hu : ContDiffOn ℝ ∞ u (slab a b))
    (ht : t ∈ Ioo a b) (x : Space) : ContDiffAt ℝ ∞ u (t, x) :=
  hu.contDiffAt (prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) Filter.univ_mem)

theorem spatialDerivative_sub {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x))) (x : Space) :
    spatialDerivative (u - v) t x = spatialDerivative u t x - spatialDerivative v t x :=
  fderiv_fun_sub (hu.differentiable (by simp) x)
    (hv.differentiable (by simp) x)

theorem spatialDivergence_sub {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x))) (x : Space) :
    spatialDivergence (u - v) t x = spatialDivergence u t x - spatialDivergence v t x := by
  simp only [spatialDivergence, spatialDerivative_sub hu hv,
    _root_.sub_apply, PiLp.sub_apply, Finset.sum_sub_distrib]

theorem advection_difference {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x))) (x : Space) :
    advection u t x - advection v t x =
      spatialDerivative u t x ((u - v) (t, x)) +
        spatialDerivative (u - v) t x (v (t, x)) := by
  simp only [advection, spatialDerivative_sub hu hv, Pi.sub_apply,
    map_sub, _root_.sub_apply]
  abel

theorem spatialLaplacian_sub {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x))) (x : Space) :
    spatialLaplacian (u - v) t x = spatialLaplacian u t x - spatialLaplacian v t x := by
  unfold spatialLaplacian
  simp_rw [spatialDerivative_sub hu hv, _root_.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hdu := ((hu.fderiv_right infty_add_one_le).clm_apply
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space => coordinateVector i))).differentiable
      (by simp) x
  have hdv := ((hv.fderiv_right infty_add_one_le).clm_apply
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space => coordinateVector i))).differentiable
      (by simp) x
  dsimp only [spatialDerivative]
  rw [fderiv_fun_sub hdu hdv]
  rfl

theorem pressureGradient_sub {p q : PressureField} {t : ℝ}
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t, x))) (x : Space) :
    pressureGradient (p - q) t x = pressureGradient p t x - pressureGradient q t x := by
  unfold pressureGradient
  have hderiv := fderiv_fun_sub (hp.differentiable (by simp) x)
    (hq.differentiable (by simp) x)
  simp only [Pi.sub_apply, hderiv, _root_.sub_apply, sub_smul,
    Finset.sum_sub_distrib]

theorem temporalDerivative_sub {u v : VelocityField} {t : ℝ} {x : Space}
    (hu : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (hv : DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t) :
    temporalDerivative (u - v) t x = temporalDerivative u t x - temporalDerivative v t x := by
  unfold temporalDerivative
  rw [show (fun s => (u - v) (s, x)) = (fun s => u (s, x) - v (s, x)) from rfl,
    fderiv_fun_sub hu hv]
  rfl

/-- Subtract the actual Navier--Stokes residuals, retaining the favorable
transport decomposition `Du(w) + Dw(v)`. -/
theorem difference_equation {u v : VelocityField} {p q : PressureField} {t : ℝ} {x : Space}
    (hu : ContDiff ℝ ∞ (fun y : Space => u (t, y)))
    (hv : ContDiff ℝ ∞ (fun y : Space => v (t, y)))
    (hp : ContDiff ℝ ∞ (fun y : Space => p (t, y)))
    (hq : ContDiff ℝ ∞ (fun y : Space => q (t, y)))
    (htu : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (htv : DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t)
    (hNS : navierStokesResidual u p t x = navierStokesResidual v q t x) :
    temporalDerivative (u - v) t x = spatialLaplacian (u - v) t x -
      spatialDerivative u t x ((u - v) (t, x)) -
      spatialDerivative (u - v) t x (v (t, x)) - pressureGradient (p - q) t x := by
  have ha := advection_difference hu hv x
  rw [temporalDerivative_sub htu htv, spatialLaplacian_sub hu hv,
    pressureGradient_sub hp hq]
  unfold navierStokesResidual at hNS
  have heq := sub_eq_zero.mpr hNS
  rw [show temporalDerivative u t x + advection u t x - spatialLaplacian u t x +
      pressureGradient p t x -
      (temporalDerivative v t x + advection v t x - spatialLaplacian v t x +
        pressureGradient q t x) =
      temporalDerivative u t x - temporalDerivative v t x +
        (advection u t x - advection v t x) -
        (spatialLaplacian u t x - spatialLaplacian v t x) +
        (pressureGradient p t x - pressureGradient q t x) by abel, ha] at heq
  apply sub_eq_zero.mp
  convert! heq using 1
  abel

/-- The only indefinite energy term is controlled by the operator norm of
the first velocity gradient. -/
theorem nonlinear_energy_bound (A : Space →L[ℝ] Space) (w : Space) {B : ℝ}
    (hB : ‖A‖ ≤ B) : -⟪w, A w⟫_ℝ ≤ B * ‖w‖ ^ 2 := by
  calc
    -⟪w, A w⟫_ℝ ≤ |⟪w, A w⟫_ℝ| := neg_le_abs _
    _ ≤ ‖w‖ * ‖A w‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖w‖ * (‖A‖ * ‖w‖) := mul_le_mul_of_nonneg_left (A.le_opNorm w) (norm_nonneg w)
    _ ≤ ‖w‖ * (B * ‖w‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hB (norm_nonneg w)) (norm_nonneg w)
    _ = B * ‖w‖ ^ 2 := by ring

/-- The zero-initial-data Gronwall conclusion, proved by the integrating
factor and mean-value theorem. Only interior derivatives are required. -/
theorem gronwall_zero {a b K : ℝ} {E E' : ℝ → ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn E (Icc a b)) (hinitial : E a = 0)
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ E t)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo a b, E' t ≤ K * E t) :
    ∀ t ∈ Icc a b, E t = 0 := by
  let G : ℝ → ℝ := fun t => Real.exp (-K * t) * E t
  let G' : ℝ → ℝ := fun t => Real.exp (-K * t) * (E' t - K * E t)
  have hgcont : ContinuousOn G (Icc a b) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hcont
  have hgderiv (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt G (G' t) t := by
    have hexp := ((hasDerivAt_id t).const_mul (-K)).exp
    convert! hexp.mul (hderiv t ht) using 1
    dsimp [G, G']
    ring
  have hG : AntitoneOn G (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hgcont
    · intro t ht
      exact (hgderiv t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (sub_nonpos.mpr (hbound t (by simpa only [interior_Icc] using ht)))
  intro t ht
  have hle := hG ⟨le_rfl, hab⟩ ht ht.1
  have hGzero : G a = 0 := by simp [G, hinitial]
  rw [hGzero] at hle
  have hE : E t ≤ 0 := by
    dsimp only [G] at hle
    nlinarith [Real.exp_pos (-K * t)]
  exact le_antisymm hE (hnonneg t ht)

/-- The ordinary spatial derivative at a time endpoint is the restriction
of the joint within-derivative to spatial directions. -/
theorem spatialDerivative_eq_within_comp {a b t : ℝ} {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (ht : t ∈ Icc a b) (x : Space) :
    spatialDerivative u t x =
      (fderivWithin ℝ u (slab a b) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have hd := (hu.differentiableOn (by simp) (t, x) ⟨ht, mem_univ x⟩).hasFDerivWithinAt
  have hs := hd.comp x (s := univ) (hasFDerivAt_prodMk_right t x).hasFDerivWithinAt
    (fun y _ => show (t, y) ∈ slab a b from ⟨ht, mem_univ y⟩)
  have hs' : HasFDerivAt (fun y : Space => u (t, y))
      ((fderivWithin ℝ u (slab a b) (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space)) x := by
    simpa only [Function.comp_def, hasFDerivWithinAt_univ] using hs
  exact hs'.fderiv

/-- Compactness supplies the spatial-gradient bound used by the energy
estimate; it is a conclusion from smoothness, not an input to uniqueness. -/
theorem exists_gradient_bound {a b : ℝ} (hab : a < b) {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) {K : Set Space} (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc a b, ∀ x ∈ K, ‖spatialDerivative u t x‖ ≤ B := by
  have hs : UniqueDiffOn ℝ (slab a b) := (uniqueDiffOn_Icc hab).prod uniqueDiffOn_univ
  have hD := (hu.fderivWithin hs infty_add_one_le).continuousOn
  have hDK : ContinuousOn (fderivWithin ℝ u (slab a b)) (Icc a b ×ˢ K) :=
    hD.mono (fun z hz => ⟨hz.1, mem_univ z.2⟩)
  obtain ⟨B, hBpos, hB⟩ := ((isCompact_Icc.prod hK).image_of_continuousOn hDK).isBounded.exists_pos_norm_le
  refine ⟨B, hBpos, ?_⟩
  intro t ht x hx
  apply ContinuousLinearMap.opNorm_le_bound _ hBpos.le
  intro w
  rw [spatialDerivative_eq_within_comp hu ht x, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]
  calc
    ‖(fderivWithin ℝ u (slab a b) (t, x)) (0, w)‖ ≤
        ‖fderivWithin ℝ u (slab a b) (t, x)‖ * ‖((0 : ℝ), w)‖ :=
      (fderivWithin ℝ u (slab a b) (t, x)).le_opNorm _
    _ ≤ B * ‖((0 : ℝ), w)‖ := mul_le_mul_of_nonneg_right
      (hB _ ⟨(t, x), ⟨ht, hx⟩, rfl⟩) (norm_nonneg _)
    _ = B * ‖w‖ := by simp

/-- Reconstruction in the standard Euclidean coordinate basis. -/
theorem sum_coordinates (x : Space) :
    (∑ i : Fin 3, x i • coordinateVector i) = x := by
  apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
  ext j
  change (EuclideanSpace.proj j) (∑ i : Fin 3, x i • coordinateVector i) = x j
  simp only [map_sum, map_smul]
  simp [coordinateVector]

/-- Unit coordinate periods imply invariance under every integer lattice
translation; no quotient or fundamental-domain claim is assumed. -/
theorem periodic_lattice {W : Type*} {f : Space → W}
    (hf : ∀ i : Fin 3, Function.Periodic f (coordinateVector i))
    (n : Fin 3 → ℤ) : Function.Periodic f (∑ i : Fin 3, n i • coordinateVector i) := by
  have hsum (s : Finset (Fin 3)) : Function.Periodic f (∑ i ∈ s, n i • coordinateVector i) := by
    induction s using Finset.induction_on with
    | empty => simp [Function.Periodic]
    | @insert i s his ih =>
      simpa only [Finset.sum_insert his] using ((hf i).zsmul (n i)).add_period ih
  simpa using hsum Finset.univ

/-- Each point has a representative in the unit cube with the same value
under every function having the three unit coordinate periods. -/
theorem exists_cube_representative {W : Type*} {f : Space → W}
    (hf : ∀ i : Fin 3, Function.Periodic f (coordinateVector i)) (x : Space) :
    ∃ y : Space, (∀ i : Fin 3, y i ∈ Icc (0 : ℝ) 1) ∧ f y = f x := by
  let y : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i => Int.fract (x i))
  have hy : ∀ i : Fin 3, y i ∈ Icc (0 : ℝ) 1 := fun i =>
    ⟨Int.fract_nonneg (x i), (Int.fract_lt_one (x i)).le⟩
  refine ⟨y, hy, ?_⟩
  have hxy : x = y + ∑ i : Fin 3, (⌊x i⌋ : ℤ) • coordinateVector i := by
    apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
    ext j
    change x j = (EuclideanSpace.proj j) (y + ∑ i : Fin 3, (⌊x i⌋ : ℤ) • coordinateVector i)
    simp only [map_add, map_sum, map_zsmul]
    simp [y, coordinateVector, Int.fract_add_floor]
  have hp := periodic_lattice hf (fun i => ⌊x i⌋)
  rw [hxy]
  exact (hp y).symm

theorem periodic_fderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Space → V} (hp : ∀ x : Space, ∀ i : Fin 3, f (x + coordinateVector i) = f x)
    (x : Space) (i : Fin 3) :
    fderiv ℝ f (x + coordinateVector i) = fderiv ℝ f x := by
  rw [← fderiv_comp_add_right (coordinateVector i)]
  exact congrArg (fun g : Space → V => fderiv ℝ g x) (funext (fun y => hp y i))

theorem spatial_partial_contDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Space → V} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ f x (coordinateVector i)) :=
  (hf.fderiv_right infty_add_one_le).clm_apply contDiff_const

theorem component_contDiff {f : Space → Space} (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x => f x j) :=
  (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp hf

theorem fderiv_component {f : Space → Space} (hf : ContDiff ℝ ∞ f)
    (j : Fin 3) (x v : Space) :
    fderiv ℝ (fun y => f y j) x v = fderiv ℝ f x v j := by
  have h := ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp x
    (hf.differentiable (by simp) x).hasFDerivAt).fderiv
  exact congrArg (fun A : Space →L[ℝ] ℝ => A v) h

theorem fderiv_apply_eq_sum (f : Space → ℝ) (x v : Space) :
    fderiv ℝ f x v = ∑ i : Fin 3, v i * fderiv ℝ f x (coordinateVector i) := by
  conv_lhs => rw [← sum_coordinates v]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem fderiv_normsq {f : Space → Space} (hf : ContDiff ℝ ∞ f) (x v : Space) :
    fderiv ℝ (fun y => ‖f y‖ ^ 2) x v = 2 * ⟪f x, fderiv ℝ f x v⟫_ℝ := by
  rw [((hf.differentiable (by simp) x).hasFDerivAt.norm_sq).fderiv]
  simp

theorem fderiv_inner {f g : Space → Space} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x v : Space) :
    fderiv ℝ (fun y => ⟪f y, g y⟫_ℝ) x v =
      ⟪f x, fderiv ℝ g x v⟫_ℝ + ⟪fderiv ℝ f x v, g x⟫_ℝ := by
  rw [((hf.differentiable (by simp) x).hasFDerivAt.inner ℝ
    (hg.differentiable (by simp) x).hasFDerivAt).fderiv]
  rfl

/-- The pressure term paired with a vector is its scalar directional
derivative. This uses exactly the gradient definition in the target. -/
theorem inner_pressureGradient (p : PressureField) (t : ℝ) (x w : Space) :
    ⟪w, pressureGradient p t x⟫_ℝ = fderiv ℝ (fun y => p (t, y)) x w := by
  rw [fderiv_apply_eq_sum]
  simp only [pressureGradient, inner_sum, inner_smul_right, coordinateVector,
    EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem energy_density_derivative {u : VelocityField} {t : ℝ} {x : Space}
    (hu : DifferentiableAt ℝ (fun s => u (s, x)) t) :
    HasDerivAt (fun s : ℝ => ‖u (s, x)‖ ^ 2)
      (2 * ⟪u (t, x), temporalDerivative u t x⟫_ℝ) t :=
  hu.hasDerivAt.norm_sq

open PeriodicIntegration

theorem component_periodic {f : Space → Space} (hf : UnitPeriods f) (j : Fin 3) :
    UnitPeriods (fun x => f x j) := by
  intro x i
  exact congrArg (fun v : Space => v j) (hf x i)

theorem spatial_partial_periodic {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Space → V} (hf : UnitPeriods f) (i : Fin 3) : UnitPeriods (spatialPartial i f) := by
  intro x j
  exact congrArg (fun A : Space →L[ℝ] V => A (coordinateVector i)) (periodic_fderiv hf x j)

theorem normsq_periodic {f : Space → Space} (hf : UnitPeriods f) :
    UnitPeriods (fun x => ‖f x‖ ^ 2) := by
  intro x i
  exact congrArg (fun v : Space => ‖v‖ ^ 2) (hf x i)

/-- Scalar transport integration by parts, derived from the three
coordinate identities on the unit cube. -/
theorem cubeIntegral_fderiv_apply {f : Space → ℝ} {v : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v)
    (hpf : UnitPeriods f) (hpv : UnitPeriods v) :
    cubeIntegral (fun x => fderiv ℝ f x (v x)) =
      -cubeIntegral (fun x => f x * ∑ i : Fin 3, spatialPartial i v x i) := by
  have hleft : (fun x => fderiv ℝ f x (v x)) =
      (fun x => ∑ i : Fin 3, v x i * spatialPartial i f x) := by
    funext x
    exact fderiv_apply_eq_sum f x (v x)
  have hright : (fun x => f x * ∑ i : Fin 3, spatialPartial i v x i) =
      (fun x => ∑ i : Fin 3, f x * spatialPartial i v x i) := by
    funext x
    exact Finset.mul_sum _ _ _
  rw [hleft, hright]
  dsimp only [spatialPartial]
  rw [cubeIntegral_sum Finset.univ _ (fun i _ =>
      (component_contDiff hv i).continuous.fun_mul (spatial_partial_contDiff hf i).continuous),
    cubeIntegral_sum Finset.univ _ (fun i _ =>
      hf.continuous.fun_mul (component_contDiff (spatial_partial_contDiff hv i) i).continuous),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := cubeIntegral_mul_partial ((component_contDiff hv i).of_le (nat_le_infty 1))
    (hf.of_le (nat_le_infty 1)) (component_periodic hpv i) hpf i
  simpa only [spatialPartial, fderiv_component hv] using h

theorem cubeIntegral_fderiv_apply_zero {f : Space → ℝ} {v : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v)
    (hpf : UnitPeriods f) (hpv : UnitPeriods v)
    (hdiv : ∀ x, (∑ i : Fin 3, spatialPartial i v x i) = 0) :
    cubeIntegral (fun x => fderiv ℝ f x (v x)) = 0 := by
  rw [cubeIntegral_fderiv_apply hf hv hpf hpv]
  simp only [hdiv, mul_zero, cubeIntegral_zero, neg_zero]

/-- Divergence-free transport has zero contribution to the energy. -/
theorem cubeIntegral_transport_energy_zero {w v : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hv : ContDiff ℝ ∞ v)
    (hpw : UnitPeriods w) (hpv : UnitPeriods v)
    (hdiv : ∀ x, (∑ i : Fin 3, spatialPartial i v x i) = 0) :
    cubeIntegral (fun x => ⟪w x, fderiv ℝ w x (v x)⟫_ℝ) = 0 := by
  have h := cubeIntegral_fderiv_apply_zero (hw.norm_sq ℝ) hv (normsq_periodic hpw) hpv hdiv
  have hfun : (fun x => fderiv ℝ (fun y => ‖w y‖ ^ 2) x (v x)) =
      (fun x => 2 * ⟪w x, fderiv ℝ w x (v x)⟫_ℝ) := by
    funext x
    exact fderiv_normsq hw x (v x)
  rw [hfun, cubeIntegral_const_mul] at h
  linarith

/-- Vector integration by parts follows from the scalar derivative of
the Euclidean inner product; it is not assumed as an energy identity. -/
theorem cubeIntegral_inner_partial {f g : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : UnitPeriods f) (hpg : UnitPeriods g) (i : Fin 3) :
    cubeIntegral (fun x => ⟪f x, spatialPartial i g x⟫_ℝ) =
      -cubeIntegral (fun x => ⟪spatialPartial i f x, g x⟫_ℝ) := by
  have hp : UnitPeriods (fun x => ⟪f x, g x⟫_ℝ) := by
    intro x j
    change ⟪f (x + coordinateVector j), g (x + coordinateVector j)⟫_ℝ = _
    rw [hpf x j, hpg x j]
  have h := cubeIntegral_partial_eq_zero ((hf.inner ℝ hg).of_le (nat_le_infty 1)) hp i
  have hfun : spatialPartial i (fun x => ⟪f x, g x⟫_ℝ) =
      (fun x => ⟪f x, spatialPartial i g x⟫_ℝ + ⟪spatialPartial i f x, g x⟫_ℝ) := by
    funext x
    exact fderiv_inner hf hg x (coordinateVector i)
  rw [hfun] at h
  dsimp only [spatialPartial] at h ⊢
  rw [cubeIntegral_add
    (hf.inner ℝ (spatial_partial_contDiff hg i)).continuous
    ((spatial_partial_contDiff hf i).inner ℝ hg).continuous] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The viscosity term is minus the actual integrated sum of squared
coordinate derivatives of the difference field. -/
theorem cubeIntegral_laplacian_energy {w : VelocityField} {t : ℝ}
    (hw : ContDiff ℝ ∞ (fun x : Space => w (t, x)))
    (hpw : UnitPeriods (fun x : Space => w (t, x))) :
    cubeIntegral (fun x => ⟪w (t, x), spatialLaplacian w t x⟫_ℝ) =
      -(∑ i : Fin 3, cubeIntegral (fun x => ‖spatialPartial i (fun y => w (t, y)) x‖ ^ 2)) := by
  have hsum : cubeIntegral (fun x => ⟪w (t, x), spatialLaplacian w t x⟫_ℝ) =
      ∑ i : Fin 3, cubeIntegral (fun x =>
        ⟪w (t, x), spatialPartial i (spatialPartial i (fun y => w (t, y))) x⟫_ℝ) := by
    simp only [spatialLaplacian, inner_sum]
    exact cubeIntegral_sum Finset.univ _ (fun i _ =>
      (hw.inner ℝ (spatial_partial_contDiff (spatial_partial_contDiff hw i) i)).continuous)
  rw [hsum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold spatialPartial
  simpa only [spatialPartial, real_inner_self_eq_norm_sq] using
    cubeIntegral_inner_partial hw (spatial_partial_contDiff hw i) hpw
      (spatial_partial_periodic hpw i) i

/-- Pressure has zero energy contribution when the difference velocity
is divergence free. -/
theorem cubeIntegral_pressure_energy_zero {w : VelocityField} {p : PressureField} {t : ℝ}
    (hw : ContDiff ℝ ∞ (fun x : Space => w (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hpw : UnitPeriods (fun x : Space => w (t, x)))
    (hpp : UnitPeriods (fun x : Space => p (t, x)))
    (hdiv : ∀ x, spatialDivergence w t x = 0) :
    cubeIntegral (fun x => ⟪w (t, x), pressureGradient p t x⟫_ℝ) = 0 := by
  have hfun : (fun x => ⟪w (t, x), pressureGradient p t x⟫_ℝ) =
      (fun x => fderiv ℝ (fun y => p (t, y)) x (w (t, x))) := by
    funext x
    exact inner_pressureGradient p t x (w (t, x))
  rw [hfun]
  exact cubeIntegral_fderiv_apply_zero hp hw hpp hpw hdiv

theorem spatialLaplacian_contDiff {w : VelocityField} {t : ℝ}
    (hw : ContDiff ℝ ∞ (fun x : Space => w (t, x))) :
    ContDiff ℝ ∞ (spatialLaplacian w t) := by
  change ContDiff ℝ ∞ (fun x => ∑ i : Fin 3,
    spatialPartial i (spatialPartial i (fun y => w (t, y))) x)
  exact ContDiff.sum fun i _ => spatial_partial_contDiff (spatial_partial_contDiff hw i) i

theorem pressureGradient_contDiff {p : PressureField} {t : ℝ}
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x))) :
    ContDiff ℝ ∞ (pressureGradient p t) := by
  change ContDiff ℝ ∞ (fun x => ∑ i : Fin 3,
    spatialPartial i (fun y => p (t, y)) x • coordinateVector i)
  exact ContDiff.sum fun i _ => (spatial_partial_contDiff hp i).smul contDiff_const

theorem unitPeriods_sub {V : Type*} [Sub V] {f g : Space → V}
    (hf : UnitPeriods f) (hg : UnitPeriods g) : UnitPeriods (f - g) := by
  intro x i
  change f (x + coordinateVector i) - g (x + coordinateVector i) = f x - g x
  rw [hf x i, hg x i]

/-- Squared `L²` distance, using the actual unit-cube Lebesgue integral. -/
noncomputable def energy (u v : VelocityField) (t : ℝ) : ℝ :=
  cubeIntegral (fun x => ‖(u - v) (t, x)‖ ^ 2)

noncomputable def energyRate (u v : VelocityField) (t : ℝ) : ℝ :=
  cubeIntegral (fun x => 2 * ⟪(u - v) (t, x), temporalDerivative (u - v) t x⟫_ℝ)

noncomputable def dissipation (w : VelocityField) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, cubeIntegral (fun x => ‖spatialPartial i (fun y => w (t, y)) x‖ ^ 2)

noncomputable def coupling (u w : VelocityField) (t : ℝ) : ℝ :=
  cubeIntegral (fun x => ⟪w (t, x), spatialDerivative u t x (w (t, x))⟫_ℝ)

theorem energy_nonneg (u v : VelocityField) (t : ℝ) : 0 ≤ energy u v t :=
  cubeIntegral_nonneg (fun _ => sq_nonneg _)

theorem dissipation_nonneg (w : VelocityField) (t : ℝ) : 0 ≤ dissipation w t :=
  Finset.sum_nonneg (fun _ _ => cubeIntegral_nonneg (fun _ => sq_nonneg _))

/-- The exact difference-energy balance, derived from the actual PDE,
pressure cancellation, divergence-free transport, and viscous integration
by parts. No energy inequality is an input. -/
theorem energy_balance {u v : VelocityField} {p q : PressureField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t, x)))
    (hpu : UnitPeriods (fun x : Space => u (t, x)))
    (hpv : UnitPeriods (fun x : Space => v (t, x)))
    (hpp : UnitPeriods (fun x : Space => p (t, x)))
    (hpq : UnitPeriods (fun x : Space => q (t, x)))
    (hdu : ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ x, spatialDivergence v t x = 0)
    (htu : ∀ x, DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (htv : ∀ x, DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t)
    (hNS : ∀ x, navierStokesResidual u p t x = navierStokesResidual v q t x) :
    energyRate u v t = -2 * dissipation (u - v) t - 2 * coupling u (u - v) t := by
  have hw : ContDiff ℝ ∞ (fun x : Space => (u - v) (t, x)) := hu.sub hv
  have hpw : UnitPeriods (fun x : Space => (u - v) (t, x)) := unitPeriods_sub hpu hpv
  have hdw : ∀ x, spatialDivergence (u - v) t x = 0 := by
    intro x
    rw [spatialDivergence_sub hu hv, hdu x, hdv x, sub_self]
  have hL := (hw.inner ℝ (spatialLaplacian_contDiff hw)).continuous
  have hN := (hw.inner ℝ ((hu.fderiv_right infty_add_one_le).clm_apply hw)).continuous
  have hT := (hw.inner ℝ ((hw.fderiv_right infty_add_one_le).clm_apply hv)).continuous
  have hP := (hw.inner ℝ (pressureGradient_contDiff (p := p - q) (t := t) (hp.sub hq))).continuous
  have hEq : (fun x => ⟪(u - v) (t, x), temporalDerivative (u - v) t x⟫_ℝ) =
      (fun x => ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
        ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ -
        ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ -
        ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ) := by
    funext x
    rw [difference_equation hu hv hp hq (htu x) (htv x) (hNS x)]
    simp only [inner_sub_right]
  unfold energyRate
  rw [cubeIntegral_const_mul, hEq]
  change 2 * cubeIntegral (fun x =>
    ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
    ⟪(u - v) (t, x), fderiv ℝ (fun y => u (t, y)) x ((u - v) (t, x))⟫_ℝ -
    ⟪(u - v) (t, x), fderiv ℝ (fun y => (u - v) (t, y)) x (v (t, x))⟫_ℝ -
    ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ) = _
  rw [cubeIntegral_sub ((hL.fun_sub hN).fun_sub hT) hP, cubeIntegral_sub (hL.fun_sub hN) hT,
    cubeIntegral_sub hL hN, cubeIntegral_laplacian_energy hw hpw,
    cubeIntegral_transport_energy_zero hw hv hpw hpv hdv,
    cubeIntegral_pressure_energy_zero hw (hp.sub hq) hpw (unitPeriods_sub hpp hpq) hdw]
  simp only [sub_zero, dissipation, coupling, spatialDerivative]
  ring

/-- Integrating the pointwise nonlinear bound only needs a gradient bound
on the compact unit cube. -/
theorem neg_coupling_le_energy {u v : VelocityField} {t B : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hB : ∀ y ∈ cube, ‖spatialDerivative u t (toSpace y)‖ ≤ B) :
    -coupling u (u - v) t ≤ B * energy u v t := by
  have hw : ContDiff ℝ ∞ (fun x : Space => (u - v) (t, x)) := hu.sub hv
  unfold coupling energy
  rw [← cubeIntegral_neg, ← cubeIntegral_const_mul]
  apply cubeIntegral_mono_on_cube
    (hw.inner ℝ ((hu.fderiv_right infty_add_one_le).clm_apply hw)).continuous.neg
    (continuous_const.mul (hw.norm_sq ℝ).continuous)
  intro y hy
  exact nonlinear_energy_bound _ _ (hB y hy)

theorem energy_rate_le {u v : VelocityField} {p q : PressureField} {t B : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t, x)))
    (hpu : UnitPeriods (fun x : Space => u (t, x)))
    (hpv : UnitPeriods (fun x : Space => v (t, x)))
    (hpp : UnitPeriods (fun x : Space => p (t, x)))
    (hpq : UnitPeriods (fun x : Space => q (t, x)))
    (hdu : ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ x, spatialDivergence v t x = 0)
    (htu : ∀ x, DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (htv : ∀ x, DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t)
    (hNS : ∀ x, navierStokesResidual u p t x = navierStokesResidual v q t x)
    (hB : ∀ y ∈ cube, ‖spatialDerivative u t (toSpace y)‖ ≤ B) :
    energyRate u v t ≤ (2 * B) * energy u v t := by
  rw [energy_balance hu hv hp hq hpu hpv hpp hpq hdu hdv htu htv hNS]
  have hc := neg_coupling_le_energy hu hv hB
  have hd := dissipation_nonneg (u - v) t
  nlinarith

theorem time_differentiable_at_interior {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b t : ℝ} {u : SpaceTime → V} (hu : ContDiffOn ℝ ∞ u (slab a b))
    (ht : t ∈ Ioo a b) (x : Space) :
    DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t :=
  ((smooth_at_interior hu ht x).comp t
    (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)

theorem energy_continuousOn {a b : ℝ} {u v : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (hv : ContDiffOn ℝ ∞ v (slab a b)) :
    ContinuousOn (energy u v) (Icc a b) := by
  have hF : ContDiffOn ℝ ∞ (fun z : SpaceTime => ‖(u - v) z‖ ^ 2)
      (Icc a b ×ˢ univ) := (hu.sub hv).norm_sq ℝ
  exact cubeIntegral_continuousOn_Icc hF.continuousOn

/-- Differentiation under the genuine spatial integral is justified by
joint smoothness and compactness of the cube. -/
theorem energy_hasDerivAt {a b t : ℝ} {u v : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (hv : ContDiffOn ℝ ∞ v (slab a b))
    (ht : t ∈ Ioo a b) : HasDerivAt (energy u v) (energyRate u v t) t := by
  have hF : ContDiffOn ℝ 1 (fun z : SpaceTime => ‖(u - v) z‖ ^ 2)
      (Ioo a b ×ˢ univ) :=
    (((hu.sub hv).norm_sq ℝ).of_le (nat_le_infty 1)).mono
      (fun z hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩)
  have h := hasDerivAt_cubeIntegral_of_contDiffOn isOpen_Ioo hF ht
  have hrate : (fun x => deriv (fun s : ℝ => ‖(u - v) (s, x)‖ ^ 2) t) =
      (fun x => 2 * ⟪(u - v) (t, x), temporalDerivative (u - v) t x⟫_ℝ) := by
    funext x
    exact (energy_density_derivative
      (time_differentiable_at_interior (u := u - v) (hu.sub hv) ht x)).deriv
  rw [hrate] at h
  exact h

theorem energy_initial_zero {u v : VelocityField} {a : ℝ}
    (hinitial : ∀ x : Space, u (a, x) = v (a, x)) : energy u v a = 0 := by
  have hzero : (fun x => ‖(u - v) (a, x)‖ ^ 2) = (fun _ : Space => (0 : ℝ)) := by
    funext x
    simp only [Pi.sub_apply, hinitial x, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  unfold energy
  rw [hzero, cubeIntegral_zero]

/-- Zero squared `L²` difference implies equality everywhere, using
continuity on the cube and the explicitly proved periodic representatives. -/
theorem eq_of_energy_zero {u v : VelocityField} {t : ℝ}
    (hu : Continuous (fun x : Space => u (t, x)))
    (hv : Continuous (fun x : Space => v (t, x)))
    (hpu : UnitPeriods (fun x : Space => u (t, x)))
    (hpv : UnitPeriods (fun x : Space => v (t, x)))
    (hzero : energy u v t = 0) (x : Space) : u (t, x) = v (t, x) := by
  have hc := eq_zero_on_cube_of_integral_norm_sq_eq_zero (hu.sub hv) hzero
  have hpw : UnitPeriods (fun z : Space => (u - v) (t, z)) := unitPeriods_sub hpu hpv
  obtain ⟨z, hz, hzx⟩ := exists_cube_representative
    (f := fun z : Space => (u - v) (t, z)) (fun i y => hpw y i) x
  let y : Coords := toSpace.symm z
  have hy : y ∈ cube := by
    constructor
    · intro i
      exact (hz i).1
    · intro i
      exact (hz i).2
  have hzy : toSpace y = z := toSpace.apply_symm_apply z
  have hcz := hc y hy
  rw [hzy] at hcz
  exact sub_eq_zero.mp (hzx.symm.trans hcz)

/-- Classical uniqueness on a compact time interval for the exact periodic
Navier--Stokes equation of `ProblemStatement`, with viscosity one. Both
solutions have the same force and initial datum. The energy inequality,
uniform gradient bound, and spatial integration identities are conclusions
of the preceding proofs, not assumptions of this theorem. -/
theorem classical_uniqueness_on_Icc {a b : ℝ}
    {u v : VelocityField} {p q : PressureField} {f : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hv : ContDiffOn ℝ ∞ v (slab a b))
    (hp : ContDiffOn ℝ ∞ p (slab a b))
    (hq : ContDiffOn ℝ ∞ q (slab a b))
    (hpu : UnitSpatialPeriodsOn (Icc a b) u)
    (hpv : UnitSpatialPeriodsOn (Icc a b) v)
    (hpp : UnitSpatialPeriodsOn (Icc a b) p)
    (hpq : UnitSpatialPeriodsOn (Icc a b) q)
    (hdu : ∀ t ∈ Ioo a b, ∀ x : Space, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo a b, ∀ x : Space, spatialDivergence v t x = 0)
    (hNSu : ∀ t ∈ Ioo a b, ∀ x : Space, navierStokesResidual u p t x = f (t, x))
    (hNSv : ∀ t ∈ Ioo a b, ∀ x : Space, navierStokesResidual v q t x = f (t, x))
    (hinitial : ∀ x : Space, u (a, x) = v (a, x)) :
    ∀ t ∈ Icc a b, ∀ x : Space, u (t, x) = v (t, x) := by
  by_cases hab : a < b
  · have hcompact : IsCompact (toSpace '' cube) :=
      (show IsCompact cube from isCompact_Icc).image toSpace.continuous
    obtain ⟨B, _, hB⟩ := exists_gradient_bound hab hu hcompact
    have hbound : ∀ t ∈ Ioo a b, energyRate u v t ≤ (2 * B) * energy u v t := by
      intro t ht
      have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
      exact energy_rate_le (spatial_smooth hu ht') (spatial_smooth hv ht')
        (spatial_smooth hp ht') (spatial_smooth hq ht')
        (hpu t ht') (hpv t ht') (hpp t ht') (hpq t ht') (hdu t ht) (hdv t ht)
        (time_differentiable_at_interior hu ht) (time_differentiable_at_interior hv ht)
        (fun x => (hNSu t ht x).trans (hNSv t ht x).symm)
        (fun y hy => hB t ht' (toSpace y) ⟨y, hy, rfl⟩)
    have hzero := gronwall_zero hab.le (energy_continuousOn hu hv)
      (energy_initial_zero hinitial) (fun t _ => energy_nonneg u v t)
      (fun t ht => energy_hasDerivAt hu hv ht) hbound
    intro t ht x
    exact eq_of_energy_zero (spatial_smooth hu ht).continuous (spatial_smooth hv ht).continuous
      (hpu t ht) (hpv t ht) (hzero t ht) x
  · intro t ht x
    have ht' : t = a := le_antisymm (ht.2.trans (le_of_not_gt hab)) ht.1
    simpa only [ht'] using hinitial x

/-- Direct application to the exact candidate specification: any other
classical periodic solution with its force and zero initial velocity must
agree on every compact interval strictly before time one. The comparison
solution is not assumed to satisfy the candidate blow-up condition. -/
theorem candidate_unique_on_Icc {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : CandidateProperties u p f) {T : ℝ} (hT : T < 1)
    {v : VelocityField} {q : PressureField}
    (hv : ContDiffOn ℝ ∞ v (slab 0 T)) (hq : ContDiffOn ℝ ∞ q (slab 0 T))
    (hpv : UnitSpatialPeriodsOn (Icc (0 : ℝ) T) v)
    (hpq : UnitSpatialPeriodsOn (Icc (0 : ℝ) T) q)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space, spatialDivergence v t x = 0)
    (hNSv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space, navierStokesResidual v q t x = f (t, x))
    (hvzero : ∀ x : Space, v (0, x) = 0) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space, u (t, x) = v (t, x) := by
  have hsub : slab 0 T ⊆ preSingularDomain := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_lt hT⟩, hz.2⟩
  apply classical_uniqueness_on_Icc (h.velocity_smooth.mono hsub) hv
    (h.pressure_smooth.mono hsub) hq
  · intro t ht x i
    exact h.velocity_periodic t ⟨ht.1, ht.2.trans_lt hT⟩ x i
  · exact hpv
  · intro t ht x i
    exact h.pressure_periodic t ⟨ht.1, ht.2.trans_lt hT⟩ x i
  · exact hpq
  · intro t ht x
    exact h.divergence_free t ⟨ht.1.le, ht.2.trans hT⟩ x
  · exact hdv
  · intro t ht x
    exact h.navier_stokes t ⟨ht.1, ht.2.trans hT⟩ x
  · exact hNSv
  · intro x
    exact (h.zero_initial_velocity x).trans (hvzero x).symm

end NavierStokes.PeriodicUniqueness

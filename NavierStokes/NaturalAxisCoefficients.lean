import NavierStokes.AnalyticCoefficientBounds
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import NavierStokes.NaturalAxisRange
import NavierStokes.NaturalAxisBridge
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.FunProp

/-!
# The actual fixed coefficients of the natural-axis problem

The pressure comes from its proved holomorphic integral extension. A common
complex neighborhood is chosen by compactness and nonvanishing of the two
actual denominators. Every fixed field is then embedded in the same complete
space of compatible coefficient functions.
-/
/-! Merged from `NavierStokes.AnalyticPrimitive` (in a section, so its `open`s cannot leak). -/
section
/-!
# An actual holomorphic primitive on a convex open set

The primitive is the radial segment integral. Its derivative is proved by
differentiating under a uniformly dominated integral on a compact local product,
then applying the real fundamental theorem of calculus along the segment.
No disk containing the entire domain and no assumed primitive are required.
-/

noncomputable section

namespace NavierStokes.AnalyticPrimitive

open Set Filter MeasureTheory Metric
open scoped Topology Interval ContDiff

/-- Integration along the straight segment from zero to `z`. -/
def primitive (g : ℂ → ℂ) (z : ℂ) : ℂ := z * ∫ t in (0 : ℝ)..1, g ((t : ℂ) * z)

@[simp] theorem primitive_zero (g : ℂ → ℂ) : primitive g 0 = 0 := by
  simp [primitive]

theorem primitive_eq_integral (g : ℂ → ℂ) (z : ℂ) :
    primitive g z = ∫ t in (0 : ℝ)..1, z * g ((t : ℂ) * z) := by
  rw [intervalIntegral.integral_const_mul]
  rfl

theorem segment_mem {U : Set ℂ} (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (t : ℂ) * z ∈ U := by
  simpa only [Complex.real_smul] using hU.smul_mem_of_zero_mem h0 hz ht

theorem continuousOn_segment {U : Set ℂ} (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U)
    {g : ℂ → ℂ} (hg : ContinuousOn g U) {z : ℂ} (hz : z ∈ U) :
    ContinuousOn (fun t : ℝ => g ((t : ℂ) * z)) (Icc (0 : ℝ) 1) := by
  exact hg.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn
    (fun _ ht => segment_mem hU h0 hz ht)

/-- The complex derivative of the parameter-dependent integrand. -/
def integrandDerivative (g : ℂ → ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  g ((t : ℂ) * z) + ((t : ℂ) * z) * deriv g ((t : ℂ) * z)

theorem integrand_hasDerivAt {U : Set ℂ} (ho : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} {t : ℝ} (htz : (t : ℂ) * z ∈ U) :
    HasDerivAt (fun w : ℂ => w * g ((t : ℂ) * w)) (integrandDerivative g z t) z := by
  have hgd := (hg _ htz).differentiableAt (ho.mem_nhds htz)
  convert! (hasDerivAt_id z).mul (hgd.hasDerivAt.comp z
    ((hasDerivAt_id z).const_mul (t : ℂ))) using 1
  simp only [integrandDerivative, Function.comp_apply, id_eq, mul_one, one_mul]
  ring

theorem integrandDerivative_continuousOn_segment {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} (hz : z ∈ U) :
    ContinuousOn (integrandDerivative g z) (Icc (0 : ℝ) 1) := by
  exact (continuousOn_segment hU h0 hg.continuousOn hz).add
    ((Complex.continuous_ofReal.mul continuous_const).continuousOn.mul
      (continuousOn_segment hU h0 (hg.deriv ho).continuousOn hz))

/-- The same derivative integrand is the real derivative of `t*g(t*z)`. -/
theorem segment_product_hasDerivAt {U : Set ℂ} (ho : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} {t : ℝ} (htz : (t : ℂ) * z ∈ U) :
    HasDerivAt (fun s : ℝ => (s : ℂ) * g ((s : ℂ) * z))
      (integrandDerivative g z t) t := by
  have ht : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
    exact Complex.ofRealCLM.hasDerivAt (x := t)
  have hgd := (hg _ htz).differentiableAt (ho.mem_nhds htz)
  convert! ht.mul (hgd.hasDerivAt.comp t (ht.mul_const z)) using 1
  simp only [integrandDerivative, Function.comp_apply, one_mul]
  ring

theorem integral_integrandDerivative {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} (hz : z ∈ U) :
    (∫ t in (0 : ℝ)..1, integrandDerivative g z t) = g z := by
  have hint : IntervalIntegrable (integrandDerivative g z) volume 0 1 :=
    (integrandDerivative_continuousOn_segment ho hU h0 hg hz).intervalIntegrable_of_Icc
      (by norm_num : (0 : ℝ) ≤ 1)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => (s : ℂ) * g ((s : ℂ) * z))
    (f' := integrandDerivative g z) (a := 0) (b := 1)
    (fun t ht => segment_product_hasDerivAt ho hg
      (segment_mem hU h0 hz (by simpa only [uIcc_of_le zero_le_one] using ht))) hint
  simpa using he

/-- An actual holomorphic primitive on any convex open neighborhood of zero. -/
theorem hasDerivAt_primitive {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (primitive g) (g z) z := by
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (ho.mem_nhds hz)
  let K : Set (ℂ × ℝ) := closedBall z r ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := (isCompact_closedBall z r).prod isCompact_Icc
  have hm : Continuous (fun p : ℂ × ℝ => (p.2 : ℂ) * p.1) :=
    (Complex.continuous_ofReal.comp continuous_snd).mul continuous_fst
  have hmU : MapsTo (fun p : ℂ × ℝ => (p.2 : ℂ) * p.1) K U := by
    intro p hp
    exact segment_mem hU h0 (hrU hp.1) hp.2
  have hcont : ContinuousOn (fun p : ℂ × ℝ => integrandDerivative g p.1 p.2) K := by
    exact (hg.continuousOn.comp hm.continuousOn hmU).add
      (hm.continuousOn.mul ((hg.deriv ho).continuousOn.comp hm.continuousOn hmU))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  have hFint : ∀ w ∈ U, IntervalIntegrable (fun t : ℝ => w * g ((t : ℂ) * w))
      volume 0 1 := by
    intro w hw
    exact (continuousOn_const.mul
      (continuousOn_segment hU h0 hg.continuousOn hw)).intervalIntegrable_of_Icc (by norm_num)
  have hFmeas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable
      (fun t : ℝ => w * g ((t : ℂ) * w)) (volume.restrict (Ι (0 : ℝ) 1)) := by
    filter_upwards [Metric.ball_mem_nhds z hr] with w hw
    simpa only [uIoc_of_le zero_le_one] using
      (hFint w (hrU (ball_subset_closedBall hw))).aestronglyMeasurable
  have hDint : IntervalIntegrable (integrandDerivative g z) volume 0 1 :=
    (integrandDerivative_continuousOn_segment ho hU h0 hg hz).intervalIntegrable_of_Icc
      (by norm_num : (0 : ℝ) ≤ 1)
  have hDmeas : AEStronglyMeasurable (integrandDerivative g z)
      (volume.restrict (Ι (0 : ℝ) 1)) := by
    simpa only [uIoc_of_le zero_le_one] using hDint.aestronglyMeasurable
  have hbound : ∀ᵐ t : ℝ, t ∈ Ι (0 : ℝ) 1 → ∀ w ∈ ball z r,
      ‖integrandDerivative g w t‖ ≤ C := by
    filter_upwards [] with t
    intro ht w hw
    apply hC (w, t)
    exact ⟨ball_subset_closedBall hw,
      by simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht⟩
  have hdiff : ∀ᵐ t : ℝ, t ∈ Ι (0 : ℝ) 1 → ∀ w ∈ ball z r,
      HasDerivAt (fun v : ℂ => v * g ((t : ℂ) * v)) (integrandDerivative g w t) w := by
    filter_upwards [] with t
    intro ht w hw
    exact integrand_hasDerivAt ho hg (segment_mem hU h0
      (hrU (ball_subset_closedBall hw))
      (by simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht))
  have hd := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w t => w * g ((t : ℂ) * w)) (F' := integrandDerivative g)
    (bound := fun _ => C) (Metric.ball_mem_nhds _ hr) hFmeas (hFint z hz) hDmeas hbound
    intervalIntegrable_const hdiff).2
  rw [integral_integrandDerivative ho hU h0 hg hz] at hd
  simpa only [← primitive_eq_integral] using hd

theorem differentiableOn_primitive {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) : DifferentiableOn ℂ (primitive g) U := by
  intro z hz
  exact (hasDerivAt_primitive ho hU h0 hg hz).differentiableAt.differentiableWithinAt

theorem analyticOnNhd_primitive {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) : AnalyticOnNhd ℂ (primitive g) U :=
  (differentiableOn_primitive ho hU h0 hg).analyticOnNhd ho


/-- If the integrand extends a real function, its segment primitive extends
the corresponding real segment integral exactly. -/
theorem primitive_ofReal (g : ℂ → ℂ) (f : ℝ → ℝ)
    (hreal : ∀ x : ℝ, g x = (f x : ℂ)) (x : ℝ) :
    primitive g x = ((x * ∫ t in (0 : ℝ)..1, f (t * x) : ℝ) : ℂ) := by
  have heq : (fun t : ℝ => g ((t : ℂ) * (x : ℂ))) =
      fun t : ℝ => (f (t * x) : ℂ) := by
    funext t
    rw [← Complex.ofReal_mul, hreal]
  rw [primitive, heq, intervalIntegral.integral_ofReal, Complex.ofReal_mul]


/-- The normalized exponential built from the actual segment primitive. -/
def amplitude (g : ℂ → ℂ) (Λ C : ℂ) (z : ℂ) : ℂ :=
  Complex.exp (Λ * primitive g z) / C

@[simp] theorem amplitude_zero (g : ℂ → ℂ) (Λ C : ℂ) : amplitude g Λ C 0 = 1 / C := by
  simp [amplitude]









end NavierStokes.AnalyticPrimitive

end
end


noncomputable section

namespace NavierStokes.NaturalAxisCoefficients

open Set Metric Filter Complex
open scoped Topology ContDiff BigOperators
open AxisCoefficientSpace AnalyticCoefficientBounds

/-- A fixed, slightly enlarged real parameter interval. -/
def window : Window := ⟨-11 / 10, 11 / 10, by norm_num⟩

theorem original_interval_interior :
    Icc (-1 : ℝ) 1 ⊆ Ioo window.left window.right := by
  intro x hx
  dsimp [window]
  constructor <;> linarith [hx.1, hx.2]

def complexD (z : ℂ) : ℂ := 1 - z ^ 2
def complexL (h : ℝ) (z : ℂ) : ℂ := 1 - 2 * (h : ℂ) * z ^ 2
def complexU (j : ℝ) (z : ℂ) : ℂ := 4 * z + (j : ℂ)
def complexH (h j : ℝ) (z : ℂ) : ℂ :=
  (NaturalAxisData.D h : ℂ) * z + complexD z * complexU j z
def complexW (h j : ℝ) (z : ℂ) : ℂ :=
  1 - 4 * complexD z - 2 * (NaturalAxisData.D h : ℂ) * z * complexU j z
def denominator (h j σ : ℝ) (z : ℂ) : ℂ := complexH h j z ^ 2 + (σ : ℂ) ^ 2
def complexZ (h j : ℝ) (P : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(NaturalAxisData.A h : ℂ) * (1 - 2 * z * complexU j z) * complexU j z -
    complexH h j z * 4 - complexD z * deriv P z +
    4 * (NaturalAxisData.A h : ℂ) * z * P z
def complexChi (h j σ : ℝ) (z : ℂ) : ℂ :=
  complexH h j z ^ 2 / denominator h j σ z
def complexGradient (h j σ : ℝ) (z : ℂ) : ℂ :=
  -complexL h z * complexH h j z / denominator h j σ z
def realGradient (h j σ x : ℝ) : ℝ :=
  -NaturalAxisData.L h x * NaturalAxisData.H h j x /
    (NaturalAxisData.H h j x ^ 2 + σ ^ 2)

@[simp] theorem complexL_ofReal (h x : ℝ) :
    complexL h (x : ℂ) = (NaturalAxisData.L h x : ℂ) := by
  simp [complexL, NaturalAxisData.L]

@[simp] theorem complexH_ofReal (h j x : ℝ) :
    complexH h j (x : ℂ) = (NaturalAxisData.H h j x : ℂ) := by
  simp [complexH, complexD, complexU, NaturalAxisData.H, NaturalAxisData.d,
    NaturalAxisData.U]

@[simp] theorem denominator_ofReal (h j σ x : ℝ) :
    denominator h j σ (x : ℂ) = (NaturalAxisData.H h j x ^ 2 + σ ^ 2 : ℝ) := by
  simp [denominator]

@[simp] theorem complexGradient_ofReal (h j σ x : ℝ) :
    complexGradient h j σ (x : ℂ) = (realGradient h j σ x : ℂ) := by
  simp [complexGradient, realGradient, denominator]

theorem L_pos_on_window {h j : ℝ} (hp : NaturalAxisRange.Parameters h j)
    {x : ℝ} (hx : x ∈ window.interval) : 0 < NaturalAxisData.L h x := by
  have hx' : -(11 / 10 : ℝ) ≤ x ∧ x ≤ 11 / 10 := by
    simpa [window, Window.interval, neg_div] using hx
  have hs : x ^ 2 ≤ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx'.2) (show 0 ≤ x + 11 / 10 by linarith [hx'.1])]
  have hh := mul_le_mul_of_nonneg_left hs hp.h_pos.le
  dsimp [NaturalAxisData.L]
  nlinarith [hp.h_le]

theorem denominator_ne_zero_on_real (h j : ℝ) {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    denominator h j σ (x : ℂ) ≠ 0 := by
  rw [denominator_ofReal]
  exact_mod_cast ne_of_gt (add_pos_of_nonneg_of_pos
    (sq_nonneg (NaturalAxisData.H h j x)) (sq_pos_of_pos hσ))

/-- The open region where all fixed rational expressions and pressure are analytic. -/
def regularSet (h j σ : ℝ) : Set ℂ :=
  PressureDatum.strip ∩ {z | complexL h z ≠ 0} ∩ {z | denominator h j σ z ≠ 0}

theorem regularSet_open (h j σ : ℝ) : IsOpen (regularSet h j σ) := by
  have hL : Continuous (complexL h) := by unfold complexL; fun_prop
  have hden : Continuous (denominator h j σ) := by
    unfold denominator complexH complexD complexU
    fun_prop
  exact (PressureDatum.strip_open.inter (isOpen_ne_fun hL continuous_const)).inter
    (isOpen_ne_fun hden continuous_const)

theorem real_mem_regularSet {h j σ : ℝ} (hp : NaturalAxisRange.Parameters h j)
    (hσ : 0 < σ) {x : ℝ} (hx : x ∈ window.interval) :
    (x : ℂ) ∈ regularSet h j σ := by
  refine ⟨⟨PressureDatum.real_mem_strip x, ?_⟩, denominator_ne_zero_on_real h j hσ x⟩
  change complexL h (x : ℂ) ≠ 0
  rw [complexL_ofReal]
  exact_mod_cast (L_pos_on_window hp hx).ne'

theorem complexGradient_analytic (h j σ : ℝ) :
    AnalyticOnNhd ℂ (complexGradient h j σ) (regularSet h j σ) := by
  intro z hz
  have hden : denominator h j σ z ≠ 0 := hz.2
  change AnalyticAt ℂ (fun w => complexGradient h j σ w) z
  dsimp [complexGradient, denominator, complexH, complexD, complexU, complexL]
  fun_prop (disch := assumption)

inductive Field
  | one | eta | d | inverseL | uStar | uStarEta | wStar | hStar | zStar | chi | gradient
  deriving DecidableEq

instance : Fintype Field :=
  ⟨{.one, .eta, .d, .inverseL, .uStar, .uStarEta, .wStar, .hStar, .zStar, .chi, .gradient},
    by intro x; cases x <;> simp⟩

def complexField (h j σ : ℝ) (P : ℂ → ℂ) : Field → ℂ → ℂ
  | .one => fun _ => 1
  | .eta => fun z => z
  | .d => complexD
  | .inverseL => fun z => (complexL h z)⁻¹
  | .uStar => complexU j
  | .uStarEta => fun _ => 4
  | .wStar => complexW h j
  | .hStar => complexH h j
  | .zStar => complexZ h j P
  | .chi => complexChi h j σ
  | .gradient => complexGradient h j σ

def realField (h j σ : ℝ) (P : ℝ → ℝ) : Field → ℝ → ℝ
  | .one => fun _ => 1
  | .eta => fun x => x
  | .d => NaturalAxisData.d
  | .inverseL => fun x => (NaturalAxisData.L h x)⁻¹
  | .uStar => NaturalAxisData.U j
  | .uStarEta => fun _ => 4
  | .wStar => NaturalAxisData.W h j
  | .hStar => NaturalAxisData.H h j
  | .zStar => NaturalAxisData.Z h j P
  | .chi => NaturalAxisData.chi h j σ
  | .gradient => realGradient h j σ

theorem deriv_complexPressure_ofReal {g a : ℝ → ℝ} {cap : ℝ}
    (hp : PressureDatum.Admissible g a cap) (x : ℝ) :
    deriv (PressureDatum.complexPressure g a) (x : ℂ) =
      ((deriv (PressureDatum.pressure g a) x : ℝ) : ℂ) := by
  have hc := ((PressureDatum.complexPressure_analytic hp (x : ℂ)
    (PressureDatum.real_mem_strip x)).differentiableAt.hasDerivAt).comp_ofReal
  have hr := (PressureDatum.hasDerivAt_pressure hp x).differentiableAt.hasDerivAt.ofReal_comp
  have hc' : HasDerivAt (fun t : ℝ => (PressureDatum.pressure g a t : ℂ))
      (deriv (PressureDatum.complexPressure g a) (x : ℂ)) x := by
    simpa only [PressureDatum.complexPressure_ofReal] using hc
  exact hc'.unique hr

theorem complexField_ofReal {g a : ℝ → ℝ} {cap : ℝ}
    (hp : PressureDatum.Admissible g a cap) (h j σ : ℝ) (k : Field) (x : ℝ) :
    complexField h j σ (PressureDatum.complexPressure g a) k (x : ℂ) =
      (realField h j σ (PressureDatum.pressure g a) k x : ℂ) := by
  cases k <;>
    simp [complexField, realField, complexD, complexL, complexU, complexH, complexW,
      complexZ, complexChi, complexGradient, denominator, realGradient,
      NaturalAxisData.d, NaturalAxisData.L, NaturalAxisData.U, NaturalAxisData.H,
      NaturalAxisData.W, NaturalAxisData.Z, NaturalAxisData.chi,
      deriv_complexPressure_ofReal hp]

theorem complexField_analytic {g a : ℝ → ℝ} {cap : ℝ}
    (hp : PressureDatum.Admissible g a cap) (h j σ : ℝ) (k : Field) :
    AnalyticOnNhd ℂ (complexField h j σ (PressureDatum.complexPressure g a) k)
      (regularSet h j σ) := by
  intro z hz
  have hL : complexL h z ≠ 0 := hz.1.2
  have hden : denominator h j σ z ≠ 0 := hz.2
  have hP := PressureDatum.complexPressure_analytic hp z hz.1.1
  have hP' := hP.deriv
  change AnalyticAt ℂ
    (fun w => complexField h j σ (PressureDatum.complexPressure g a) k w) z
  cases k <;>
    dsimp [complexField, complexD, complexL, complexU, complexH, complexW,
      complexZ, complexChi, complexGradient, denominator] <;>
    fun_prop (disch := assumption)


/-- A convex open outer neighborhood and compact inner neighborhood.
The inner radius can be used for both the fixed fields and an analytic primitive. -/
theorem exists_convex_common_neighborhood {h j σ : ℝ}
    (hp : NaturalAxisRange.Parameters h j) (hσ : 0 < σ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ U K : Set ℂ,
      IsOpen U ∧ Convex ℝ U ∧ (0 : ℂ) ∈ U ∧ IsCompact K ∧
      (∀ x ∈ window.interval, closedBall (x : ℂ) ρ ⊆ K) ∧
      K ⊆ U ∧ U ⊆ regularSet h j σ := by
  let R : Set ℂ := Complex.ofReal '' window.interval
  have hR : IsCompact R := isCompact_Icc.image Complex.continuous_ofReal
  have hRconv : Convex ℝ R :=
    (convex_Icc window.left window.right).linear_image Complex.ofRealCLM.toLinearMap
  have hRzero : (0 : ℂ) ∈ R := by
    refine ⟨0, ?_, by simp⟩
    norm_num [window, Window.interval]
  have hsub : R ⊆ regularSet h j σ := by
    rintro z ⟨x, hx, rfl⟩
    exact real_mem_regularSet hp hσ hx
  obtain ⟨δ, hδ, hδU⟩ := hR.exists_cthickening_subset_open (regularSet_open h j σ) hsub
  refine ⟨δ / 2, half_pos hδ, thickening δ R, cthickening (δ / 2) R,
    isOpen_thickening, hRconv.thickening δ, self_subset_thickening hδ R hRzero,
    hR.cthickening, ?_, cthickening_subset_thickening' hδ (half_lt_self hδ) R,
    (thickening_subset_cthickening δ R).trans hδU⟩
  intro x hx
  exact closedBall_subset_cthickening (mem_image_of_mem Complex.ofReal hx) (δ / 2)

/-- Compactness and finiteness give one common value bound for all inputs. -/
theorem finite_family_bound {ι : Type*} [Fintype ι]
    {K : Set ℂ} (hK : IsCompact K) (f : ι → ℂ → ℂ)
    (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ B : ℝ, 0 < B ∧ ∀ i z, z ∈ K → ‖f i z‖ ≤ B := by
  classical
  choose b hb using fun i => hK.exists_bound_of_continuousOn (hf i)
  let B : ℝ := 1 + ∑ i, |b i|
  have hsum : 0 ≤ ∑ i, |b i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨B, by dsimp [B]; linarith, ?_⟩
  intro i z hz
  have hi : |b i| ≤ ∑ i, |b i| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (b k)) (Finset.mem_univ i)
  exact (hb i z hz).trans ((le_abs_self _).trans (by dsimp [B]; linarith))

theorem unitHolomorphic_of_bound {I : Window} {ρ B : ℝ} {f : ℂ → ℂ}
    (hB : 0 < B) (hf : AnalyticOnNhd ℂ f (closedTube I ρ))
    (hb : ∀ z ∈ closedTube I ρ, ‖f z‖ ≤ B) :
    UnitHolomorphic I ρ (fun z => f z / (B : ℂ)) := by
  have hBne : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  constructor
  · intro z hz
    exact (hf z hz).div analyticAt_const hBne
  · intro z hz
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    exact (div_le_one hB).mpr (hb z hz)

theorem coefficient_smul (I : Window) (ε c : ℝ) (a : AxisSpace I ε) (n : ℕ) (x : ℝ) :
    coefficient I (AxisWeightEstimates.weight ε) (c • a) n x =
      c * coefficient I (AxisWeightEstimates.weight ε) a n x := by
  exact jet_smul I (AxisWeightEstimates.weight ε) c a.1 n 0 x

/-- An arbitrary finite complex bound is reduced to the unit-bound Cauchy constructor. -/
def boundedAxisElement {I : Window} {ε ρ B : ℝ} {f : ℂ → ℂ}
    (hε : 0 < ε) (hερ : ε < ρ) (hB : 0 < B)
    (hf : AnalyticOnNhd ℂ f (closedTube I ρ))
    (hb : ∀ z ∈ closedTube I ρ, ‖f z‖ ≤ B) : AxisSpace I ε :=
  B • (unitHolomorphic_of_bound hB hf hb).toAxisSpace hε hερ

theorem boundedAxisElement_norm {I : Window} {ε ρ B : ℝ} {f : ℂ → ℂ}
    (hε : 0 < ε) (hερ : ε < ρ) (hB : 0 < B)
    (hf : AnalyticOnNhd ℂ f (closedTube I ρ))
    (hb : ∀ z ∈ closedTube I ρ, ‖f z‖ ≤ B) :
    ‖boundedAxisElement hε hερ hB hf hb‖ ≤ B * radiusLoss (ε / ρ) := by
  unfold boundedAxisElement
  calc
    _ ≤ ‖B‖ * ‖(unitHolomorphic_of_bound hB hf hb).toAxisSpace hε hερ‖ :=
      NormedSpace.norm_smul_le B _
    _ ≤ B * radiusLoss (ε / ρ) := by
      rw [Real.norm_eq_abs, abs_of_pos hB]
      exact mul_le_mul_of_nonneg_left
        ((unitHolomorphic_of_bound hB hf hb).norm_toAxisSpace_le hε hερ) hB.le

theorem boundedAxisElement_coefficient {I : Window} {ε ρ B : ℝ} {f : ℂ → ℂ}
    (hε : 0 < ε) (hερ : ε < ρ) (hB : 0 < B)
    (hf : AnalyticOnNhd ℂ f (closedTube I ρ))
    (hb : ∀ z ∈ closedTube I ρ, ‖f z‖ ≤ B)
    (n : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    coefficient I (AxisWeightEstimates.weight ε) (boundedAxisElement hε hερ hB hf hb) n x =
      if n = 0 then (f (x : ℂ)).re else 0 := by
  rw [boundedAxisElement, coefficient_smul,
    (unitHolomorphic_of_bound hB hf hb).coefficient_toAxisSpace hε hερ n hx]
  by_cases hn : n = 0
  · rw [ite_eq_left hn, ite_eq_left hn, Complex.div_ofReal_re]
    exact mul_div_cancel₀ _ hB.ne'
  · rw [ite_eq_right hn, ite_eq_right hn, mul_zero]

/-- A finite family of actual degree-zero fields, all using the same
positive parameter radius and the same finite norm bound. -/
structure CoefficientFamily (h j σ : ℝ) (P : ℝ → ℝ) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  elements : Field → AxisSpace window epsilon
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ k, ‖elements k‖ ≤ bound
  coefficient_eq : ∀ k n x, x ∈ window.interval →
    coefficient window (AxisWeightEstimates.weight epsilon) (elements k) n x =
      if n = 0 then realField h j σ P k x else 0

theorem exists_coefficientFamily_on_neighborhood {h j σ ρ : ℝ}
    {g a : ℝ → ℝ} {cap : ℝ} (hp : PressureDatum.Admissible g a cap)
    (hρ : 0 < ρ) {K : Set ℂ} (hK : IsCompact K)
    (hcover : ∀ x ∈ window.interval, closedBall (x : ℂ) ρ ⊆ K)
    (hKU : K ⊆ regularSet h j σ) :
    ∃ v : CoefficientFamily h j σ (PressureDatum.pressure g a), v.epsilon = ρ / 2 := by
  have hsub : closedTube window ρ ⊆ K := by
    rintro z ⟨x, hx, hz⟩
    exact hcover x hx hz
  let f := complexField h j σ (PressureDatum.complexPressure g a)
  have hf : ∀ k, AnalyticOnNhd ℂ (f k) (closedTube window ρ) :=
    fun k => (complexField_analytic hp h j σ k).mono (hsub.trans hKU)
  obtain ⟨B, hB, hb⟩ := finite_family_bound hK f
    (fun k => ((complexField_analytic hp h j σ k).mono hKU).continuousOn)
  have hb' : ∀ k z, z ∈ closedTube window ρ → ‖f k z‖ ≤ B :=
    fun k z hz => hb k z (hsub hz)
  have hε : 0 < ρ / 2 := half_pos hρ
  have hερ : ρ / 2 < ρ := half_lt_self hρ
  let v : Field → AxisSpace window (ρ / 2) :=
    fun k => boundedAxisElement hε hερ hB (hf k) (hb' k)
  refine ⟨{
    epsilon := ρ / 2
    epsilon_pos := hε
    elements := v
    bound := B * radiusLoss ((ρ / 2) / ρ)
    bound_nonneg := mul_nonneg hB.le
      (radiusLoss_nonneg (div_nonneg hε.le hρ.le))
    norm_le := fun k => boundedAxisElement_norm hε hερ hB (hf k) (hb' k)
    coefficient_eq := ?_
  }, rfl⟩
  intro k n x hx
  rw [boundedAxisElement_coefficient hε hερ hB (hf k) (hb' k) n hx]
  simp only [f, complexField_ofReal hp, Complex.ofReal_re]


/-- The coefficient family and the open convex domain for its primitive
can be chosen together, with an explicit strict gap between the two radii. -/
theorem exists_coefficientFamily_with_convex_domain {h j σ : ℝ}
    (hsmall : NaturalAxisRange.Parameters h j) (hσ : 0 < σ)
    {g a : ℝ → ℝ} {cap : ℝ} (hp : PressureDatum.Admissible g a cap) :
    ∃ v : CoefficientFamily h j σ (PressureDatum.pressure g a),
      ∃ ρ : ℝ, v.epsilon < ρ ∧ ∃ U K : Set ℂ,
      IsOpen U ∧ Convex ℝ U ∧ (0 : ℂ) ∈ U ∧ IsCompact K ∧
      (∀ x ∈ window.interval, closedBall (x : ℂ) ρ ⊆ K) ∧
      K ⊆ U ∧ U ⊆ regularSet h j σ := by
  obtain ⟨ρ, hρ, U, K, hUopen, hUconv, hUzero, hK, hcover, hKU, hUreg⟩ :=
    exists_convex_common_neighborhood hsmall hσ
  obtain ⟨v, hv⟩ := exists_coefficientFamily_on_neighborhood hp hρ hK hcover (hKU.trans hUreg)
  exact ⟨v, ρ, hv ▸ half_lt_self hρ, U, K, hUopen, hUconv, hUzero, hK,
    hcover, hKU, hUreg⟩

def CoefficientFamily.axisData {h j σ : ℝ} {P : ℝ → ℝ}
    (v : CoefficientFamily h j σ P) : AxisContraction.AxisData (AxisSpace window v.epsilon) where
  A := NaturalAxisData.A h
  D := NaturalAxisData.D h
  h := h
  one := v.elements .one
  eta := v.elements .eta
  d := v.elements .d
  inverseL := v.elements .inverseL
  uStar := v.elements .uStar
  uStarEta := v.elements .uStarEta
  wStar := v.elements .wStar
  hStar := v.elements .hStar
  normalizedGradient := v.elements .gradient
  zStar := v.elements .zStar

theorem CoefficientFamily.radiallyConstant {h j σ : ℝ} {P : ℝ → ℝ}
    (v : CoefficientFamily h j σ P) (k : Field) :
    NaturalAxisBridge.RadiallyConstant window v.epsilon (v.elements k) := by
  intro n hn x hx
  rw [v.coefficient_eq k n x hx, ite_eq_right hn]

theorem CoefficientFamily.value {h j σ : ℝ} {P : ℝ → ℝ}
    (v : CoefficientFamily h j σ P) (k : Field) {x : ℝ} (hx : x ∈ window.interval) :
    NaturalAxisBridge.inputValue window v.epsilon (v.elements k) x =
      realField h j σ P k x := by
  exact (v.coefficient_eq k 0 x hx).trans (ite_eq_left rfl)

theorem CoefficientFamily.compatible {h j σ : ℝ} {P : ℝ → ℝ}
    (v : CoefficientFamily h j σ P) :
    NaturalAxisBridge.CompatibleData window v.epsilon (v.elements .chi) v.axisData := by
  refine {
    chi_radial := v.radiallyConstant .chi
    one_radial := v.radiallyConstant .one
    eta_radial := v.radiallyConstant .eta
    d_radial := v.radiallyConstant .d
    inverseL_radial := v.radiallyConstant .inverseL
    uStar_radial := v.radiallyConstant .uStar
    uStarEta_radial := v.radiallyConstant .uStarEta
    wStar_radial := v.radiallyConstant .wStar
    hStar_radial := v.radiallyConstant .hStar
    gradient_radial := v.radiallyConstant .gradient
    zStar_radial := v.radiallyConstant .zStar
    one_value := fun x hx => v.value .one hx
    eta_value := fun x hx => v.value .eta hx
    uStarEta_value := ?_
  }
  intro x hx
  have hx' : x ∈ window.interval := ⟨hx.1.le, hx.2.le⟩
  change NaturalAxisBridge.inputValue window v.epsilon (v.elements .uStarEta) x =
    deriv (NaturalAxisBridge.inputValue window v.epsilon (v.elements .uStar)) x
  rw [v.value .uStarEta hx']
  have heq : NaturalAxisBridge.inputValue window v.epsilon (v.elements .uStar) =ᶠ[𝓝 x]
      NaturalAxisData.U j := by
    filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
    exact v.value .uStar hy
  rw [heq.deriv_eq]
  symm
  change deriv (fun y : ℝ => 4 * y + j) x = 4
  simp


/-- The actual normalized logarithmic phase, as a complex segment integral. -/
def axisPhase (h j σ : ℝ) : ℂ → ℂ :=
  AnalyticPrimitive.primitive (complexGradient h j σ)

def realPhase (h j σ x : ℝ) : ℝ :=
  x * ∫ t in (0 : ℝ)..1, realGradient h j σ (t * x)

@[simp] theorem axisPhase_zero (h j σ : ℝ) : axisPhase h j σ 0 = 0 := by
  simp [axisPhase]

@[simp] theorem axisPhase_ofReal (h j σ x : ℝ) :
    axisPhase h j σ (x : ℂ) = (realPhase h j σ x : ℂ) :=
  AnalyticPrimitive.primitive_ofReal (complexGradient h j σ) (realGradient h j σ)
    (complexGradient_ofReal h j σ) x

/-- The fixed coefficient family and its actual analytic phase on one
common compact neighborhood. No primitive or coefficient record is assumed
by the existence theorem below. -/
structure AnalyticInputs (h j σ : ℝ) (P : ℝ → ℝ) where
  coefficients : CoefficientFamily h j σ P
  radius : ℝ
  radius_gap : coefficients.epsilon < radius
  compactSet : Set ℂ
  isCompact : IsCompact compactSet
  covers : ∀ x ∈ window.interval, closedBall (x : ℂ) radius ⊆ compactSet
  phase_analytic : AnalyticOnNhd ℂ (axisPhase h j σ) compactSet
  phase_derivative : ∀ z ∈ compactSet,
    HasDerivAt (axisPhase h j σ) (complexGradient h j σ z) z

theorem exists_analyticInputs {h j σ : ℝ}
    (hsmall : NaturalAxisRange.Parameters h j) (hσ : 0 < σ)
    {g a : ℝ → ℝ} {cap : ℝ} (hp : PressureDatum.Admissible g a cap) :
    Nonempty (AnalyticInputs h j σ (PressureDatum.pressure g a)) := by
  obtain ⟨v, ρ, hgap, U, K, hUopen, hUconv, hUzero, hK, hcover, hKU, hUreg⟩ :=
    exists_coefficientFamily_with_convex_domain hsmall hσ hp
  have hg : DifferentiableOn ℂ (complexGradient h j σ) U :=
    ((complexGradient_analytic h j σ).mono hUreg).differentiableOn
  refine ⟨{
    coefficients := v
    radius := ρ
    radius_gap := hgap
    compactSet := K
    isCompact := hK
    covers := hcover
    phase_analytic := (AnalyticPrimitive.analyticOnNhd_primitive hUopen hUconv hUzero hg).mono hKU
    phase_derivative := fun z hz =>
      AnalyticPrimitive.hasDerivAt_primitive hUopen hUconv hUzero hg (hKU hz)
  }⟩

theorem AnalyticInputs.radius_pos {h j σ : ℝ} {P : ℝ → ℝ}
    (d : AnalyticInputs h j σ P) : 0 < d.radius :=
  d.coefficients.epsilon_pos.trans d.radius_gap

theorem AnalyticInputs.real_mem_compact {h j σ : ℝ} {P : ℝ → ℝ}
    (d : AnalyticInputs h j σ P) {x : ℝ} (hx : x ∈ window.interval) :
    (x : ℂ) ∈ d.compactSet :=
  d.covers x hx (mem_closedBall_self d.radius_pos.le)

theorem AnalyticInputs.realPhase_hasDerivAt {h j σ : ℝ} {P : ℝ → ℝ}
    (d : AnalyticInputs h j σ P) {x : ℝ} (hx : x ∈ window.interval) :
    HasDerivAt (realPhase h j σ) (realGradient h j σ x) x := by
  simpa only [axisPhase_ofReal, complexGradient_ofReal, Complex.ofReal_re] using
    (d.phase_derivative (x : ℂ) (d.real_mem_compact hx)).real_of_complex

def realAmplitude (h j σ Λ C x : ℝ) : ℝ := Real.exp (Λ * realPhase h j σ x) / C

theorem AnalyticInputs.realAmplitude_hasDerivAt {h j σ : ℝ} {P : ℝ → ℝ}
    (d : AnalyticInputs h j σ P) (Λ C : ℝ) {x : ℝ} (hx : x ∈ window.interval) :
    HasDerivAt (realAmplitude h j σ Λ C)
      ((Λ * realGradient h j σ x) * realAmplitude h j σ Λ C x) x := by
  have hd := (((d.realPhase_hasDerivAt hx).const_mul Λ).exp).div_const C
  convert! hd using 1
  unfold realAmplitude
  ring

theorem realAmplitude_pos (h j σ Λ : ℝ) {C : ℝ} (hC : 0 < C) (x : ℝ) :
    0 < realAmplitude h j σ Λ C x :=
  div_pos (Real.exp_pos _) hC

/-- The true logarithmic derivative is the prescribed `ξ₀=Λκ`. -/
theorem AnalyticInputs.realAmplitude_logDerivative {h j σ : ℝ} {P : ℝ → ℝ}
    (d : AnalyticInputs h j σ P) (Λ : ℝ) {C : ℝ} (hC : 0 < C)
    {x : ℝ} (hx : x ∈ window.interval) :
    deriv (realAmplitude h j σ Λ C) x / realAmplitude h j σ Λ C x =
      Λ * realGradient h j σ x := by
  rw [(d.realAmplitude_hasDerivAt Λ C hx).deriv]
  exact mul_div_cancel_right₀ _ (realAmplitude_pos h j σ Λ hC x).ne'

def AnalyticInputs.normalizationThreshold {h j σ : ℝ} {P : ℝ → ℝ}
    (d : AnalyticInputs h j σ P) (Λ : ℝ) : ℝ :=
  Real.exp (Λ * realPartSup (axisPhase h j σ) d.compactSet)

def AnalyticInputs.amplitudeBound {h j σ : ℝ} {P : ℝ → ℝ}
    (d : AnalyticInputs h j σ P) : ℝ :=
  radiusLoss (d.coefficients.epsilon / d.radius)

theorem AnalyticInputs.amplitudeBound_nonneg {h j σ : ℝ} {P : ℝ → ℝ}
    (d : AnalyticInputs h j σ P) : 0 ≤ d.amplitudeBound :=
  radiusLoss_nonneg (div_nonneg d.coefficients.epsilon_pos.le d.radius_pos.le)

/-- The actual `φ*/C` belongs to exactly the same coefficient space as
all fixed data, uniformly for every allowed large parameter and normalization. -/
theorem AnalyticInputs.uniformAmplitude {h j σ : ℝ} {P : ℝ → ℝ}
    (d : AnalyticInputs h j σ P) :
    ∀ Λ : ℝ, 0 ≤ Λ → ∀ C : ℝ, d.normalizationThreshold Λ ≤ C →
      ∃ a : AxisSpace window d.coefficients.epsilon,
        ‖a‖ ≤ d.amplitudeBound ∧
        NaturalAxisBridge.RadiallyConstant window d.coefficients.epsilon a ∧
        ∀ x ∈ window.interval,
          NaturalAxisBridge.inputValue window d.coefficients.epsilon a x =
            realAmplitude h j σ Λ C x := by
  intro Λ hΛ C hC
  obtain ⟨a, ha, hvalue, hzero⟩ :=
    uniform_normalizedExp_axisData_of_compact d.coefficients.epsilon_pos d.radius_gap
      d.isCompact d.phase_analytic d.covers
      (fun x _ => by simp only [axisPhase_ofReal, Complex.ofReal_im]) Λ hΛ C hC
  refine ⟨a, ha, hzero, ?_⟩
  intro x hx
  simpa only [NaturalAxisBridge.inputValue, realAmplitude, axisPhase_ofReal,
    Complex.ofReal_re] using hvalue x hx

/-- End-to-end fixed analytic input construction from the actual pressure
integral and ideal prefix, including the normalized amplitude source. -/
theorem ideal_prefix_analytic_inputs {h j : ℝ}
    (hsmall : NaturalAxisRange.Parameters h j)
    {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ δ σ : ℝ, 0 < δ ∧ 0 < σ ∧
      (∀ x ∈ Icc (-1 : ℝ) 1,
        |NaturalAxisData.Z h j (PressureDatum.pressure g a) x| ≤ δ →
          99 / 100 < NaturalAxisData.chi h j σ x) ∧
      Nonempty (AnalyticInputs h j σ (PressureDatum.pressure g a)) := by
  obtain ⟨δ, σ, hδ, hσ, hcut, _⟩ :=
    NaturalAxisRange.ideal_prefix_cutoff_parameters hsmall hp hB hg ha
  exact ⟨δ, σ, hδ, hσ, hcut, exists_analyticInputs hsmall hσ hp⟩

end NavierStokes.NaturalAxisCoefficients

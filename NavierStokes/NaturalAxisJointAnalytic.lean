import NavierStokes.AxisHolomorphic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import NavierStokes.CauchyRestriction
import NavierStokes.HolomorphicFamily
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Topology.ContinuousMap.Units
import NavierStokes.NaturalEntrance

/-! # Joint analyticity of the constructed natural-axis solution

The coefficient witness retained by `CoefficientProfile` identifies the actual
nonlinear solution with convergent analytic radial sums. Its pressure integral
identifies the same analytic primitive, so no analyticity of the output is assumed.
-/
/-! Merged from `NavierStokes.AxisJointAnalytic` (in a section, so its `open`s cannot leak). -/
section
/-! # Joint real analyticity of the actual evaluated axis profiles

A geometrically convergent radial series takes values in the Banach space of
holomorphic parameter-disk functions. Fixed-contour Cauchy evaluation gives
joint analyticity; termwise real agreement identifies the constructed profile.
-/
/-! Merged from `NavierStokes.AxisAnalyticRadialSeries`. -/
/-! # A convergent radial series in a Banach space of parameter-disk functions -/

/-! Merged from `NavierStokes.AxisAnalyticCoefficients`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Holomorphic radial coefficients with a common geometric bound -/

noncomputable section

open Set Metric Filter Complex
open scoped Topology
open NavierStokes.AxisCoefficientSpace NavierStokes.AxisWeightEstimates
open NavierStokes.AxisEvaluation NavierStokes.AxisHolomorphic

namespace NavierStokes.AxisJointAnalytic

def coefficientJet (I : Window) (ε : ℝ) (A : AxisSpace I ε) (n m : ℕ) (x : ℝ) : ℝ :=
  jet I (weight ε) A.1 n m x / (m.factorial : ℝ)

theorem coefficientJet_hasDerivAt (I : Window) {ε : ℝ} (_hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) {x : ℝ} (hx : x ∈ Ioo I.left I.right) :
    HasDerivAt (coefficientJet I ε A n m)
      (((m : ℝ) + 1) * coefficientJet I ε A n (m + 1) x) x := by
  have hd := (hasDerivAt_jet_interior I (weight ε) A n m hx).div_const (m.factorial : ℝ)
  convert! hd using 1
  unfold coefficientJet
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem coefficientJet_bound (I : Window) {ε s : ℝ} (hε : 0 < ε)
    (hs : (1 : ℝ) / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (n m : ℕ) (x : ℝ) :
    ‖coefficientJet I ε A n m x‖ ≤
      (‖A‖ / (1 - s) * (1 / 20 / s) ^ n) * ((ε * (1 - s))⁻¹) ^ m := by
  have hb := term_factorial_bound I hε (R := 1) (by rfl) hs hs1 A 0 m n
    (p := (1, x)) (by norm_num)
  simp only [term, polynomialJet, Nat.descFactorial_zero, Nat.cast_one, Nat.sub_zero,
    one_pow, one_mul, pow_zero, mul_one] at hb
  rw [coefficientJet, norm_div, Real.norm_natCast]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < m.factorial)).mpr
  calc
    _ ≤ _ := hb
    _ = _ := by ring

/-- The actual vertical Taylor extension of radial coefficient `n`. -/
def complexCoefficient (I : Window) (ε : ℝ) (A : AxisSpace I ε) (n : ℕ) : ℂ → ℂ :=
  verticalExtension (coefficientJet I ε A n)

theorem complexCoefficient_ofReal (I : Window) (ε : ℝ) (A : AxisSpace I ε)
    (n : ℕ) (x : ℝ) :
    complexCoefficient I ε A n (x : ℂ) = (coefficient I (weight ε) A n x : ℂ) := by
  rw [complexCoefficient, verticalExtension_ofReal]
  simp [coefficientJet, coefficient]

theorem complexCoefficient_analytic (I : Window) {ε s : ℝ} (hε : 0 < ε)
    (hs : (1 : ℝ) / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε) (n : ℕ) :
    AnalyticOnNhd ℂ (complexCoefficient I ε A n) (parameterStrip I (ε * (1 - s))) := by
  apply verticalExtension_analytic I (C := ‖A‖ / (1 - s) * (1 / 20 / s) ^ n)
    (mul_nonneg (div_nonneg (norm_nonneg A) (by linarith)) (by positivity))
    (mul_pos hε (by linarith))
  · intro m x hx
    exact coefficientJet_hasDerivAt I hε A n m hx
  · intro m x _
    exact coefficientJet_bound I hε hs hs1 A n m x

theorem complexCoefficient_bound (I : Window) {ε s : ℝ} (hε : 0 < ε)
    (hs : (1 : ℝ) / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε) (n : ℕ)
    {z : ℂ} (hz : z ∈ parameterStrip I (ε * (1 - s))) :
    ‖complexCoefficient I ε A n z‖ ≤ (2 * ‖A‖ / (1 - s)) * (1 / 20 / s) ^ n := by
  have hb := verticalExtension_bound
    (C := ‖A‖ / (1 - s) * (1 / 20 / s) ^ n)
    (mul_nonneg (div_nonneg (norm_nonneg A) (by linarith)) (by positivity))
    (mul_pos hε (by linarith)) hz.2.le
    (fun m => coefficientJet_bound I hε hs hs1 A n m z.re)
  change ‖verticalExtension (coefficientJet I ε A n) z‖ ≤ _
  convert! hb using 1
  ring

end NavierStokes.AxisJointAnalytic


end


noncomputable section

open Set Metric Filter Complex
open scoped Topology
open NavierStokes.AxisCoefficientSpace NavierStokes.AxisWeightEstimates
open NavierStokes.AxisEvaluation NavierStokes.AxisHolomorphic NavierStokes.CauchyRestriction

namespace NavierStokes.AxisJointAnalytic

section Geometric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Uniform geometric coefficient bounds yield a genuine Banach-valued
holomorphic radial sum throughout the indicated disk. -/
theorem geometricSeries_analytic {a : ℕ → E} {C ρ R : ℝ}
    (_hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hR : 0 < R) (hq : R * ρ < 1)
    (ha : ∀ n, ‖a n‖ ≤ C * ρ ^ n) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∑' n : ℕ, z ^ n • a n) (ball 0 R) := by
  have hg : Summable (fun n : ℕ => C * (R * ρ) ^ n) :=
    (summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hR.le hρ)]
      exact hq)).mul_left C
  apply (Complex.differentiableOn_tsum_of_summable_norm hg _ isOpen_ball _).analyticOnNhd isOpen_ball
  · intro n
    exact ((differentiable_id.pow n).smul_const (a n)).differentiableOn
  · intro n z hz
    have hzR : ‖z‖ ≤ R := (mem_ball_zero_iff.mp hz).le
    rw [norm_smul, norm_pow]
    calc
      _ ≤ R ^ n * (C * ρ ^ n) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hzR n)
        (ha n) (norm_nonneg _) (pow_nonneg hR.le n)
      _ = _ := by rw [mul_pow]; ring

theorem geometricSeries_summable {a : ℕ → E} {C ρ R : ℝ}
    (_hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hR : 0 < R) (hq : R * ρ < 1)
    (ha : ∀ n, ‖a n‖ ≤ C * ρ ^ n) {z : ℂ} (hz : ‖z‖ ≤ R) :
    Summable (fun n : ℕ => z ^ n • a n) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hR.le hρ)]
      exact hq)).mul_left C)
  intro n
  rw [norm_smul, norm_pow]
  calc
    _ ≤ R ^ n * (C * ρ ^ n) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz n)
      (ha n) (norm_nonneg _) (pow_nonneg hR.le n)
    _ = _ := by rw [mul_pow]; ring

end Geometric

/-- Each coefficient restricted to a closed disk inside the common strip. -/
def diskCoefficient (I : Window) {ε s : ℝ} (hε : 0 < ε)
    (hs : (1 : ℝ) / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s)))
    (n : ℕ) : C(Disk c σ, ℂ) where
  toFun z := complexCoefficient I ε A n z
  continuous_toFun := (complexCoefficient_analytic I hε hs hs1 A n).continuousOn.comp_continuous
    continuous_subtype_val (fun z => hK z.2)

theorem diskCoefficient_bound (I : Window) {ε s : ℝ} (hε : 0 < ε)
    (hs : (1 : ℝ) / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s))) (n : ℕ) :
    ‖diskCoefficient I hε hs hs1 A c σ hK n‖ ≤
      (2 * ‖A‖ / (1 - s)) * (1 / 20 / s) ^ n := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro z
  exact complexCoefficient_bound I hε hs hs1 A n (hK z.2)

/-- The same coefficient series, evaluated at a real radius and a complex
parameter. Its real slice is the original constructed profile. -/
def radialExtension (I : Window) (ε : ℝ) (A : AxisSpace I ε) (Y : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (Y : ℂ) ^ n * complexCoefficient I ε A n z

theorem radialExtension_ofReal (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y : ℝ} (hY : |Y| < 20) (x : ℝ) :
    radialExtension I ε A Y (x : ℂ) = (profile I ε A (Y, x) : ℂ) := by
  unfold radialExtension profile
  simp only [complexCoefficient_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  exact (Complex.ofRealCLM.map_tsum (profile_hasSum I hε A (p := (Y, x)) hY).summable).symm

end NavierStokes.AxisJointAnalytic


/-! Merged from `NavierStokes.HolomorphicFamilyAnalytic`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Joint analyticity from analytic disk-valued families

The fixed Cauchy contour is a bounded bilinear operation. Its kernel is
analytic in the supremum norm because inversion is analytic at units of the
Banach algebra of continuous contour functions.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace NavierStokes.HolomorphicFamily

private def constantPath : ℂ →L[ℝ] C(Angles, ℂ) :=
  LinearMap.mkContinuous {
    toFun := ContinuousMap.const Angles
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
  } 1 (by
    intro z
    simpa only [one_mul] using (ContinuousMap.norm_le _ (norm_nonneg z)).mpr (fun _ => le_rfl))

private def circlePath (c : ℂ) (σ : ℝ) : C(Angles, ℂ) :=
  ⟨fun θ => circleMap c σ θ, (continuous_circleMap c σ).comp continuous_subtype_val⟩

private def tangentPath (σ : ℝ) : C(Angles, ℂ) :=
  ⟨fun θ => circleMap 0 σ θ * I,
    ((continuous_circleMap 0 σ).comp continuous_subtype_val).mul continuous_const⟩

private theorem inversePath_apply {f : C(Angles, ℂ)} (hf : IsUnit f) (θ : Angles) :
    Ring.inverse f θ = (f θ)⁻¹ := by
  have h := congrArg (fun g : C(Angles, ℂ) => g θ) (Ring.mul_inverse_cancel f hf)
  change f θ * Ring.inverse f θ = 1 at h
  exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using h)

/-- The fixed-contour kernel is analytic as a curve in the supremum norm. -/
theorem analyticAt_kernelPath (c : ℂ) (σ : ℝ) {z : ℂ} (hz : z ∈ ball c σ) :
    AnalyticAt ℝ (kernelPath c σ) z := by
  let D : ℂ → C(Angles, ℂ) := fun w => circlePath c σ - constantPath w
  have hu : IsUnit (D z) := by
    apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
    intro θ
    exact sub_ne_zero.mpr (circleMap_ne_mem_ball hz θ)
  have hd : AnalyticAt ℝ D z := analyticAt_const.sub (constantPath.analyticAt z)
  have hi : AnalyticAt ℝ (fun w => Ring.inverse (D w)) z :=
    (analyticOnNhd_inverse (𝕜 := ℝ) (D z) hu).comp hd
  have ha : AnalyticAt ℝ (fun w => tangentPath σ * Ring.inverse (D w)) z :=
    analyticAt_const.mul hi
  apply ha.congr
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  ext θ
  have huw : IsUnit (D w) := by
    apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
    intro a
    exact sub_ne_zero.mpr (circleMap_ne_mem_ball hw a)
  simp only [ContinuousMap.mul_apply, inversePath_apply huw,
    kernelPath_apply c σ hw θ]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Analytic disk data gives joint real analyticity of its Cauchy evaluation. -/
theorem analyticAt_cauchyValue (c : ℂ) {σ : ℝ} (hσ : 0 < σ)
    (V : ℝ → C(CauchyRestriction.Disk c σ, E)) {p : ℝ × ℂ}
    (hV : AnalyticAt ℝ V p.1) (hz : p.2 ∈ ball c σ) :
    AnalyticAt ℝ (cauchyValue c hσ V) p := by
  have hk : AnalyticAt ℝ (fun q : ℝ × ℂ => kernelPath c σ q.2) p :=
    (analyticAt_kernelPath c σ hz).comp (analyticAt_snd (𝕜 := ℝ) (p := p))
  have hv : AnalyticAt ℝ (fun q : ℝ × ℂ => sampleCircle c hσ (V q.1)) p :=
    ((sampleCircle c hσ (E := E)).analyticAt _).comp_of_eq
      (hV.comp (analyticAt_fst (𝕜 := ℝ) (p := p))) rfl
  have hp : AnalyticAt ℝ (fun q : ℝ × ℂ => pathAction (E := E)
      (kernelPath c σ q.2) (sampleCircle c hσ (V q.1))) p :=
    ((pathAction (E := E)).analyticAt_bilinear _).comp_of_eq (hk.prod hv) rfl
  exact (((angleIntegral (E := E)).analyticAt _).comp_of_eq hp rfl).const_smul
    (c := (2 * Real.pi * I : ℂ)⁻¹)

variable [CompleteSpace E]

/-- Joint real analyticity follows from analytic disk data and holomorphic
slices, by equality with the actual fixed-contour Cauchy expression. -/
theorem analyticOnNhd_of_disk_family (c : ℂ) {σ : ℝ} (hσ : 0 < σ)
    {S : Set ℝ} (hS : IsOpen S) (V : ℝ → C(CauchyRestriction.Disk c σ, E))
    (F : ℝ → ℂ → E) (hV : AnalyticOnNhd ℝ V S)
    (hF : ∀ r ∈ S, DifferentiableOn ℂ (F r) (ball c σ))
    (hvalues : ∀ r ∈ S, ∀ z : CauchyRestriction.Disk c σ, V r z = F r z) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℂ => F p.1 p.2) (S ×ˢ ball c σ) := by
  intro p hp
  apply (analyticAt_cauchyValue c hσ V (hV p.1 hp.1) hp.2).congr
  filter_upwards [(hS.prod isOpen_ball).mem_nhds hp] with q hq
  exact cauchyValue_eq c hσ V F (hF q.1 hq.1) (hvalues q.1 hq.1) hq.2

end NavierStokes.HolomorphicFamily


end


noncomputable section

open Set Metric Filter Complex
open scoped Topology
open NavierStokes.AxisCoefficientSpace NavierStokes.AxisWeightEstimates
open NavierStokes.AxisEvaluation NavierStokes.AxisHolomorphic NavierStokes.CauchyRestriction

namespace NavierStokes.AxisJointAnalytic

private theorem ratio_lt_one {R s : ℝ} (hR : 1 ≤ R) (hs : R / 20 < s) :
    R * (1 / 20 / s) < 1 := by
  have hs0 : 0 < s := lt_trans (by positivity : 0 < R / 20) hs
  calc
    R * (1 / 20 / s) = R / 20 / s := by ring
    _ < 1 := (div_lt_one hs0).mpr hs

private theorem term_bound {R s C : ℝ} (hR : 0 ≤ R) (_hC : 0 ≤ C) (_hs : 0 < s)
    {Y z : ℂ} (hY : ‖Y‖ ≤ R) (n : ℕ)
    (hz : ‖z‖ ≤ C * (1 / 20 / s) ^ n) :
    ‖Y ^ n * z‖ ≤ C * (R * (1 / 20 / s)) ^ n := by
  rw [norm_mul, norm_pow]
  calc
    _ ≤ R ^ n * (C * (1 / 20 / s) ^ n) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg Y) hY n) hz (norm_nonneg z) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- The parameter slices of the radial sum are holomorphic on a common strip. -/
theorem radialExtension_analytic_parameter (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    {Y : ℝ} (hY : |Y| ≤ R) :
    AnalyticOnNhd ℂ (radialExtension I ε A Y) (parameterStrip I (ε * (1 - s))) := by
  change AnalyticOnNhd ℂ (fun z : ℂ => ∑' n : ℕ, (Y : ℂ) ^ n * complexCoefficient I ε A n z) _
  have hs0 : 0 < s := lt_trans (by positivity : 0 < R / 20) hs
  have hs' : (1 : ℝ) / 20 < s := (div_le_div_of_nonneg_right hR (by norm_num)).trans_lt hs
  have hC : 0 ≤ 2 * ‖A‖ / (1 - s) := by positivity
  have hq := ratio_lt_one hR hs
  have hqn : ‖(R * (1 / 20 / s) : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (zero_le_one.trans hR) (by positivity))]
    exact hq
  have hg : Summable (fun n : ℕ => (2 * ‖A‖ / (1 - s)) * (R * (1 / 20 / s)) ^ n) :=
    (summable_geometric_of_norm_lt_one hqn).mul_left (2 * ‖A‖ / (1 - s))
  have ht (n : ℕ) : DifferentiableOn ℂ
      (fun z : ℂ => (Y : ℂ) ^ n * complexCoefficient I ε A n z)
      (parameterStrip I (ε * (1 - s))) :=
    (complexCoefficient_analytic I hε hs' hs1 A n).differentiableOn.const_mul _
  have hb (n : ℕ) (z : ℂ) (hz : z ∈ parameterStrip I (ε * (1 - s))) :
      ‖(Y : ℂ) ^ n * complexCoefficient I ε A n z‖ ≤
        (2 * ‖A‖ / (1 - s)) * (R * (1 / 20 / s)) ^ n := by
    apply term_bound (by positivity) hC hs0 _ n
      (complexCoefficient_bound I hε hs' hs1 A n hz)
    simpa only [norm_real, Real.norm_eq_abs] using hY
  exact (Complex.differentiableOn_tsum_of_summable_norm hg ht
    (parameterStrip_isOpen I (ε * (1 - s))) hb).analyticOnNhd
      (parameterStrip_isOpen I (ε * (1 - s)))

/-- The constructed complex extension is jointly real analytic on each
parameter disk, with an open radial interval independent of the coefficient vector. -/
theorem radialExtension_joint_disk (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s))) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℂ => radialExtension I ε A p.1 p.2)
      (Ioo (-R) R ×ˢ ball c σ) := by
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hs0 : 0 < s := lt_trans (by positivity : 0 < R / 20) hs
  have hs' : (1 : ℝ) / 20 < s := (div_le_div_of_nonneg_right hR (by norm_num)).trans_lt hs
  let a : ℕ → C(Disk c σ, ℂ) := diskCoefficient I hε hs' hs1 A c σ hK
  let V : ℝ → C(Disk c σ, ℂ) := fun Y => ∑' n : ℕ, (Y : ℂ) ^ n • a n
  have hC : 0 ≤ 2 * ‖A‖ / (1 - s) := by positivity
  have hρ : 0 ≤ (1 : ℝ) / 20 / s := by positivity
  have hb (n : ℕ) : ‖a n‖ ≤ (2 * ‖A‖ / (1 - s)) * (1 / 20 / s) ^ n :=
    diskCoefficient_bound I hε hs' hs1 A c σ hK n
  have hVc := geometricSeries_analytic hC hρ hR0 (ratio_lt_one hR hs) hb
  apply HolomorphicFamily.analyticOnNhd_of_disk_family c hσ isOpen_Ioo V (radialExtension I ε A)
  · intro Y hY
    have hYc : (Y : ℂ) ∈ ball 0 R := by
      simpa only [mem_ball_zero_iff, norm_real, Real.norm_eq_abs] using abs_lt.mpr hY
    exact (hVc (Y : ℂ) hYc).restrictScalars.comp (Complex.ofRealCLM.analyticAt Y)
  · intro Y hY
    exact (radialExtension_analytic_parameter I hε hR hs hs1 A (abs_lt.mpr hY).le).differentiableOn.mono
      (ball_subset_closedBall.trans hK)
  · intro Y hY z
    have hsum := geometricSeries_summable hC hρ hR0 (ratio_lt_one hR hs) hb
      (z := (Y : ℂ)) (by simpa only [norm_real, Real.norm_eq_abs] using (abs_lt.mpr hY).le)
    change (ContinuousMap.evalCLM (R := ℂ) z) (∑' n : ℕ, (Y : ℂ) ^ n • a n) = _
    rw [(ContinuousMap.evalCLM (R := ℂ) z).map_tsum hsum]
    rfl

/-- Every genuine axis coefficient vector evaluates to a function analytic
jointly in the two real variables throughout the natural open strip. -/
theorem profile_analyticOnNhd (I : Window) {ε : ℝ} (hε : 0 < ε) (A : AxisSpace I ε) :
    AnalyticOnNhd ℝ (profile I ε A) (strip I 20) := by
  intro p hp
  have hY20 : |p.1| < 20 := abs_lt.mpr hp.1
  obtain ⟨R, hRp, hR20⟩ := exists_between (max_lt (by norm_num : (1 : ℝ) < 20) hY20)
  have hR : 1 ≤ R := (le_max_left 1 |p.1|).trans hRp.le
  have hYR : |p.1| < R := (le_max_right 1 |p.1|).trans_lt hRp
  obtain ⟨s, hs, hs1⟩ := exists_between (show R / 20 < 1 by linarith)
  have ha : 0 < ε * (1 - s) := mul_pos hε (by linarith)
  have hc : (p.2 : ℂ) ∈ parameterStrip I (ε * (1 - s)) := by
    exact ⟨hp.2, by simpa only [ofReal_im, abs_zero] using (half_pos ha)⟩
  obtain ⟨σ, hσ, hK⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((parameterStrip_isOpen I (ε * (1 - s))).mem_nhds hc)
  have hj := radialExtension_joint_disk I hε hR hs hs1 A (p.2 : ℂ) hσ hK
  let J : ℝ × ℝ → ℝ × ℂ := fun q => (q.1, (q.2 : ℂ))
  have hJ : AnalyticAt ℝ J p :=
    analyticAt_fst.prod (Complex.ofRealCLM.analyticAt _ |>.comp analyticAt_snd)
  have hpJ : J p ∈ Ioo (-R) R ×ˢ ball (p.2 : ℂ) σ := ⟨abs_lt.mp hYR, mem_ball_self hσ⟩
  have hcomp : AnalyticAt ℝ (fun q : ℝ × ℝ => (radialExtension I ε A q.1 (q.2 : ℂ)).re) p :=
    Complex.reCLM.analyticAt _ |>.comp_of_eq ((hj (J p) hpJ).comp hJ) rfl
  apply hcomp.congr
  filter_upwards [(isOpen_Ioo.prod isOpen_Ioo).mem_nhds hp] with q hq
  rw [radialExtension_ofReal I hε A (abs_lt.mpr hq.1), ofReal_re]

end NavierStokes.AxisJointAnalytic
end


noncomputable section

open Set Filter
open scoped Topology

namespace NavierStokes.NaturalEntrance

open AxisCoefficientSpace NaturalProfile NaturalAxisBridge NaturalAxisCoefficients

/-- All four scaled profiles of the actual nonlinear fixed point are jointly
real analytic on the common open axis rectangle. -/
theorem CoefficientProfile.scaled_analytic {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : CoefficientProfile d Λ C)
    (hΛ : 0 ≤ Λ) (hC : d.normalizationThreshold Λ ≤ C) :
    AnalyticOnNhd ℝ F.family.phi (AxisEvaluation.strip window 20) ∧
    AnalyticOnNhd ℝ F.family.u (AxisEvaluation.strip window 20) ∧
    AnalyticOnNhd ℝ F.family.average (AxisEvaluation.strip window 20) ∧
    AnalyticOnNhd ℝ F.family.pressure (AxisEvaluation.strip window 20) := by
  have hφ : AnalyticOnNhd ℝ F.family.phi (AxisEvaluation.strip window 20) := by
    rw [F.phi_eq]
    exact AxisJointAnalytic.profile_analyticOnNhd window d.coefficients.epsilon_pos _
  have hu : AnalyticOnNhd ℝ F.family.u (AxisEvaluation.strip window 20) := by
    rw [F.u_eq]
    exact AxisJointAnalytic.profile_analyticOnNhd window d.coefficients.epsilon_pos _
  have hB : AnalyticOnNhd ℝ F.family.average (AxisEvaluation.strip window 20) := by
    rw [F.average_eq]
    exact AxisJointAnalytic.profile_analyticOnNhd window d.coefficients.epsilon_pos _
  refine ⟨hφ, hu, hB, ?_⟩
  obtain ⟨a, _, harad, havalue⟩ := d.uniformAmplitude Λ hΛ C hC
  have heq : (AxisEvaluation.strip window 20).EqOn
      (AxisEvaluation.profile window d.coefficients.epsilon
        (pressureCoefficient window d.coefficients.epsilon_pos a F.coefficients.1))
      F.family.pressure := by
    intro p hp
    rw [pressure_integral window d.coefficients.epsilon_pos a F.coefficients.1 harad hp,
      F.scaled.pressure_integral p hp, F.phi_eq,
      havalue p.2 ⟨hp.2.1.le, hp.2.2.le⟩]
  exact (analyticOnNhd_congr (AxisEvaluation.strip_isOpen window 20) heq).mp
    (AxisJointAnalytic.profile_analyticOnNhd window d.coefficients.epsilon_pos _)

theorem amplitude_analytic {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (Λ C : ℝ) :
    AnalyticOnNhd ℝ (realAmplitude h j σ Λ C) (Ioo window.left window.right) := by
  intro η hη
  have hc := d.phase_analytic (η : ℂ) (d.real_mem_compact ⟨hη.1.le, hη.2.le⟩)
  have hr : AnalyticAt ℝ (realPhase h j σ) η := by
    have ht : AnalyticAt ℝ (fun x : ℝ => (axisPhase h j σ (x : ℂ)).re) η :=
      (Complex.reCLM.analyticAt _).comp_of_eq
        (hc.restrictScalars.comp (Complex.ofRealCLM.analyticAt η)) rfl
    simpa only [axisPhase_ofReal, Complex.ofReal_re] using ht
  exact ((analyticAt_const.mul hr).rexp).mul analyticAt_const

theorem pullback_analytic {F : ℝ × ℝ → ℝ}
    (hF : AnalyticOnNhd ℝ F (AxisEvaluation.strip window 20)) (Λ : ℝ) :
    AnalyticOnNhd ℝ (pullback Λ F) (domain Λ) := by
  intro p hp
  exact (hF (rescalePoint Λ p) hp).comp
    ((analyticAt_const.mul analyticAt_fst).prod analyticAt_snd)

theorem affineProfile_analytic {b : ℝ → ℝ}
    (hb : AnalyticOnNhd ℝ b (Ioo window.left window.right))
    {F : ℝ × ℝ → ℝ} (hF : AnalyticOnNhd ℝ F (AxisEvaluation.strip window 20))
    (c Λ : ℝ) : AnalyticOnNhd ℝ (affineProfile b c Λ F) (domain Λ) := by
  intro p hp
  exact ((hb p.2 hp.2).comp analyticAt_snd).add
    (analyticAt_const.mul (pullback_analytic hF Λ p hp))

theorem angularProfile_analytic {a : ℝ → ℝ}
    (ha : AnalyticOnNhd ℝ a (Ioo window.left window.right))
    {Φ : ℝ × ℝ → ℝ} (hΦ : AnalyticOnNhd ℝ Φ (AxisEvaluation.strip window 20))
    (Λ : ℝ) : AnalyticOnNhd ℝ (angularProfile a Λ Φ) (domain Λ) := by
  intro p hp
  exact ((ha p.2 hp.2).comp analyticAt_snd).mul (pullback_analytic hΦ Λ p hp)

/-- The unscaled angular velocity, axial velocity, average and pressure of
the actual nonlinear solution are jointly analytic in `(X,η)`. -/
theorem CoefficientProfile.natural_analytic {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : CoefficientProfile d Λ C)
    (hΛ : 0 ≤ Λ) (hC : d.normalizationThreshold Λ ≤ C)
    (hP0 : AnalyticOnNhd ℝ P0 (Ioo window.left window.right)) :
    AnalyticOnNhd ℝ F.family.f (domain Λ) ∧
    AnalyticOnNhd ℝ F.family.U (domain Λ) ∧
    AnalyticOnNhd ℝ F.family.Ubar (domain Λ) ∧
    AnalyticOnNhd ℝ F.family.Pi (domain Λ) := by
  obtain ⟨hφ, hu, hB, hP⟩ := F.scaled_analytic hΛ hC
  have hU : AnalyticOnNhd ℝ (NaturalAxisData.U j) (Ioo window.left window.right) := by
    intro η _
    exact (analyticAt_const.mul analyticAt_id).add analyticAt_const
  exact ⟨angularProfile_analytic (amplitude_analytic d Λ C) hφ Λ,
    affineProfile_analytic hU hu (1 / Λ) Λ,
    affineProfile_analytic hU hB (1 / Λ) Λ,
    affineProfile_analytic hP0 hP (1 / Λ) Λ⟩




end NavierStokes.NaturalEntrance

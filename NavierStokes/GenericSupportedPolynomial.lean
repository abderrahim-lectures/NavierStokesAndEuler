import NavierStokes.DiagonalResidual
import NavierStokes.MixedFiniteBackground

/-! Merged from `NavierStokes.GenericRealizationBounds` (in a section, so its `open`s cannot leak). -/
/-! Merged from `NavierStokes.GenericDifferentialPolynomial` (in a section, so its `open`s cannot leak). -/
section
/-! Merged from `NavierStokes.GenericJetRateAlgebra`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

noncomputable section

namespace NavierStokes.GenericDifferentialPolynomial

open Set Filter DiagonalResidual
open scoped Topology ContDiff

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
private local instance : NormedAddCommGroup ((D →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ ((D →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance

variable {l : Filter D} {q : D → ℝ} {U : Set D} {f g : D → ℝ}

theorem rate_zero {m : ℕ} {r : ℝ} : JetRate l q (fun _ : D => (0 : ℝ)) m r := by
  exact ⟨0, le_rfl, Eventually.of_forall (fun _ => by simp)⟩

theorem rate_mul (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {m : ℕ} {r s : ℝ} (hr : FiniteJetRate l q f m r)
    (hs : FiniteJetRate l q g m s) :
    JetRate l q (fun x => f x * g x) m (r + s) := by
  obtain ⟨A, hA, hbA⟩ := hr
  obtain ⟨B, hB, hbB⟩ := hs
  let L := ContinuousLinearMap.mul ℝ ℝ
  refine ⟨‖L‖ * 2 ^ m * A * B, by positivity, ?_⟩
  filter_upwards [hlU, hq, hbA, hbB] with x hx hqx hAx hBx
  calc
    _ ≤ ‖L‖ * 2 ^ m * (A * q x ^ r) * (B * q x ^ s) :=
      ResidualStability.norm_jet_bilinear_bound L hU hf hg hx m hAx hBx
    _ = (‖L‖ * 2 ^ m * A * B) * q x ^ (r + s) := by
      rw [Real.rpow_add hqx.1]
      ring

theorem smooth_directional (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (v : D) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x v) U :=
  (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

theorem rate_directional (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (v : D) {m : ℕ} {r : ℝ}
    (hr : JetRate l q f (m + 1) r) :
    JetRate l q (fun x => fderiv ℝ f x v) m r := by
  obtain ⟨C, hC, hb⟩ := hr
  let L := ContinuousLinearMap.apply ℝ ℝ v
  refine ⟨‖L‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  filter_upwards [hlU, hb] with x hx hbx
  exact (ResidualStability.norm_jet_linear_map_fderiv L hU hf hx m).trans
    ((mul_le_mul_of_nonneg_left hbx (norm_nonneg L)).trans_eq (mul_assoc _ _ _).symm)

theorem directional_sub_eqOn (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (v : D) :
    EqOn (fun x => fderiv ℝ (fun y => f y - g y) x v)
      (fun x => fderiv ℝ f x v - fderiv ℝ g x v) U := by
  intro x hx
  change fderiv ℝ (f - g) x v = _
  rw [fderiv_sub ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    ((hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
  rfl

end NavierStokes.GenericDifferentialPolynomial


end

noncomputable section

namespace NavierStokes.GenericDifferentialPolynomial

open Set Filter DiagonalResidual
open scoped Topology ContDiff

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Quantitative approximation data. Constants may depend on the stage, while
the power losses and derivative thresholds are fixed functions of the jet order. -/
structure ApproximationRates (l : Filter D) (q : D → ℝ) (gain : ℕ → ℝ)
    (f : D → ℝ) (stage : ℕ → D → ℝ) where
  growthLoss : ℕ → ℝ
  tailLoss : ℕ → ℝ
  threshold : ℕ → ℕ
  stage_growth : ∀ J m, JetRate l q (stage J) m (-growthLoss m)
  tail_rate : ∀ m J, threshold m ≤ J →
    JetRate l q (fun x => f x - stage J x) m (gain J - tailLoss m)

private def maxThreshold (M : ℕ → ℕ) (m : ℕ) : ℕ :=
  (Finset.range (m + 1)).sup M

private theorem le_maxThreshold (M : ℕ → ℕ) {k m : ℕ} (hk : k ≤ m) :
    M k ≤ maxThreshold M m :=
  Finset.le_sup (f := M) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

variable {l : Filter D} {q : D → ℝ} {gain : ℕ → ℝ} {U : Set D}
variable {f g : D → ℝ} {fs gs : ℕ → D → ℝ}

theorem ApproximationRates.full_growth
    (h : ApproximationRates l q gain f fs)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U) (hfs : ∀ J, ContDiffOn ℝ ∞ (fs J) U)
    (hg : Tendsto gain atTop atTop) (m : ℕ) :
    JetRate l q f m (-max 0 (h.growthLoss m)) := by
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1
    (hg.eventually (eventually_ge_atTop (h.tailLoss m)))
  let J := max (h.threshold m) J₀
  have htail := (h.tail_rate m J (le_max_left _ _)).weaken hq
    (show -max 0 (h.growthLoss m) ≤ gain J - h.tailLoss m by
      have := hJ₀ J (le_max_right _ _)
      have := le_max_left 0 (h.growthLoss m)
      linarith)
  have hstage := (h.stage_growth J m).weaken hq
    (neg_le_neg (le_max_right 0 (h.growthLoss m)))
  exact (hstage.add htail hU hlU (hfs J) (hf.sub (hfs J))).congr_on hU hlU
    (fun x _ => by dsimp; ring)

theorem ApproximationRates.stage_finite_growth
    (h : ApproximationRates l q gain f fs)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1) (J m : ℕ) :
    FiniteJetRate l q (fs J) m (-maxJetLoss h.growthLoss m) := by
  apply finiteJetRate_of_jetRate (hq.mono fun _ hx => hx.1)
  intro k hk
  exact (h.stage_growth J k).weaken hq (neg_le_neg (le_maxJetLoss _ hk))

theorem ApproximationRates.full_finite_growth
    (h : ApproximationRates l q gain f fs)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U) (hfs : ∀ J, ContDiffOn ℝ ∞ (fs J) U)
    (hg : Tendsto gain atTop atTop) (m : ℕ) :
    FiniteJetRate l q f m (-maxJetLoss h.growthLoss m) := by
  apply finiteJetRate_of_jetRate (hq.mono fun _ hx => hx.1)
  intro k hk
  exact (h.full_growth hU hlU hq hf hfs hg k).weaken hq
    (neg_le_neg (max_le (maxJetLoss_nonneg _ _) (le_maxJetLoss _ hk)))

theorem ApproximationRates.tail_finite_rate
    (h : ApproximationRates l q gain f fs)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1) (m J : ℕ)
    (hJ : maxThreshold h.threshold m ≤ J) :
    FiniteJetRate l q (fun x => f x - fs J x) m
      (gain J - maxJetLoss h.tailLoss m) := by
  apply finiteJetRate_of_jetRate (hq.mono fun _ hx => hx.1)
  intro k hk
  exact (h.tail_rate k J ((le_maxThreshold _ hk).trans hJ)).weaken hq
    (sub_le_sub_left (le_maxJetLoss _ hk) _)

def ApproximationRates.add
    (a : ApproximationRates l q gain f fs) (b : ApproximationRates l q gain g gs)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hfs : ∀ J, ContDiffOn ℝ ∞ (fs J) U)
    (hgs : ∀ J, ContDiffOn ℝ ∞ (gs J) U) :
    ApproximationRates l q gain (fun x => f x + g x)
      (fun J x => fs J x + gs J x) where
  growthLoss m := max (a.growthLoss m) (b.growthLoss m)
  tailLoss m := max (a.tailLoss m) (b.tailLoss m)
  threshold m := max (a.threshold m) (b.threshold m)
  stage_growth J m :=
    ((a.stage_growth J m).weaken hq (neg_le_neg (le_max_left _ _))).add
      ((b.stage_growth J m).weaken hq (neg_le_neg (le_max_right _ _)))
      hU hlU (hfs J) (hgs J)
  tail_rate m J hJ := by
    have ha := (a.tail_rate m J ((le_max_left _ _).trans hJ)).weaken hq
      (sub_le_sub_left (le_max_left (a.tailLoss m) (b.tailLoss m)) _)
    have hb := (b.tail_rate m J ((le_max_right _ _).trans hJ)).weaken hq
      (sub_le_sub_left (le_max_right (a.tailLoss m) (b.tailLoss m)) _)
    exact (ha.add hb hU hlU (hf.sub (hfs J)) (hg.sub (hgs J))).congr_on hU hlU
      (fun x _ => by dsimp; ring)

def ApproximationRates.mul
    (a : ApproximationRates l q gain f fs) (b : ApproximationRates l q gain g gs)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hfs : ∀ J, ContDiffOn ℝ ∞ (fs J) U)
    (hgs : ∀ J, ContDiffOn ℝ ∞ (gs J) U)
    (hgain : Tendsto gain atTop atTop) :
    ApproximationRates l q gain (fun x => f x * g x)
      (fun J x => fs J x * gs J x) where
  growthLoss m := maxJetLoss a.growthLoss m + maxJetLoss b.growthLoss m
  tailLoss m := max
    (maxJetLoss a.tailLoss m + maxJetLoss b.growthLoss m)
    (maxJetLoss b.tailLoss m + maxJetLoss a.growthLoss m)
  threshold m := max (maxThreshold a.threshold m) (maxThreshold b.threshold m)
  stage_growth J m := by
    have h := rate_mul hU hlU hq (hfs J) (hgs J)
      (a.stage_finite_growth hq J m) (b.stage_finite_growth hq J m)
    simpa only [neg_add] using h
  tail_rate m J hJ := by
    have ha := rate_mul hU hlU hq (hf.sub (hfs J)) hg
      (a.tail_finite_rate hq m J ((le_max_left _ _).trans hJ))
      (b.full_finite_growth hU hlU hq hg hgs hgain m)
    have hb := rate_mul hU hlU hq (hfs J) (hg.sub (hgs J))
      (a.stage_finite_growth hq J m)
      (b.tail_finite_rate hq m J ((le_max_right _ _).trans hJ))
    have ha' := ha.weaken hq
      (show gain J - max
        (maxJetLoss a.tailLoss m + maxJetLoss b.growthLoss m)
        (maxJetLoss b.tailLoss m + maxJetLoss a.growthLoss m) ≤
        (gain J - maxJetLoss a.tailLoss m) + -maxJetLoss b.growthLoss m by
        have := le_max_left
          (maxJetLoss a.tailLoss m + maxJetLoss b.growthLoss m)
          (maxJetLoss b.tailLoss m + maxJetLoss a.growthLoss m)
        linarith)
    have hb' := hb.weaken hq
      (show gain J - max
        (maxJetLoss a.tailLoss m + maxJetLoss b.growthLoss m)
        (maxJetLoss b.tailLoss m + maxJetLoss a.growthLoss m) ≤
        -maxJetLoss a.growthLoss m + (gain J - maxJetLoss b.tailLoss m) by
        have := le_max_right
          (maxJetLoss a.tailLoss m + maxJetLoss b.growthLoss m)
          (maxJetLoss b.tailLoss m + maxJetLoss a.growthLoss m)
        linarith)
    exact (ha'.add hb' hU hlU ((hf.sub (hfs J)).mul hg)
      ((hfs J).mul (hg.sub (hgs J)))).congr_on hU hlU
      (fun x _ => by dsimp; ring)

def ApproximationRates.directional
    (a : ApproximationRates l q gain f fs)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hfs : ∀ J, ContDiffOn ℝ ∞ (fs J) U) (v : D) :
    ApproximationRates l q gain (fun x => fderiv ℝ f x v)
      (fun J x => fderiv ℝ (fs J) x v) where
  growthLoss m := a.growthLoss (m + 1)
  tailLoss m := a.tailLoss (m + 1)
  threshold m := a.threshold (m + 1)
  stage_growth J m := rate_directional hU hlU (hfs J) v (a.stage_growth J (m + 1))
  tail_rate m J hJ := by
    have h := rate_directional hU hlU (hf.sub (hfs J)) v
      (a.tail_rate (m + 1) J hJ)
    exact h.congr_on hU hlU (directional_sub_eqOn hU hf (hfs J) v)

def ApproximationRates.fixed {c : D → ℝ} {L : ℕ → ℝ}
    (hc : ∀ m, JetRate l q c m (-L m)) :
    ApproximationRates l q gain c (fun _ => c) where
  growthLoss := L
  tailLoss := 0
  threshold := 0
  stage_growth _ m := hc m
  tail_rate m J _ := by
    simpa only [sub_self] using (rate_zero (l := l) (q := q) (m := m)
      (r := gain J - (0 : ℕ → ℝ) m))

/-- A finite differential expression in scalar components with fixed variable
coefficients. Products, sums, and arbitrary fixed directional derivatives are
allowed at every node; consequently the order and polynomial degree are finite. -/
inductive Expression (D ι κ : Type*) where
  | input : ι → Expression D ι κ
  | coeff : κ → Expression D ι κ
  | add : Expression D ι κ → Expression D ι κ → Expression D ι κ
  | mul : Expression D ι κ → Expression D ι κ → Expression D ι κ
  | directional : D → Expression D ι κ → Expression D ι κ

namespace Expression

variable {ι κ : Type*}

/-- Evaluation uses actual Fréchet derivatives, including at derivative nodes. -/
def eval (c : κ → D → ℝ) (u : ι → D → ℝ) : Expression D ι κ → D → ℝ
  | .input i => u i
  | .coeff i => c i
  | .add a b => fun x => eval c u a x + eval c u b x
  | .mul a b => fun x => eval c u a x * eval c u b x
  | .directional v a => fun x => fderiv ℝ (eval c u a) x v

theorem smooth_eval (e : Expression D ι κ)
    {c : κ → D → ℝ} {u : ι → D → ℝ} (hU : IsOpen U)
    (hc : ∀ i, ContDiffOn ℝ ∞ (c i) U)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U) : ContDiffOn ℝ ∞ (eval c u e) U := by
  induction e with
  | input i => exact hu i
  | coeff i => exact hc i
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb
  | directional v a ha => exact smooth_directional hU ha v

/-- Stability of every finite differential polynomial, with explicitly
constructed losses independent of the approximation stage. -/
def approximation_eval (e : Expression D ι κ)
    {c : κ → D → ℝ} {u : ι → D → ℝ} {us : ℕ → ι → D → ℝ}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hc : ∀ i, ContDiffOn ℝ ∞ (c i) U)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hus : ∀ J i, ContDiffOn ℝ ∞ (us J i) U)
    (hgain : Tendsto gain atTop atTop)
    (Lc : κ → ℕ → ℝ) (hcg : ∀ i m, JetRate l q (c i) m (-Lc i m))
    (happrox : ∀ i, ApproximationRates l q gain (u i) (fun J => us J i)) :
    ApproximationRates l q gain (eval c u e) (fun J => eval c (us J) e) := by
  induction e with
  | input i => exact happrox i
  | coeff i => exact ApproximationRates.fixed (hcg i)
  | add a b ha hb =>
      exact ha.add hb hU hlU hq (a.smooth_eval hU hc hu) (b.smooth_eval hU hc hu)
        (fun J => a.smooth_eval hU hc (hus J)) (fun J => b.smooth_eval hU hc (hus J))
  | mul a b ha hb =>
      exact ha.mul hb hU hlU hq (a.smooth_eval hU hc hu) (b.smooth_eval hU hc hu)
        (fun J => a.smooth_eval hU hc (hus J)) (fun J => b.smooth_eval hU hc (hus J)) hgain
  | directional v a ha =>
      exact ha.directional hU hlU (a.smooth_eval hU hc hu)
        (fun J => a.smooth_eval hU hc (hus J)) v

end Expression


end NavierStokes.GenericDifferentialPolynomial
end

section
/-!
# Quantitative bounds for general diagonal realizations

The base is retained without a cutoff. The positive corrections are actual
locally finite cutoff sums. Logarithmic losses are absorbed at each fixed
stage, while the resulting power loss is independent of the stage.
-/

noncomputable section

namespace NavierStokes.GenericRealizationBounds

open Set Filter DiagonalResidual
open scoped Topology ContDiff BigOperators

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The uncut base plus the actual positive cutoff series. -/
def realized (a : ℕ → ℝ) (q : E → ℝ) (base : E → V) (A : ℕ → E → V) : E → V :=
  fun x => base x + SolenoidalDiagonal.potentialSum a q
    (CutStageEstimates.positiveStages A) x

/-- The corresponding finite approximation, including exactly stages `1,…,J`. -/
def stage (base : E → V) (A : ℕ → E → V) (J : ℕ) : E → V :=
  fun x => base x + DiagonalJetBounds.uncutPrefix
    (CutStageEstimates.positiveStages A) (J + 1) x

theorem realized_smooth {U : Set E} (hU : IsOpen U) {q : E → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ x ∈ U, 0 < q x)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {base : E → V}
    (hbase : ContDiffOn ℝ ∞ base U) {A : ℕ → E → V}
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U) :
    ContDiffOn ℝ ∞ (realized a q base A) U :=
  hbase.add (SolenoidalDiagonal.potentialSum_contDiffOn ha hU hpos hq
    (CutStageEstimates.positiveStages_smooth hA))

theorem stage_smooth {U : Set E} {base : E → V}
    (hbase : ContDiffOn ℝ ∞ base U) {A : ℕ → E → V}
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U) (J : ℕ) :
    ContDiffOn ℝ ∞ (stage base A J) U :=
  hbase.add (ContDiffOn.sum (fun j _ => CutStageEstimates.positiveStages_smooth hA j))

/-- A logarithmic weight costs one fixed power, regardless of its fixed exponent. -/
theorem jetRate_of_log_bound {l : Filter E} {q : E → ℝ} {f : E → V}
    (hq : ∀ᶠ x in l, 0 < q x) (hqzero : Tendsto q l (𝓝 0))
    (m : ℕ) (C P r : ℝ)
    (hb : ∀ᶠ x in l, ‖iteratedFDeriv ℝ m f x‖ ≤
      C * (1 + |Real.log (q x)|) ^ P * q x ^ r) :
    JetRate l q f m (r - 1) := by
  have hqright : Tendsto q l (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hqzero, hq⟩
  have ht := ((DiagonalScale.tendsto_logPowerWeight C P 1 zero_lt_one).comp hqright).abs
  simp only [abs_zero] at ht
  have hs : ∀ᶠ x in l, |DiagonalScale.logPowerWeight C P 1 (q x)| ≤ 1 := by
    simpa only [Function.comp_def] using (ht.eventually (gt_mem_nhds zero_lt_one)).mono
      (fun _ h => h.le)
  refine ⟨1, zero_le_one, ?_⟩
  filter_upwards [hq, hb, hs] with x hx hbx hsx
  have he : r = 1 + (r - 1) := by ring
  calc
    _ ≤ C * (1 + |Real.log (q x)|) ^ P * q x ^ r := hbx
    _ ≤ |C * (1 + |Real.log (q x)|) ^ P * q x ^ r| := le_abs_self _
    _ = |DiagonalScale.logPowerWeight C P 1 (q x)| * q x ^ (r - 1) := by
      rw [show q x ^ r = q x ^ (1 : ℝ) * q x ^ (r - 1) from by calc
        q x ^ r = q x ^ (1 + (r - 1)) := congrArg (fun t : ℝ => q x ^ t) he
        _ = _ := Real.rpow_add hx _ _]
      simp only [DiagonalScale.logPowerWeight, ← mul_assoc, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hx.le (r - 1))]
    _ ≤ 1 * q x ^ (r - 1) :=
      mul_le_mul_of_nonneg_right hsx (Real.rpow_nonneg hx.le _)

theorem raw_log_jetRate {l : Filter E} {q : E → ℝ} {A : ℕ → E → V}
    {g L : ℕ → ℝ} {C P : ℕ → ℕ → ℝ} {U : Set E}
    (hraw : CutStageEstimates.RawStageBounds q A g L C P U)
    (hlU : ∀ᶠ x in l, x ∈ U) (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hqzero : Tendsto q l (𝓝 0)) {j : ℕ} (hj : 1 ≤ j) (m : ℕ) :
    JetRate l q (A j) m (g j - L m - 1) := by
  apply jetRate_of_log_bound (hq.mono (fun _ h => h.1)) hqzero m (C j m) (P j m)
  filter_upwards [hlU, hq] with x hx hqx
  exact hraw j hj m x hx hqx.2

theorem stage_growth {l : Filter E} {q : E → ℝ} {base : E → V}
    {A : ℕ → E → V} {g L Lbase : ℕ → ℝ} {C P : ℕ → ℕ → ℝ} {U : Set E}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1) (hqzero : Tendsto q l (𝓝 0))
    (hbase : ContDiffOn ℝ ∞ base U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hraw : CutStageEstimates.RawStageBounds q A g L C P U)
    (hg : ∀ j, 1 ≤ j → 0 ≤ g j)
    (hbg : ∀ m, JetRate l q base m (-Lbase m)) (J m : ℕ) :
    JetRate l q (stage base A J) m (-max (L m + 1) (Lbase m)) := by
  have hzero : JetRate l q (CutStageEstimates.positiveStages A 0) m
      (-max (L m + 1) (Lbase m)) := by
    rw [CutStageEstimates.positiveStages_zero]
    refine ⟨0, le_rfl, Filter.Eventually.of_forall (fun x => ?_)⟩
    simp
  have hp := MixedFiniteBackground.nonemptyPrefix_jetRate hU hlU
    (CutStageEstimates.positiveStages_smooth hA) hzero (fun j hj => ?_) J
  · exact ((hbg m).weaken hq (neg_le_neg (le_max_right _ _))).add hp hU hlU hbase
      (ContDiffOn.sum (fun j _ => CutStageEstimates.positiveStages_smooth hA j))
  · rw [CutStageEstimates.positiveStages_of_pos hj]
    apply (raw_log_jetRate hraw hlU hq hqzero hj m).weaken hq
    have hgain := hg j hj
    have hmax := le_max_left (L m + 1) (Lbase m)
    linarith

theorem realized_tail_jetRate {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : E → ℝ} {base : E → V} {A : ℕ → E → V} {g L : ℕ → ℝ}
    {U : Set E} {l : Filter E} (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U) (hg : Monotone g)
    (hb : DiagonalJetBounds.CutStageBounds a q A g L U)
    (hlU : ∀ᶠ x in l, x ∈ U) (hlq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hqzero : Tendsto q l (𝓝 0)) (J m : ℕ) (hm : m ≤ J + 3) :
    JetRate l q (fun x => realized a q base A x - stage base A J x)
      m (g (J + 1) - L m) := by
  have ht := jetRate_diagonal_tail ha hU hq
    (CutStageEstimates.positiveStages_smooth hA) hg
    (CutStageEstimates.positiveStages_cut_bounds hb) hlU hlq hqzero J m hm
  apply ht.congr_on hU hlU
  intro x hx
  simp only [realized, stage]
  abel

omit [NormedSpace ℝ E] in
/-- The entire finite prefix is on the constant plateau on the exact interval
printed in the realization lemma. -/
theorem prefix_eventually_uncut {a : ℕ → ℝ} (ha : Monotone a)
    (hapos : ∀ j, 0 < a j) {q : E → ℝ} {x : E}
    (hq : ContinuousAt q x) (hqx : 0 < q x) {J : ℕ}
    (hsmall : q x < 1 / (2 * a J)) (A : ℕ → E → V) :
    SolenoidalDiagonal.partialPotential a q A (J + 1) =ᶠ[𝓝 x]
      DiagonalJetBounds.uncutPrefix A (J + 1) := by
  have hprod : a J * q x < 1 / 2 := by
    have := (lt_div_iff₀ (mul_pos (by norm_num) (hapos J))).mp hsmall
    nlinarith
  have hnear : ∀ᶠ y in 𝓝 x, 0 < q y ∧ a J * q y < 1 / 2 := by
    exact (hq.eventually (lt_mem_nhds hqx)).and
      ((continuousAt_const.mul hq).eventually (gt_mem_nhds hprod))
  filter_upwards [hnear] with y hy
  unfold SolenoidalDiagonal.partialPotential DiagonalJetBounds.uncutPrefix
  apply Finset.sum_congr rfl
  intro j hj
  have hjJ : j ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hlow : 0 ≤ a j * q y := mul_nonneg (hapos j).le hy.1.le
  have hhigh : a j * q y ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right (ha hjJ) hy.1.le).trans hy.2.le
  rw [SolenoidalDiagonal.cutStage,
    SmoothCutoffs.scaledCutoff_one_of_abs_le (by rwa [abs_of_nonneg hlow]), one_smul]

/-- Exact geometric tail, for each derivative, on `0 < q < 1/(2 a_J)`.
The derivative loss is independent of the truncation index. -/
theorem realized_tail_bound {a : ℕ → ℝ} (hatop : Tendsto a atTop atTop)
    (ha : Monotone a) (hapos : ∀ j, 0 < a j)
    {q : E → ℝ} {base : E → V} {A : ℕ → E → V} {g L : ℕ → ℝ}
    {U : Set E} (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U) (hg : Monotone g)
    (hb : DiagonalJetBounds.CutStageBounds a q A g L U)
    {x : E} (hx : x ∈ U) (hqx : 0 < q x) (hq1 : q x ≤ 1)
    (J m : ℕ) (hm : m ≤ J + 3) (hsmall : q x < 1 / (2 * a J)) :
    ‖iteratedFDeriv ℝ m (fun y => realized a q base A y - stage base A J y) x‖ ≤
      (1 / 2 : ℝ) ^ J * q x ^ (g (J + 1) - L m) := by
  have hp := prefix_eventually_uncut ha hapos
    (hq.contDiffAt (hU.mem_nhds hx)).continuousAt hqx hsmall
      (CutStageEstimates.positiveStages A)
  have heq :
      (fun y => SolenoidalDiagonal.potentialSum a q (CutStageEstimates.positiveStages A) y -
        SolenoidalDiagonal.partialPotential a q (CutStageEstimates.positiveStages A) (J + 1) y)
        =ᶠ[𝓝 x] (fun y => realized a q base A y - stage base A J y) := by
    filter_upwards [hp] with y hy
    simp only [realized, stage, hy]
    abel
  rw [← (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq heq m).self_of_nhds]
  exact DiagonalJetBounds.potential_tail_jet_bound hatop hU hq
    (CutStageEstimates.positiveStages_smooth hA) hg
    (CutStageEstimates.positiveStages_cut_bounds hb) hx hqx hq1 J m hm

omit [NormedSpace ℝ E] in
/-- The added series is identically zero on an entire neighborhood of any
outer-boundary point beyond the first support. This proves compatible zero
extension without imposing regularity of the uncut representatives outside. -/
theorem correction_eventually_zero {a : ℕ → ℝ} (ha : Monotone a)
    (hapos : ∀ j, 0 < a j) {q : E → ℝ} {x : E} (hq : ContinuousAt q x)
    (houter : 1 / a 0 < q x) (A : ℕ → E → V) :
    SolenoidalDiagonal.potentialSum a q A =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [hq.eventually (lt_mem_nhds houter)] with y hy
  unfold SolenoidalDiagonal.potentialSum
  have hzero : ∀ j, SolenoidalDiagonal.cutStage a q A j y = 0 := by
    intro j
    rw [SolenoidalDiagonal.cutStage,
      SmoothCutoffs.scaledCutoff_zero_of_inv_le (hapos j), zero_smul]
    exact ((one_div_le_one_div_of_le (hapos 0) (ha (Nat.zero_le j))).trans hy.le)
  simp only [hzero, tsum_zero]


/-- The flat error in the finite residual hypothesis may be an arbitrary
nonnegative majorant; it need not itself be a derivative or a smooth field. -/
theorem jetRate_of_log_bound_add_flat {l : Filter E} {q : E → ℝ} {f : E → V}
    {error : E → ℝ} (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hqzero : Tendsto q l (𝓝 0)) (m : ℕ) (C P r : ℝ)
    (hb : ∀ᶠ x in l, ‖iteratedFDeriv ℝ m f x‖ ≤
      C * (1 + |Real.log (q x)|) ^ P * q x ^ r + error x)
    (he : ∀ N : ℕ, ∃ Ce : ℝ, 0 ≤ Ce ∧
      ∀ᶠ x in l, error x ≤ Ce * q x ^ N) : JetRate l q f m (r - 1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (r - 1)
  obtain ⟨Ce, hCe, heN⟩ := he N
  have hqright : Tendsto q l (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hqzero, hq.mono fun _ hx => hx.1⟩
  have ht := ((DiagonalScale.tendsto_logPowerWeight C P 1 zero_lt_one).comp hqright).abs
  simp only [abs_zero] at ht
  have hs : ∀ᶠ x in l, |DiagonalScale.logPowerWeight C P 1 (q x)| ≤ 1 := by
    simpa only [Function.comp_def] using
      (ht.eventually (gt_mem_nhds zero_lt_one)).mono (fun _ h => h.le)
  refine ⟨1 + Ce, by positivity, ?_⟩
  filter_upwards [hq, hb, heN, hs] with x hx hbx hex hsx
  have hpower : q x ^ r = q x ^ (1 : ℝ) * q x ^ (r - 1) := by
    calc
      _ = q x ^ (1 + (r - 1)) := by congr 1; ring
      _ = _ := Real.rpow_add hx.1 _ _
  have hlog : C * (1 + |Real.log (q x)|) ^ P * q x ^ r ≤ q x ^ (r - 1) := by
    calc
      _ ≤ |C * (1 + |Real.log (q x)|) ^ P * q x ^ r| := le_abs_self _
      _ = |DiagonalScale.logPowerWeight C P 1 (q x)| * q x ^ (r - 1) := by
        rw [hpower]
        simp only [DiagonalScale.logPowerWeight, ← mul_assoc, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg hx.1.le (r - 1))]
      _ ≤ 1 * q x ^ (r - 1) :=
        mul_le_mul_of_nonneg_right hsx (Real.rpow_nonneg hx.1.le _)
      _ = _ := one_mul _
  have herr : error x ≤ Ce * q x ^ (r - 1) := by
    apply hex.trans
    rw [← Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 hN) hCe
  exact hbx.trans ((add_le_add hlog herr).trans_eq (by ring))

omit [NormedSpace ℝ E] in
/-- Local finiteness lets individually vanishing representative germs pass to
the sum, without assuming one neighborhood works for every stage. -/
theorem potentialSum_zero_germ {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : E → ℝ} {x : E} (hq : ContinuousAt q x) (hpos : 0 < q x)
    (A : ℕ → E → V) (hA : ∀ j, A j =ᶠ[𝓝 x] fun _ => 0) :
    SolenoidalDiagonal.potentialSum a q A =ᶠ[𝓝 x] fun _ => 0 := by
  obtain ⟨N, hN⟩ := SolenoidalDiagonal.potentialSum_eventuallyEq_partial ha hq hpos A
  have hz (j : ℕ) : SolenoidalDiagonal.cutStage a q A j =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hA j] with y hy
    simp only [SolenoidalDiagonal.cutStage, hy, smul_zero]
  apply hN.trans
  filter_upwards [(Filter.eventually_all_finset (Finset.range N)).2 (fun j _ => hz j)] with y hy
  exact Finset.sum_eq_zero hy



end NavierStokes.GenericRealizationBounds
end

noncomputable section

namespace NavierStokes.GenericDifferentialPolynomial

open Set Filter DiagonalResidual
open scoped Topology ContDiff BigOperators

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {l : Filter D} {q : D → ℝ} {U S : Set D}

theorem rate_filter_mono {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l' : Filter D} (hl : l' ≤ l) {f : D → V} {m : ℕ} {r : ℝ}
    (hf : JetRate l q f m r) : JetRate l' q f m r := by
  obtain ⟨C, hC, hb⟩ := hf
  exact ⟨C, hC, hb.filter_mono hl⟩

def ApproximationRates.filter_mono {f : D → ℝ} {fs : ℕ → D → ℝ} {gain : ℕ → ℝ}
    (h : ApproximationRates l q gain f fs) {l' : Filter D} (hl : l' ≤ l) :
    ApproximationRates l' q gain f fs where
  growthLoss := h.growthLoss
  tailLoss := h.tailLoss
  threshold := h.threshold
  stage_growth J m := rate_filter_mono hl (h.stage_growth J m)
  tail_rate m J hJ := rate_filter_mono hl (h.tail_rate m J hJ)

/-- Restrict coefficient growth to the common support region. Outside that
region the field factor vanishes on a neighborhood, so every derivative of
its product with the coefficient is zero. -/
theorem rate_of_restricted_support {f : D → ℝ} {m : ℕ} {r : ℝ}
    (hq : ∀ᶠ x in l, 0 < q x) (hlU : ∀ᶠ x in l, x ∈ U)
    (hr : JetRate (l ⊓ 𝓟 S) q f m r)
    (hsupport : ∀ x ∈ U, x ∉ S → f =ᶠ[𝓝 x] (fun _ => 0)) : JetRate l q f m r := by
  obtain ⟨C, hC, hb⟩ := hr
  have hb' : ∀ᶠ x in l, x ∈ S → ‖iteratedFDeriv ℝ m f x‖ ≤ C * q x ^ r :=
    eventually_inf_principal.mp hb
  refine ⟨C, hC, ?_⟩
  filter_upwards [hq, hb', hlU] with x hx hbx hxU
  by_cases hs : x ∈ S
  · exact hbx hs
  · have heq := (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq (hsupport x hxU hs) m).self_of_nhds
    rw [heq]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using
      mul_nonneg hC (Real.rpow_nonneg hx.le r)

/-- Tail data suffice for residual transfer; a coefficient independent of the
fields cancels exactly and therefore needs no growth bound in this step. -/
structure TailRates (l : Filter D) (q : D → ℝ) (gain : ℕ → ℝ)
    (f : D → ℝ) (stage : ℕ → D → ℝ) where
  loss : ℕ → ℝ
  threshold : ℕ → ℕ
  rate : ∀ m J, threshold m ≤ J →
    JetRate l q (fun x => f x - stage J x) m (gain J - loss m)

def ApproximationRates.tail {gain : ℕ → ℝ} {f : D → ℝ} {fs : ℕ → D → ℝ}
    (a : ApproximationRates l q gain f fs) : TailRates l q gain f fs :=
  ⟨a.tailLoss, a.threshold, a.tail_rate⟩

/-- Only common-support coefficient bounds are assumed. In particular, the
coefficient may grow arbitrarily fast away from the supports. -/
def ApproximationRates.mul_coefficient_local
    {gain : ℕ → ℝ} {f c : D → ℝ} {fs : ℕ → D → ℝ}
    (a : ApproximationRates l q gain f fs)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U) (hfs : ∀ J, ContDiffOn ℝ ∞ (fs J) U)
    (hc : ContDiffOn ℝ ∞ c U) (Lc : ℕ → ℝ)
    (hcg : ∀ m, JetRate (l ⊓ 𝓟 S) q c m (-Lc m))
    (hzero : ∀ x ∈ U, x ∉ S → f =ᶠ[𝓝 x] (fun _ => 0))
    (hszero : ∀ J x, x ∈ U → x ∉ S → fs J =ᶠ[𝓝 x] (fun _ => 0)) :
    TailRates l q gain (fun x => c x * f x) (fun J x => c x * fs J x) := by
  let b := a.filter_mono (show l ⊓ 𝓟 S ≤ l from inf_le_left)
  let M : ℕ → ℕ := fun m => (Finset.range (m + 1)).sup a.threshold
  refine ⟨fun m => maxJetLoss Lc m + maxJetLoss a.tailLoss m, M, ?_⟩
  intro m J hJ
  have hqr : ∀ᶠ x in l ⊓ 𝓟 S, 0 < q x ∧ q x ≤ 1 := hq.filter_mono inf_le_left
  have hcr : FiniteJetRate (l ⊓ 𝓟 S) q c m (-maxJetLoss Lc m) := by
    apply finiteJetRate_of_jetRate (hqr.mono fun _ hx => hx.1)
    intro k hk
    exact (hcg k).weaken hqr (neg_le_neg (le_maxJetLoss Lc hk))
  have htr : FiniteJetRate (l ⊓ 𝓟 S) q (fun x => f x - fs J x) m
      (gain J - maxJetLoss a.tailLoss m) := by
    apply finiteJetRate_of_jetRate (hqr.mono fun _ hx => hx.1)
    intro k hk
    have ht : a.threshold k ≤ J :=
      (Finset.le_sup (f := a.threshold) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).trans hJ
    exact (rate_filter_mono inf_le_left (a.tail_rate k J ht)).weaken hqr
      (sub_le_sub_left (le_maxJetLoss a.tailLoss hk) _)
  have hr := rate_mul hU (hlU.filter_mono inf_le_left) hqr hc (hf.sub (hfs J)) hcr htr
  have hr' : JetRate (l ⊓ 𝓟 S) q (fun x => c x * f x - c x * fs J x) m
      (gain J - (maxJetLoss Lc m + maxJetLoss a.tailLoss m)) := by
    convert hr.congr_on hU (hlU.filter_mono inf_le_left)
      (show EqOn (fun x => c x * (f x - fs J x))
        (fun x => c x * f x - c x * fs J x) U from fun x _ => mul_sub _ _ _) using 1
    ring
  apply rate_of_restricted_support (hq.mono fun _ hx => hx.1) hlU hr'
  intro x hxU hx
  filter_upwards [hzero x hxU hx, hszero J x hxU hx] with y hy hsy
  simp only [hy, hsy, mul_zero, sub_self]

/-- Finite sums preserve a stage-independent loss and threshold. -/
def TailRates.add {gain : ℕ → ℝ} {f g : D → ℝ} {fs gs : ℕ → D → ℝ}
    (a : TailRates l q gain f fs) (b : TailRates l q gain g gs)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hfs : ∀ J, ContDiffOn ℝ ∞ (fs J) U) (hgs : ∀ J, ContDiffOn ℝ ∞ (gs J) U) :
    TailRates l q gain (fun x => f x + g x) (fun J x => fs J x + gs J x) where
  loss m := max (a.loss m) (b.loss m)
  threshold m := max (a.threshold m) (b.threshold m)
  rate m J hJ := by
    have ha := (a.rate m J ((le_max_left _ _).trans hJ)).weaken hq
      (sub_le_sub_left (le_max_left (a.loss m) (b.loss m)) _)
    have hb := (b.rate m J ((le_max_right _ _).trans hJ)).weaken hq
      (sub_le_sub_left (le_max_right (a.loss m) (b.loss m)) _)
    exact (ha.add hb hU hlU (hf.sub (hfs J)) (hg.sub (hgs J))).congr_on hU hlU
      (fun x _ => by dsimp; ring)

def TailRates.fixed {gain : ℕ → ℝ} (c : D → ℝ) :
    TailRates l q gain c (fun _ => c) where
  loss := 0
  threshold := 0
  rate m J _ := by simpa only [sub_self] using (rate_zero (l := l) (q := q)
    (m := m) (r := gain J - (0 : ℕ → ℝ) m))

/-- The finite residual decay order and the correction decay order are
independent sequences. Both may grow arbitrarily slowly. -/
theorem TailRates.flat_of_residuals {gain rho : ℕ → ℝ} {f : D → ℝ} {fs : ℕ → D → ℝ}
    (a : TailRates l q gain f fs)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U) (hfs : ∀ J, ContDiffOn ℝ ∞ (fs J) U)
    (hgain : Tendsto gain atTop atTop) (hrho : Tendsto rho atTop atTop)
    (Lres : ℕ → ℝ) (hres : ∀ J m, JetRate l q (fs J) m (rho J - Lres m))
    (m : ℕ) (n : ℝ) : JetRate l q f m n := by
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1
    ((hgain.eventually (eventually_ge_atTop (n + a.loss m))).and
      (hrho.eventually (eventually_ge_atTop (n + Lres m))))
  let J := max (a.threshold m) J₀
  have hj := hJ₀ J (le_max_right _ _)
  have ht := (a.rate m J (le_max_left _ _)).weaken hq (by linarith [hj.1] : n ≤ gain J - a.loss m)
  have hr := (hres J m).weaken hq (by linarith [hj.2] : n ≤ rho J - Lres m)
  exact (hr.add ht hU hlU (hfs J) (hf.sub (hfs J))).congr_on hU hlU
    (fun x _ => by dsimp; ring)

/-- A field-only differential expression inherits a common zero germ from all
its input components, including after any fixed number of derivatives. -/
theorem Expression.zero_germ {ι : Type*} (e : Expression D ι Empty)
    {u : ι → D → ℝ} {x : D}
    (hu : ∀ i, u i =ᶠ[𝓝 x] (fun _ => 0)) :
    e.eval (fun k => Empty.elim k) u =ᶠ[𝓝 x] (fun _ => 0) := by
  induction e with
  | input i => exact hu i
  | coeff k => exact Empty.elim k
  | add a b ha hb =>
      filter_upwards [ha, hb] with y hy hz
      simp only [Expression.eval, hy, hz, add_zero]
  | mul a b ha hb =>
      filter_upwards [ha, hb] with y hy hz
      simp only [Expression.eval, hy, hz, mul_zero]
  | directional v a ha =>
      have hd := ha.fderiv (𝕜 := ℝ)
      filter_upwards [hd] with y hy
      change fderiv ℝ (a.eval (fun k => Empty.elim k) u) y v = 0
      rw [hy]
      simp

/-- A finite differential polynomial in normal form, allowing coefficients
whose growth bounds are local to a different common support for every term. -/
structure SupportedPolynomial (D ι : Type*) where
  constant : D → ℝ
  terms : List ((D → ℝ) × Expression D ι Empty)

namespace SupportedPolynomial

variable {ι : Type*}

def evalTerms (u : ι → D → ℝ) : List ((D → ℝ) × Expression D ι Empty) → D → ℝ
  | [] => fun _ => 0
  | (c, e) :: es => fun x => c x * e.eval (fun k => Empty.elim k) u x + evalTerms u es x

def eval (P : SupportedPolynomial D ι) (u : ι → D → ℝ) : D → ℝ :=
  fun x => P.constant x + evalTerms u P.terms x

theorem smooth_evalTerms (terms : List ((D → ℝ) × Expression D ι Empty))
    {u : ι → D → ℝ} (hU : IsOpen U)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hc : ∀ t ∈ terms, ContDiffOn ℝ ∞ t.1 U) :
    ContDiffOn ℝ ∞ (evalTerms u terms) U := by
  induction terms with
  | nil => exact contDiffOn_const
  | cons t ts ih =>
      exact ((hc t (by simp)).mul
        (t.2.smooth_eval hU (fun k => Empty.elim k) hu)).add
          (ih (fun v hv => hc v (by simp [hv])))

theorem smooth_eval (P : SupportedPolynomial D ι) {u : ι → D → ℝ}
    (hU : IsOpen U) (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hconst : ContDiffOn ℝ ∞ P.constant U)
    (hc : ∀ t ∈ P.terms, ContDiffOn ℝ ∞ t.1 U) :
    ContDiffOn ℝ ∞ (P.eval u) U :=
  hconst.add (smooth_evalTerms P.terms hU hu hc)

/-- The support condition quantifies over one common neighborhood for all
field components in a monomial, uniformly in the truncation. Coefficients
are required to have controlled growth only on that monomial's region. -/
def termTail {gain : ℕ → ℝ} {u : ι → D → ℝ} {us : ℕ → ι → D → ℝ}
    (t : (D → ℝ) × Expression D ι Empty)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hus : ∀ J i, ContDiffOn ℝ ∞ (us J i) U)
    (hgain : Tendsto gain atTop atTop)
    (ha : ∀ i, ApproximationRates l q gain (u i) (fun J => us J i))
    (hc : ContDiffOn ℝ ∞ t.1 U) (S : Set D) (Lc : ℕ → ℝ)
    (hcg : ∀ m, JetRate (l ⊓ 𝓟 S) q t.1 m (-Lc m))
    (hzero : ∀ x ∈ U, x ∉ S → t.2.eval (fun k => Empty.elim k) u =ᶠ[𝓝 x] (fun _ => 0))
    (hszero : ∀ J x, x ∈ U → x ∉ S →
      t.2.eval (fun k => Empty.elim k) (us J) =ᶠ[𝓝 x] (fun _ => 0)) :
    TailRates l q gain (fun x => t.1 x * t.2.eval (fun k => Empty.elim k) u x)
      (fun J x => t.1 x * t.2.eval (fun k => Empty.elim k) (us J) x) :=
  (t.2.approximation_eval hU hlU hq (fun k => Empty.elim k) hu hus hgain
    (fun k => Empty.elim k) (fun k => Empty.elim k) ha).mul_coefficient_local
      hU hlU hq (t.2.smooth_eval hU (fun k => Empty.elim k) hu)
      (fun J => t.2.smooth_eval hU (fun k => Empty.elim k) (hus J))
      hc Lc hcg hzero hszero

def termsTail {gain : ℕ → ℝ} {u : ι → D → ℝ} {us : ℕ → ι → D → ℝ}
    (terms : List ((D → ℝ) × Expression D ι Empty))
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hus : ∀ J i, ContDiffOn ℝ ∞ (us J i) U)
    (hc : ∀ t ∈ terms, ContDiffOn ℝ ∞ t.1 U)
    (ht : ∀ t ∈ terms,
      TailRates l q gain (fun x => t.1 x * t.2.eval (fun k => Empty.elim k) u x)
        (fun J x => t.1 x * t.2.eval (fun k => Empty.elim k) (us J) x)) :
    TailRates l q gain (evalTerms u terms) (fun J => evalTerms (us J) terms) := by
  induction terms with
  | nil => exact TailRates.fixed (fun _ => 0)
  | cons t ts ih =>
      exact (ht t (by simp)).add
        (ih (fun v hv => hc v (by simp [hv])) (fun v hv => ht v (by simp [hv])))
        hU hlU hq
        ((hc t (by simp)).mul (t.2.smooth_eval hU (fun k => Empty.elim k) hu))
        (smooth_evalTerms ts hU hu (fun v hv => hc v (by simp [hv])))
        (fun J => (hc t (by simp)).mul (t.2.smooth_eval hU (fun k => Empty.elim k) (hus J)))
        (fun J => smooth_evalTerms ts hU (hus J) (fun v hv => hc v (by simp [hv])))

/-- Full finite-polynomial residual transfer, with the term independent of
fields retained in the residual hypothesis and canceled in the comparison. -/
theorem flat_of_local_coefficients (P : SupportedPolynomial D ι)
    {gain rho : ℕ → ℝ} {u : ι → D → ℝ} {us : ℕ → ι → D → ℝ}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hus : ∀ J i, ContDiffOn ℝ ∞ (us J i) U)
    (hgain : Tendsto gain atTop atTop) (hrho : Tendsto rho atTop atTop)
    (ha : ∀ i, ApproximationRates l q gain (u i) (fun J => us J i))
    (hconst : ContDiffOn ℝ ∞ P.constant U)
    (hc : ∀ t ∈ P.terms, ContDiffOn ℝ ∞ t.1 U)
    (region : ((D → ℝ) × Expression D ι Empty) → Set D)
    (Lc : ((D → ℝ) × Expression D ι Empty) → ℕ → ℝ)
    (hcg : ∀ t ∈ P.terms, ∀ m, JetRate (l ⊓ 𝓟 (region t)) q t.1 m (-Lc t m))
    (hzero : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      t.2.eval (fun k => Empty.elim k) u =ᶠ[𝓝 x] (fun _ => 0))
    (hszero : ∀ t ∈ P.terms, ∀ J x, x ∈ U → x ∉ region t →
      t.2.eval (fun k => Empty.elim k) (us J) =ᶠ[𝓝 x] (fun _ => 0))
    (Lres : ℕ → ℝ)
    (hres : ∀ J m, JetRate l q (P.eval (us J)) m (rho J - Lres m))
    (m : ℕ) (n : ℝ) : JetRate l q (P.eval u) m n := by
  let ht := termsTail P.terms hU hlU hq hu hus hc (fun t ht =>
    termTail t hU hlU hq hu hus hgain ha (hc t ht) (region t) (Lc t)
      (hcg t ht) (hzero t ht) (hszero t ht))
  let hp := (TailRates.fixed P.constant).add ht hU hlU hq hconst
    (smooth_evalTerms P.terms hU hu hc) (fun _ => hconst)
      (fun J => smooth_evalTerms P.terms hU (hus J) hc)
  exact hp.flat_of_residuals hU hlU hq (P.smooth_eval hU hu hconst hc)
    (fun J => P.smooth_eval hU (hus J) hconst hc) hgain hrho Lres hres m n

end SupportedPolynomial

end NavierStokes.GenericDifferentialPolynomial

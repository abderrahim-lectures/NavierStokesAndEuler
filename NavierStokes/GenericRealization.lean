import NavierStokes.CutStageEstimates
import NavierStokes.GenericSupportedPolynomial

/-!
# A single smooth diagonal realization with finite differential-polynomial tests

All estimates are on the actual cutoff series. The same schedule supplies every
jet order and an arbitrary finite set of extra tests at each stage. Residual
transfer permits independently varying residual gains and coefficient growth
only on the common support of each nonconstant monomial.
-/
/-! Merged from `NavierStokes.GenericDiagonalSchedule` (in a section, so its `open`s cannot leak). -/
section
/-!
# A common diagonal schedule with arbitrary additional finite tests

The same sequence of cutoff scales enforces all field jet estimates and any
prescribed finite family of positive-power logarithmic tests at each stage.
The bounds apply throughout the reciprocal interval, including its endpoint.
-/

noncomputable section

namespace NavierStokes.GenericDiagonalSchedule

open Set Function Filter
open scoped Topology ContDiff BigOperators

/-- The logarithmic power and the positive decay power may both depend on the
individual member of the finite family. -/
theorem exists_integer_scale_variable {κ : Type*} (s : Finset κ)
    (B P γ : κ → ℝ) (hγ : ∀ k ∈ s, 0 < γ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℕ, 0 < a ∧ ∀ k ∈ s, ∀ r : ℝ, 0 < r → r ≤ 1 / (a : ℝ) →
      |DiagonalScale.logPowerWeight (B k) (P k) (γ k) r| ≤ ε := by
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ k ∈ s, |DiagonalScale.logPowerWeight (B k) (P k) (γ k) r| < ε := by
    apply (eventually_all_finset s).2
    intro k hk
    have hlim := (DiagonalScale.tendsto_logPowerWeight (B k) (P k) (γ k) (hγ k hk)).abs
    simp only [abs_zero] at hlim
    exact hlim.eventually (gt_mem_nhds hε)
  rcases mem_nhdsGT_iff_exists_Ioo_subset.1 hsmall with ⟨δ, hδ, hb⟩
  change (0 : ℝ) < δ at hδ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n + 1, Nat.succ_pos _, ?_⟩
  intro k hk r hr hra
  apply (hb ⟨hr, ?_⟩ k hk).le
  apply hra.trans_lt
  simpa only [Nat.cast_add, Nat.cast_one] using hn

/-- One doubling sequence dominates any prescribed sequence of lower bounds
and meets an arbitrary finite list of tests at each stage. All cutoff supports
lie strictly below the prescribed positive outer boundary. -/
theorem exists_scales_with_tests {κ : Type*} (tests : ℕ → Finset κ)
    (B P γ : ℕ → κ → ℝ) (hγ : ∀ j k, k ∈ tests j → 0 < γ j k)
    (lower : ℕ → ℕ) {q0 : ℝ} (hq0 : 0 < q0) :
    ∃ a : ℕ → ℕ, (∀ j, lower j ≤ a j) ∧ (∀ j, 0 < a j) ∧
      (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      (∀ j, 1 / (a j : ℝ) < q0) ∧
      ∀ j k, k ∈ tests j → ∀ r : ℝ, 0 < r → r ≤ 1 / (a j : ℝ) →
        |DiagonalScale.logPowerWeight (B j k) (P j k) (γ j k) r| ≤
          (1 / 2 : ℝ) ^ j := by
  choose b hb htest using fun j =>
    exists_integer_scale_variable (tests j) (B j) (P j) (γ j) (hγ j)
      (show (0 : ℝ) < (1 / 2) ^ j by positivity)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hq0
  let c : ℕ → ℕ := fun j => max (lower j) (max (b j) (n + 1))
  let a := DiagonalScale.doublingEnvelope c
  have hca : ∀ j, c j ≤ a j := DiagonalScale.doublingEnvelope_ge c
  have hba : ∀ j, b j ≤ a j := fun j =>
    ((le_max_left _ _).trans (le_max_right _ _)).trans (hca j)
  have hna : ∀ j, n + 1 ≤ a j := fun j =>
    ((le_max_right _ _).trans (le_max_right _ _)).trans (hca j)
  have hmono : StrictMono a := DiagonalScale.doublingEnvelope_strictMono c
  refine ⟨a, fun j => (le_max_left _ _).trans (hca j),
    DiagonalScale.doublingEnvelope_pos c, DiagonalScale.doublingEnvelope_growth c,
    hmono, SolenoidalDiagonal.realScales_tendsto hmono, ?_, ?_⟩
  · intro j
    apply (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))
      (by exact_mod_cast hna j)).trans_lt
    simpa only [Nat.cast_add, Nat.cast_one] using hn
  · intro j k hk r hr hra
    apply htest j k hk r hr
    exact hra.trans (one_div_le_one_div_of_le (by exact_mod_cast hb j)
      (by exact_mod_cast hba j))

section Fields

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- The realization schedule and the additional normalized coefficient tests
are imposed simultaneously, for one finite heterogeneous family of fields. -/
theorem exists_finite_diagonal_cut_bounds_with_tests {U S : Set E}
    (hU : IsOpen U) (hSU : S ⊆ U) {q : E → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ x ∈ S, 0 < q x)
    (Bq : ℕ → ℝ)
    (hBq : ∀ k x, x ∈ S → q x ≤ 1 →
      ‖iteratedFDeriv ℝ k q x‖ ≤ Bq k * q x ^ (1 - (k : ℝ)))
    {A : ∀ i, ℕ → E → W i} (hA : ∀ i j, 1 ≤ j → ContDiffOn ℝ ∞ (A i j) U)
    (g L : ℕ → ℝ) (C p : ι → ℕ → ℕ → ℝ)
    (hraw : ∀ i, CutStageEstimates.RawStageBounds q (A i) g L (C i) (p i) S)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (lower : ℕ)
    {κ : Type*} (tests : ℕ → Finset κ) (B P γ : ℕ → κ → ℝ)
    (hγ : ∀ j k, k ∈ tests j → 0 < γ j k) {q0 : ℝ} (hq0 : 0 < q0) :
    ∃ a : ℕ → ℕ, lower ≤ a 0 ∧ (∀ j, 0 < a j) ∧
      (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      (∀ j, 1 / (a j : ℝ) < q0) ∧
      (∀ i, DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ)) q (A i)
        (fun j => g j / 2) (CutStageEstimates.cutLoss L) S) ∧
      ∀ j k, k ∈ tests j → ∀ r : ℝ, 0 < r → r ≤ 1 / (a j : ℝ) →
        |DiagonalScale.logPowerWeight (B j k) (P j k) (γ j k) r| ≤
          (1 / 2 : ℝ) ^ j := by
  classical
  choose K hK hb using fun i =>
    CutStageEstimates.exists_cut_stage_constants hU hSU hq hpos Bq hBq
      (hA i) g L (C i) (p i) (hraw i)
  let Kall : ℕ → ℕ → ℝ := fun j m => 1 + ∑ i, |K i j m|
  let Pall : ℕ → ℕ → ℝ := fun j m => 1 + ∑ i, |CutStageEstimates.cutLog (p i) j m|
  have hKall : ∀ j m, 0 < Kall j m := by
    intro j m
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (K i j m))
    dsimp only [Kall]
    linarith
  have hKle : ∀ i j m, K i j m ≤ Kall j m := by
    intro i j m
    exact (le_abs_self _).trans ((Finset.single_le_sum (fun i _ => abs_nonneg (K i j m))
      (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one))
  have hPle : ∀ i j m, CutStageEstimates.cutLog (p i) j m ≤ Pall j m := by
    intro i j m
    exact (le_abs_self _).trans ((Finset.single_le_sum
      (fun i _ => abs_nonneg (CutStageEstimates.cutLog (p i) j m)) (Finset.mem_univ i)).trans
        (le_add_of_nonneg_left zero_le_one))
  obtain ⟨b, hblower, hbpos, _, _, _, hbsmall⟩ :=
    DiagonalScale.exists_diagonal_scales Kall Pall g hg lower
  obtain ⟨a, hba, hapos, hadouble, hamono, hatop, haouter, hatest⟩ :=
    exists_scales_with_tests tests B P γ hγ b hq0
  refine ⟨a, hblower.trans (hba 0), hapos, hadouble, hamono, hatop, haouter, ?_, hatest⟩
  intro i j hj m hm x hx
  apply CutStageEstimates.cut_product_bound_of_threshold hU hSU hq hpos (hA i j hj) m
    (show (1 : ℝ) ≤ (a j : ℝ) by exact_mod_cast (Nat.succ_le_of_lt (hapos j))) (by positivity) (K := Kall j m) (P := Pall j m)
    (g := g j) (L := CutStageEstimates.cutLoss L m) ?_ ?_ x hx
  · intro c hc y hy hq1
    apply (hb i j hj m c hc y hy hq1).trans
    have hlog : 1 ≤ 1 + |Real.log (q y)| := le_add_of_nonneg_right (abs_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hpos y hy).le _)
    calc
      _ ≤ Kall j m * (1 + |Real.log (q y)|) ^ (CutStageEstimates.cutLog (p i) j m) :=
        mul_le_mul_of_nonneg_right (hKle i j m) (Real.rpow_nonneg (by positivity) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hlog (hPle i j m)) (hKall j m).le
  · intro r hr hra
    exact hbsmall j hj m hm r hr
      (hra.trans (one_div_le_one_div_of_le (by exact_mod_cast hbpos j)
        (show (b j : ℝ) ≤ (a j : ℝ) by exact_mod_cast hba j)))

end Fields

end NavierStokes.GenericDiagonalSchedule
end


noncomputable section

namespace NavierStokes.GenericRealization

open Set Filter DiagonalResidual GenericRealizationBounds GenericDifferentialPolynomial
open scoped Topology ContDiff BigOperators

variable {D : Type*}

/-- Approach the singular scale uniformly over the full prescribed domain. -/
def scaleApproach (U : Set D) (q : D → ℝ) : Filter D :=
  comap q (𝓝[>] (0 : ℝ)) ⊓ 𝓟 U

theorem eventually_domain (U : Set D) (q : D → ℝ) :
    ∀ᶠ x in scaleApproach U q, x ∈ U :=
  Filter.Eventually.filter_mono inf_le_right (show ∀ᶠ x in 𝓟 U, x ∈ U from by simp)

theorem scale_tendsto (U : Set D) (q : D → ℝ) :
    Tendsto q (scaleApproach U q) (𝓝 0) :=
  (tendsto_comap.mono_left inf_le_left).mono_right nhdsWithin_le_nhds

variable [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- A filter rate yields the literal uniform small-scale estimate, including
strictly positive constants and radius. -/
theorem uniform_bound_of_rate {U : Set D} {q : D → ℝ} {f : D → ℝ}
    {m : ℕ} {r : ℝ} (h : JetRate (scaleApproach U q) q f m r) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ x ∈ U, 0 < q x → q x < δ →
      ‖iteratedFDeriv ℝ m f x‖ ≤ C * q x ^ r := by
  obtain ⟨C, hC, hb⟩ := h
  have hb' : ∀ᶠ v in 𝓝[>] (0 : ℝ), ∀ x, q x = v → x ∈ U →
      ‖iteratedFDeriv ℝ m f x‖ ≤ C * q x ^ r :=
    eventually_comap.mp (eventually_inf_principal.mp hb)
  obtain ⟨δ, hδ, hd⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hb'
  refine ⟨δ, C + 1, hδ, by linarith, ?_⟩
  intro x hx hqx hsmall
  exact (hd ⟨hqx, hsmall⟩ x rfl hx).trans
    (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hqx.le _))

variable {ι : Type*}

/-- Properties derived for one selected schedule, rather than new schedules
chosen after the derivative order or the polynomial has been supplied. -/
structure Properties (U : Set D) (q : D → ℝ) (base : ι → D → ℝ)
    (A : ι → ℕ → D → ℝ) (g L : ℕ → ℝ) (a : ℕ → ℕ) : Prop where
  positive : ∀ j, 0 < a j
  doubling : ∀ j, 2 * a j ≤ a (j + 1)
  strictMono : StrictMono a
  tends : Tendsto (fun j => (a j : ℝ)) atTop atTop
  locallyFinite : ∀ i, LocallyFinite (fun j =>
    Function.support (fun x : U => SolenoidalDiagonal.cutStage (fun j => (a j : ℝ)) q
      (CutStageEstimates.positiveStages (A i)) j x))
  smooth : ∀ i, ContDiffOn ℝ ∞ (realized (fun j => (a j : ℝ)) q (base i) (A i)) U
  approximation : ∀ i, Nonempty (ApproximationRates (scaleApproach U q) q (fun J => g (J + 1) / 2)
    (realized (fun j => (a j : ℝ)) q (base i) (A i)) (stage (base i) (A i)))
  exact_tail : ∀ i x, x ∈ U → ∀ J m, m ≤ J + 3 → q x < 1 / (2 * (a J : ℝ)) →
    ‖iteratedFDeriv ℝ m (fun y => realized (fun j => (a j : ℝ)) q (base i) (A i) y -
      stage (base i) (A i) J y) x‖ ≤
      (1 / 2 : ℝ) ^ J * q x ^ (g (J + 1) / 2 - CutStageEstimates.cutLoss L m)
  outer_zero : ∀ i x, ContinuousAt q x → 1 / (a 0 : ℝ) < q x →
    SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) q
      (CutStageEstimates.positiveStages (A i)) =ᶠ[𝓝 x] (fun _ => 0)

/-- Existence from the raw logarithmic increment and base bounds. Auxiliary
tests have arbitrary per-test logarithmic weights and positive decay powers. -/
theorem exists_realization [Fintype ι] {U : Set D} (hU : IsOpen U) {q : D → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ x ∈ U, 0 < q x ∧ q x ≤ 1)
    (Bq : ℕ → ℝ)
    (hBq : ∀ k x, x ∈ U → q x ≤ 1 →
      ‖iteratedFDeriv ℝ k q x‖ ≤ Bq k * q x ^ (1 - (k : ℝ)))
    {base : ι → D → ℝ} (hbase : ∀ i, ContDiffOn ℝ ∞ (base i) U)
    (Cb Pb Kb : ℕ → ℝ)
    (hbaseBound : ∀ i m x, x ∈ U → ‖iteratedFDeriv ℝ m (base i) x‖ ≤
      Cb m * (1 + |Real.log (q x)|) ^ Pb m * q x ^ (-Kb m))
    {A : ι → ℕ → D → ℝ} (hA : ∀ i j, 1 ≤ j → ContDiffOn ℝ ∞ (A i j) U)
    (g L : ℕ → ℝ) (C P : ι → ℕ → ℕ → ℝ)
    (hraw : ∀ i, CutStageEstimates.RawStageBounds q (A i) g L (C i) (P i) U)
    (hgpos : ∀ j, 1 ≤ j → 0 < g j) (hgmono : Monotone g)
    (lower : ℕ) {κ : Type*} (tests : ℕ → Finset κ) (B Pt γ : ℕ → κ → ℝ)
    (hγ : ∀ j k, k ∈ tests j → 0 < γ j k) {q0 : ℝ} (hq0 : 0 < q0) :
    ∃ a : ℕ → ℕ, lower ≤ a 0 ∧ (∀ j, 1 / (a j : ℝ) < q0) ∧
      Properties U q base A g L a ∧
      ∀ j k, k ∈ tests j → ∀ r : ℝ, 0 < r → r ≤ 1 / (a j : ℝ) →
        |DiagonalScale.logPowerWeight (B j k) (Pt j k) (γ j k) r| ≤ (1 / 2 : ℝ) ^ j := by
  obtain ⟨a, hlo, hap, had, ham, hat, hao, hab, hatest⟩ :=
    GenericDiagonalSchedule.exists_finite_diagonal_cut_bounds_with_tests hU Subset.rfl hq
      (fun x hx => (hpos x hx).1) Bq hBq hA g L C P hraw hgpos lower tests B Pt γ hγ hq0
  have hlU := eventually_domain U q
  have hlq : ∀ᶠ x in scaleApproach U q, 0 < q x ∧ q x ≤ 1 := hlU.mono fun x hx => hpos x hx
  have hzero := scale_tendsto U q
  have haReal : Monotone (fun j => (a j : ℝ)) := fun i j hij => by
    change (a i : ℝ) ≤ (a j : ℝ)
    exact_mod_cast ham.monotone hij
  have hapReal : ∀ j, 0 < (a j : ℝ) := fun j => by exact_mod_cast hap j
  have hgHalf : Monotone (fun j => g j / 2) := fun i j hij => div_le_div_of_nonneg_right (hgmono hij) (by norm_num)
  have hb : ∀ i m, JetRate (scaleApproach U q) q (base i) m (-(Kb m + 1)) := by
    intro i m
    convert jetRate_of_log_bound (hlq.mono fun _ hx => hx.1) hzero m (Cb m) (Pb m) (-Kb m)
      (hlU.mono fun x hx => hbaseBound i m x hx) using 1
    ring
  refine ⟨a, hlo, hao, ?_, hatest⟩
  refine ⟨hap, had, ham, hat, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact SolenoidalDiagonal.locallyFinite_cutStage_support_on hat hq.continuousOn
      (fun x hx => (hpos x hx).1) _
  · intro i
    exact realized_smooth hU hq (fun x hx => (hpos x hx).1) hat (hbase i) (hA i)
  · intro i
    refine ⟨⟨fun m => max (L m + 1) (Kb m + 1), CutStageEstimates.cutLoss L, id, ?_, ?_⟩⟩
    · intro J m
      exact stage_growth hU hlU hlq hzero (hbase i) (hA i) (hraw i)
        (fun j hj => (hgpos j hj).le) (hb i) J m
    · intro m J hJ
      change m ≤ J at hJ
      exact realized_tail_jetRate hat hU hq (hA i) hgHalf (hab i) hlU hlq hzero J m (by omega)
  · intro i x hx J m hm hsmall
    exact realized_tail_bound hat haReal hapReal hU hq (hA i) hgHalf (hab i)
      hx (hpos x hx).1 (hpos x hx).2 J m hm hsmall
  · intro i x hqx houter
    exact correction_eventually_zero haReal hapReal hqx houter _

/-- The full residual assertion, with logarithmic coefficient and finite-stage
bounds and an arbitrary all-orders-flat error majorant. Its conclusion is a
uniform estimate on the whole domain, with the schedule already fixed. -/
theorem Properties.flat_residual {U : Set D} {q : D → ℝ}
    {base : ι → D → ℝ} {A : ι → ℕ → D → ℝ} {g L : ℕ → ℝ} {a : ℕ → ℕ}
    (H : Properties U q base A g L a) (hU : IsOpen U)
    (hq : ∀ x ∈ U, 0 < q x ∧ q x ≤ 1)
    (hbase : ∀ i, ContDiffOn ℝ ∞ (base i) U)
    (hA : ∀ i j, 1 ≤ j → ContDiffOn ℝ ∞ (A i j) U)
    (hgtop : Tendsto g atTop atTop) (P : SupportedPolynomial D ι)
    (hconst : ContDiffOn ℝ ∞ P.constant U)
    (hc : ∀ t ∈ P.terms, ContDiffOn ℝ ∞ t.1 U)
    (region : ((D → ℝ) × Expression D ι Empty) → Set D) (Cc Pc Kc : ℕ → ℝ)
    (hcoeff : ∀ t ∈ P.terms, ∀ m x, x ∈ U → x ∈ region t →
      ‖iteratedFDeriv ℝ m t.1 x‖ ≤
        Cc m * (1 + |Real.log (q x)|) ^ Pc m * q x ^ (-Kc m))
    (hzero : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      t.2.eval (fun k => Empty.elim k)
        (fun i => realized (fun j => (a j : ℝ)) q (base i) (A i)) =ᶠ[𝓝 x] (fun _ => 0))
    (hszero : ∀ t ∈ P.terms, ∀ J x, x ∈ U → x ∉ region t →
      t.2.eval (fun k => Empty.elim k)
        (fun i => stage (base i) (A i) J) =ᶠ[𝓝 x] (fun _ => 0))
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop atTop)
    (Cr Pr : ℕ → ℕ → ℝ) (Kr : ℕ → ℝ) (error : ℕ → ℕ → D → ℝ)
    (hres : ∀ J m x, x ∈ U →
      ‖iteratedFDeriv ℝ m (P.eval (fun i => stage (base i) (A i) J)) x‖ ≤
        Cr J m * (1 + |Real.log (q x)|) ^ Pr J m * q x ^ (rho J - Kr m) + error J m x)
    (he : ∀ J m N, ∃ Ce : ℝ, 0 ≤ Ce ∧ ∀ x ∈ U, error J m x ≤ Ce * q x ^ (N : ℕ))
    (m : ℕ) (N : ℝ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ x ∈ U, 0 < q x → q x < δ →
      ‖iteratedFDeriv ℝ m
        (P.eval (fun i => realized (fun j => (a j : ℝ)) q (base i) (A i))) x‖ ≤ C * q x ^ N := by
  have hlU := eventually_domain U q
  have hlq := hlU.mono (fun x hx => hq x hx)
  have hqzero := scale_tendsto U q
  have hgain : Tendsto (fun J => g (J + 1) / 2) atTop atTop :=
    (hgtop.comp (tendsto_add_atTop_nat 1)).atTop_div_const (by norm_num)
  have hcoeffRate : ∀ t ∈ P.terms, ∀ m,
      JetRate (scaleApproach U q ⊓ 𝓟 (region t)) q t.1 m (-(Kc m + 1)) := by
    intro t ht m
    have hregion : ∀ᶠ x in scaleApproach U q ⊓ 𝓟 (region t), x ∈ region t :=
      Filter.Eventually.filter_mono inf_le_right (by simp)
    have hb : ∀ᶠ x in scaleApproach U q ⊓ 𝓟 (region t),
        ‖iteratedFDeriv ℝ m t.1 x‖ ≤ Cc m * (1 + |Real.log (q x)|) ^ Pc m * q x ^ (-Kc m) := by
      filter_upwards [hlU.filter_mono inf_le_left, hregion] with x hx hr
      exact hcoeff t ht m x hx hr
    convert jetRate_of_log_bound ((hlq.filter_mono inf_le_left).mono fun _ hx => hx.1)
      (hqzero.mono_left inf_le_left) m (Cc m) (Pc m) (-Kc m) hb using 1
    ring
  have hresRate : ∀ J k, JetRate (scaleApproach U q) q
      (P.eval (fun i => stage (base i) (A i) J)) k (rho J - (Kr k + 1)) := by
    intro J k
    have herr : ∀ M : ℕ, ∃ Ce : ℝ, 0 ≤ Ce ∧
        ∀ᶠ x in scaleApproach U q, error J k x ≤ Ce * q x ^ M := by
      intro M
      obtain ⟨Ce, hCe, hb⟩ := he J k M
      exact ⟨Ce, hCe, hlU.mono fun x hx => hb x hx⟩
    convert jetRate_of_log_bound_add_flat hlq hqzero k (Cr J k) (Pr J k)
      (rho J - Kr k) (hlU.mono fun x hx => hres J k x hx) herr using 1
    ring
  apply uniform_bound_of_rate
  exact P.flat_of_local_coefficients hU hlU hlq H.smooth
    (fun J i => stage_smooth (hbase i) (hA i) J) hgain hrho
    (fun i => (H.approximation i).some) hconst hc region (fun _ m => Kc m + 1)
    hcoeffRate hzero hszero (fun k => Kr k + 1) hresRate m N

end NavierStokes.GenericRealization

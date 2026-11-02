import NavierStokes.GenericSummationRealization
import NavierStokes.GenericSupportedPolynomial

/-! # Actual summation residuals with support-local coefficient regularity

Every statement retains the given cutoff schedule, literal polynomial and
coefficient functions. Smoothness and growth of a nonconstant coefficient
are only needed on its common differentiated-factor support region.
-/
/-! Merged from `NavierStokes.GenericSupportLocalCoefficients` (in a section, so its `open`s cannot leak). -/
section
/-! # Differential polynomials with coefficients smooth only on factor supports

The literal coefficient is retained. At points outside the common factor
region the monomial has a zero germ, making its product smooth with every
jet zero even when the coefficient itself is singular or nonsmooth there.
-/

noncomputable section

namespace NavierStokes.GenericDifferentialPolynomial

open Set Filter DiagonalResidual
open scoped Topology ContDiff BigOperators

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {l : Filter D} {q : D → ℝ} {U S : Set D}

theorem norm_jet_mul_at {f g : D → ℝ} {x : D}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ)
    {A B : ℝ} (hA : ∀ k ≤ m, ‖iteratedFDeriv ℝ k f x‖ ≤ A)
    (hB : ∀ k ≤ m, ‖iteratedFDeriv ℝ k g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (fun y => f y * g y) x‖ ≤ 2 ^ m * A * B := by
  obtain ⟨V, hV, hxV, hfV⟩ := hf.contDiffOn' (m := (m : WithTop ℕ∞)) (by simp) (by simp)
  obtain ⟨W, hW, hxW, hgW⟩ := hg.contDiffOn' (m := (m : WithTop ℕ∞)) (by simp) (by simp)
  simp only [Set.insert_eq_of_mem (Set.mem_univ x), univ_inter] at hfV hgW
  have hfs : ContDiffOn ℝ m f (V ∩ W) := hfV.mono inter_subset_left
  have hgs : ContDiffOn ℝ m g (V ∩ W) := hgW.mono inter_subset_right
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _))
  apply (JetBounds.norm_iteratedFDeriv_mul_le_on (hV.inter hW) hfs hgs
    ⟨hxV, hxW⟩ (le_refl (m : WithTop ℕ∞))).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hA i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
          (Nat.cast_nonneg _))
        (hB (m - i) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA0)
    _ = 2 ^ m * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose m

/-- The product estimate only needs smoothness at the points in the filter. -/
theorem rate_mul_at {f g : D → ℝ}
    (hq : ∀ᶠ x in l, 0 < q x)
    (hf : ∀ᶠ x in l, ContDiffAt ℝ ∞ f x)
    (hg : ∀ᶠ x in l, ContDiffAt ℝ ∞ g x)
    {m : ℕ} {r s : ℝ} (hr : FiniteJetRate l q f m r)
    (hs : FiniteJetRate l q g m s) :
    JetRate l q (fun x => f x * g x) m (r + s) := by
  obtain ⟨A, hA, hbA⟩ := hr
  obtain ⟨B, hB, hbB⟩ := hs
  refine ⟨2 ^ m * A * B, by positivity, ?_⟩
  filter_upwards [hq, hf, hg, hbA, hbB] with x hqx hfx hgx hAx hBx
  calc
    _ ≤ 2 ^ m * (A * q x ^ r) * (B * q x ^ s) := norm_jet_mul_at hfx hgx m hAx hBx
    _ = (2 ^ m * A * B) * q x ^ (r + s) := by rw [Real.rpow_add hqx]; ring

omit [NormedSpace ℝ D] in
theorem mul_zero_germ {c f : D → ℝ} {x : D}
    (hzero : f =ᶠ[𝓝 x] (fun _ => 0)) :
    (fun y => c y * f y) =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [hzero] with y hy
  simp only [hy, mul_zero]


theorem smooth_mul_of_support_local {c f : D → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hc : ∀ x ∈ U, x ∈ S → ContDiffAt ℝ ∞ c x)
    (hzero : ∀ x ∈ U, x ∉ S → f =ᶠ[𝓝 x] (fun _ => 0)) :
    ContDiffOn ℝ ∞ (fun x => c x * f x) U := by
  intro x hx
  by_cases hs : x ∈ S
  · exact ((hc x hx hs).mul (hf.contDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  · exact (contDiffAt_const.congr_of_eventuallyEq
      (mul_zero_germ (c := c) (hzero x hx hs))).contDiffWithinAt


def ApproximationRates.mul_coefficient_support_local
    {gain : ℕ → ℝ} {f c : D → ℝ} {fs : ℕ → D → ℝ}
    (a : ApproximationRates l q gain f fs)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U) (hfs : ∀ J, ContDiffOn ℝ ∞ (fs J) U)
    (hc : ∀ x ∈ U, x ∈ S → ContDiffAt ℝ ∞ c x) (Lc : ℕ → ℝ)
    (hcg : ∀ m, JetRate (l ⊓ 𝓟 S) q c m (-Lc m))
    (hzero : ∀ x ∈ U, x ∉ S → f =ᶠ[𝓝 x] (fun _ => 0))
    (hszero : ∀ J x, x ∈ U → x ∉ S → fs J =ᶠ[𝓝 x] (fun _ => 0)) :
    TailRates l q gain (fun x => c x * f x) (fun J x => c x * fs J x) := by
  let M : ℕ → ℕ := fun m => (Finset.range (m + 1)).sup a.threshold
  refine ⟨fun m => maxJetLoss Lc m + maxJetLoss a.tailLoss m, M, ?_⟩
  intro m J hJ
  have hqr : ∀ᶠ x in l ⊓ 𝓟 S, 0 < q x ∧ q x ≤ 1 := hq.filter_mono inf_le_left
  have hlr : ∀ᶠ x in l ⊓ 𝓟 S, x ∈ U := hlU.filter_mono inf_le_left
  have hregion : ∀ᶠ x in l ⊓ 𝓟 S, x ∈ S :=
    Filter.Eventually.filter_mono inf_le_right (by simp)
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
  have hca : ∀ᶠ x in l ⊓ 𝓟 S, ContDiffAt ℝ ∞ c x := by
    filter_upwards [hlr, hregion] with x hx hs
    exact hc x hx hs
  have hr := rate_mul_at (hqr.mono fun _ hx => hx.1) hca
    (hlr.mono fun x hx => (hf.sub (hfs J)).contDiffAt (hU.mem_nhds hx)) hcr htr
  have hr' : JetRate (l ⊓ 𝓟 S) q (fun x => c x * f x - c x * fs J x) m
      (gain J - (maxJetLoss Lc m + maxJetLoss a.tailLoss m)) := by
    convert hr.congr_on hU hlr
      (show EqOn (fun x => c x * (f x - fs J x))
        (fun x => c x * f x - c x * fs J x) U from fun x _ => mul_sub _ _ _) using 1
    ring
  apply rate_of_restricted_support (hq.mono fun _ hx => hx.1) hlU hr'
  intro x hxU hx
  filter_upwards [hzero x hxU hx, hszero J x hxU hx] with y hy hsy
  simp only [hy, hsy, mul_zero, sub_self]

namespace SupportedPolynomial

variable {ι : Type*}

theorem smooth_evalTerms_of_products (terms : List ((D → ℝ) × Expression D ι Empty))
    {u : ι → D → ℝ}
    (ht : ∀ t ∈ terms, ContDiffOn ℝ ∞
      (fun x => t.1 x * t.2.eval (fun k => Empty.elim k) u x) U) :
    ContDiffOn ℝ ∞ (evalTerms u terms) U := by
  induction terms with
  | nil => exact contDiffOn_const
  | cons t ts ih =>
      exact (ht t (by simp)).add (ih (fun v hv => ht v (by simp [hv])))

def termsTail_of_products {gain : ℕ → ℝ} {u : ι → D → ℝ} {us : ℕ → ι → D → ℝ}
    (terms : List ((D → ℝ) × Expression D ι Empty))
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hu : ∀ t ∈ terms, ContDiffOn ℝ ∞
      (fun x => t.1 x * t.2.eval (fun k => Empty.elim k) u x) U)
    (hus : ∀ t ∈ terms, ∀ J, ContDiffOn ℝ ∞
      (fun x => t.1 x * t.2.eval (fun k => Empty.elim k) (us J) x) U)
    (ht : ∀ t ∈ terms,
      TailRates l q gain (fun x => t.1 x * t.2.eval (fun k => Empty.elim k) u x)
        (fun J x => t.1 x * t.2.eval (fun k => Empty.elim k) (us J) x)) :
    TailRates l q gain (evalTerms u terms) (fun J => evalTerms (us J) terms) := by
  induction terms with
  | nil => exact TailRates.fixed (fun _ => 0)
  | cons t ts ih =>
      exact (ht t (by simp)).add
        (ih (fun v hv => hu v (by simp [hv])) (fun v hv => hus v (by simp [hv]))
          (fun v hv => ht v (by simp [hv]))) hU hlU hq
        (hu t (by simp)) (smooth_evalTerms_of_products ts (fun v hv => hu v (by simp [hv])))
        (hus t (by simp))
        (fun J => smooth_evalTerms_of_products ts (fun v hv => hus v (by simp [hv]) J))

/-- Full residual transfer with smoothness, as well as all coefficient
growth bounds, required only at points of each common factor region. The
conclusion evaluates the original polynomial with its original coefficients. -/
theorem flat_of_support_local_coefficients (P : SupportedPolynomial D ι)
    {gain rho : ℕ → ℝ} {u : ι → D → ℝ} {us : ℕ → ι → D → ℝ}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hus : ∀ J i, ContDiffOn ℝ ∞ (us J i) U)
    (hgain : Tendsto gain atTop atTop) (hrho : Tendsto rho atTop atTop)
    (ha : ∀ i, ApproximationRates l q gain (u i) (fun J => us J i))
    (hconst : ContDiffOn ℝ ∞ P.constant U)
    (region : ((D → ℝ) × Expression D ι Empty) → Set D)
    (hc : ∀ t ∈ P.terms, ∀ x ∈ U, x ∈ region t → ContDiffAt ℝ ∞ t.1 x)
    (Lc : ((D → ℝ) × Expression D ι Empty) → ℕ → ℝ)
    (hcg : ∀ t ∈ P.terms, ∀ m, JetRate (l ⊓ 𝓟 (region t)) q t.1 m (-Lc t m))
    (hzero : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      t.2.eval (fun k => Empty.elim k) u =ᶠ[𝓝 x] (fun _ => 0))
    (hszero : ∀ t ∈ P.terms, ∀ J x, x ∈ U → x ∉ region t →
      t.2.eval (fun k => Empty.elim k) (us J) =ᶠ[𝓝 x] (fun _ => 0))
    (Lres : ℕ → ℝ)
    (hres : ∀ J m, JetRate l q (P.eval (us J)) m (rho J - Lres m))
    (m : ℕ) (n : ℝ) : JetRate l q (P.eval u) m n := by
  have hprod : ∀ t ∈ P.terms, ContDiffOn ℝ ∞
      (fun x => t.1 x * t.2.eval (fun k => Empty.elim k) u x) U := by
    intro t ht
    exact smooth_mul_of_support_local hU (t.2.smooth_eval hU (fun k => Empty.elim k) hu)
      (hc t ht) (hzero t ht)
  have hsprod : ∀ t ∈ P.terms, ∀ J, ContDiffOn ℝ ∞
      (fun x => t.1 x * t.2.eval (fun k => Empty.elim k) (us J) x) U := by
    intro t ht J
    exact smooth_mul_of_support_local hU (t.2.smooth_eval hU (fun k => Empty.elim k) (hus J))
      (hc t ht) (hszero t ht J)
  let ht := termsTail_of_products P.terms hU hlU hq hprod hsprod (fun t ht =>
    (t.2.approximation_eval hU hlU hq (fun k => Empty.elim k) hu hus hgain
      (fun k => Empty.elim k) (fun k => Empty.elim k) ha).mul_coefficient_support_local
        hU hlU hq (t.2.smooth_eval hU (fun k => Empty.elim k) hu)
        (fun J => t.2.smooth_eval hU (fun k => Empty.elim k) (hus J))
        (hc t ht) (Lc t) (hcg t ht) (hzero t ht) (hszero t ht))
  have hs := smooth_evalTerms_of_products P.terms hprod
  have hss := fun J => smooth_evalTerms_of_products P.terms (fun t ht => hsprod t ht J)
  let hp := (TailRates.fixed P.constant).add ht hU hlU hq hconst hs (fun _ => hconst) hss
  exact hp.flat_of_residuals hU hlU hq (hconst.add hs)
    (fun J => hconst.add (hss J)) hgain hrho Lres hres m n

end SupportedPolynomial

end NavierStokes.GenericDifferentialPolynomial
end


noncomputable section

namespace NavierStokes.GenericTupleRealization

open Set Filter ProblemStatement GenericDifferentialPolynomial DiagonalResidual
open GenericRealizationBounds GenericRealization GenericSolenoidalRealization
open scoped Topology ContDiff BigOperators

/-! ## Residual transfer from actual field approximation -/

theorem Result.flat_residual_support_local {κ : Type*} {U : Set SpaceTime} {q : SpaceTime → ℝ}
    {u0 : VelocityField} {s0 : κ → PressureField} {A B : ℕ → VelocityField}
    {R : κ → ℕ → PressureField} {g L : ℕ → ℝ} {a : ℕ → ℕ}
    (H : Result U q u0 s0 A B R g L a) (hU : IsOpen U)
    (hq : ∀ w ∈ U, 0 < q w ∧ q w ≤ 1)
    (hu0 : ContDiffOn ℝ ∞ u0 U) (hs0 : ∀ k, ContDiffOn ℝ ∞ (s0 k) U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (hR : ∀ k j, 1 ≤ j → ContDiffOn ℝ ∞ (R k j) U)
    (hgtop : Tendsto g atTop atTop) (P : SupportedPolynomial SpaceTime (Fin 3 ⊕ κ))
    (hconst : ContDiffOn ℝ ∞ P.constant U)
    (region : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → Set SpaceTime)
    (hc : ∀ t ∈ P.terms, ∀ x ∈ U, x ∈ region t → ContDiffAt ℝ ∞ t.1 x)
    (Lc : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → ℕ → ℝ)
    (hcg : ∀ t ∈ P.terms, ∀ m, JetRate (scaleApproach U q ⊓ 𝓟 (region t)) q t.1 m (-Lc t m))
    (hzero : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      t.2.eval (fun k => Empty.elim k) (components (fun j => (a j : ℝ)) q u0 s0 A B R)
        =ᶠ[𝓝 x] (fun _ => 0))
    (hszero : ∀ t ∈ P.terms, ∀ J x, x ∈ U → x ∉ region t →
      t.2.eval (fun k => Empty.elim k) (stageComponents u0 s0 A B R J)
        =ᶠ[𝓝 x] (fun _ => 0))
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop atTop) (Lres : ℕ → ℝ)
    (hres : ∀ J m, JetRate (scaleApproach U q) q
      (P.eval (stageComponents u0 s0 A B R J)) m (rho J - Lres m)) (m : ℕ) (N : ℝ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ x ∈ U, 0 < q x → q x < δ →
      ‖iteratedFDeriv ℝ m (P.eval (components (fun j => (a j : ℝ)) q u0 s0 A B R)) x‖ ≤ C * q x ^ N := by
  have hlU := eventually_domain U q
  have hlq := hlU.mono fun w hw => hq w hw
  have hu : ∀ i, ContDiffOn ℝ ∞ (components (fun j => (a j : ℝ)) q u0 s0 A B R i) U := by
    intro i
    cases i with
    | inl i => exact (EuclideanSpace.proj i).contDiff.comp_contDiffOn H.smooth_velocity
    | inr k => exact H.smooth_scalars k
  have hus : ∀ J i, ContDiffOn ℝ ∞ (stageComponents u0 s0 A B R J i) U := by
    intro J i
    cases i with
    | inl i => exact (EuclideanSpace.proj i).contDiff.comp_contDiffOn (positiveStage_smooth hU hu0 hA hB J)
    | inr k => exact stage_smooth (hs0 k) (hR k) J
  have hgain : Tendsto (fun J => g (J + 1) / 2) atTop atTop :=
    (hgtop.comp (tendsto_add_atTop_nat 1)).atTop_div_const (by norm_num)
  exact uniform_bound_of_rate (P.flat_of_support_local_coefficients hU hlU hlq hu hus hgain hrho
    (fun i => (H.approximation i).some) hconst region hc Lc hcg hzero hszero Lres hres m N)


/-- Raw and cut differentiated-factor supports imply the required zero germs
for the actual finite stages and locally finite realized sum. -/
theorem Result.flat_residual_of_support_local_factors {κ : Type*} {U : Set SpaceTime} {q : SpaceTime → ℝ}
    {u0 : VelocityField} {s0 : κ → PressureField} {A B : ℕ → VelocityField}
    {R : κ → ℕ → PressureField} {g L : ℕ → ℝ} {a : ℕ → ℕ}
    (H : Result U q u0 s0 A B R g L a) (hU : IsOpen U)
    (hqs : ContDiffOn ℝ ∞ q U) (hq : ∀ w ∈ U, 0 < q w ∧ q w ≤ 1)
    (hu0 : ContDiffOn ℝ ∞ u0 U) (hs0 : ∀ k, ContDiffOn ℝ ∞ (s0 k) U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (hR : ∀ k j, 1 ≤ j → ContDiffOn ℝ ∞ (R k j) U)
    (hgtop : Tendsto g atTop atTop) (P : SupportedPolynomial SpaceTime (Fin 3 ⊕ κ))
    (hconst : ContDiffOn ℝ ∞ P.constant U)
    (region : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → Set SpaceTime)
    (hc : ∀ t ∈ P.terms, ∀ x ∈ U, x ∈ region t → ContDiffAt ℝ ∞ t.1 x)
    (Lc : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → ℕ → ℝ)
    (hcg : ∀ t ∈ P.terms, ∀ m, DiagonalResidual.JetRate (scaleApproach U q ⊓ 𝓟 (region t)) q t.1 m (-Lc t m))
    (hrawsupport : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      FactorSupportAt (baseComponents u0 s0) (incrementComponents A B R) x t.2)
    (hcutsupport : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      FactorSupportAt (baseComponents u0 s0) (cutIncrementComponents (fun j => (a j : ℝ)) q A B R) x t.2)
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop atTop) (Lres : ℕ → ℝ)
    (hres : ∀ J m, DiagonalResidual.JetRate (scaleApproach U q) q
      (P.eval (stageComponents u0 s0 A B R J)) m (rho J - Lres m)) (m : ℕ) (N : ℝ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ x ∈ U, 0 < q x → q x < δ →
      ‖iteratedFDeriv ℝ m (P.eval (components (fun j => (a j : ℝ)) q u0 s0 A B R)) x‖ ≤ C * q x ^ N := by
  apply H.flat_residual_support_local hU hq hu0 hs0 hA hB hR hgtop P hconst region hc Lc hcg
    _ _ rho hrho Lres hres m N
  · intro t ht x hx hxs
    exact (hcutsupport t ht x hx hxs).zero_germ hU hx (smooth_baseComponents hu0 hs0)
      (smooth_cutIncrementComponents hU hqs hA hB hR)
      (components_local_sum hU H.tends hqs (fun w hw => (hq w hw).1) hA hx)
  · intro t ht J x hx hxs
    exact (hrawsupport t ht x hx hxs).zero_germ hU hx (smooth_baseComponents hu0 hs0)
      (smooth_incrementComponents hU hA hB hR) (stageComponents_local_sum hU hA J hx)


/-- The printed logarithmic hypotheses with coefficients smooth only on the
common supports, independent correction and residual gains, and an arbitrary
all-orders-flat finite-stage error, imply flatness of the actual residual. -/
theorem Result.flat_residual_of_support_local_raw_bounds {κ : Type*} {U : Set SpaceTime} {q : SpaceTime → ℝ}
    {u0 : VelocityField} {s0 : κ → PressureField} {A B : ℕ → VelocityField}
    {R : κ → ℕ → PressureField} {g L : ℕ → ℝ} {a : ℕ → ℕ}
    (H : Result U q u0 s0 A B R g L a) (hU : IsOpen U)
    (hqs : ContDiffOn ℝ ∞ q U) (hq : ∀ w ∈ U, 0 < q w ∧ q w ≤ 1)
    (hu0 : ContDiffOn ℝ ∞ u0 U) (hs0 : ∀ k, ContDiffOn ℝ ∞ (s0 k) U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (hR : ∀ k j, 1 ≤ j → ContDiffOn ℝ ∞ (R k j) U)
    (hgtop : Tendsto g atTop atTop) (P : SupportedPolynomial SpaceTime (Fin 3 ⊕ κ))
    (hconst : ContDiffOn ℝ ∞ P.constant U)
    (region : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → Set SpaceTime)
    (hc : ∀ t ∈ P.terms, ∀ x ∈ U, x ∈ region t → ContDiffAt ℝ ∞ t.1 x)
    (Cc Pc Kc : ℕ → ℝ)
    (hcoeff : ∀ t ∈ P.terms, ∀ m x, x ∈ U → x ∈ region t →
      ‖iteratedFDeriv ℝ m t.1 x‖ ≤ Cc m * (1 + |Real.log (q x)|) ^ Pc m * q x ^ (-Kc m))
    (hrawsupport : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      FactorSupportAt (baseComponents u0 s0) (incrementComponents A B R) x t.2)
    (hcutsupport : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      FactorSupportAt (baseComponents u0 s0) (cutIncrementComponents (fun j => (a j : ℝ)) q A B R) x t.2)
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop atTop) (Cr Pr : ℕ → ℕ → ℝ) (Kr : ℕ → ℝ)
    (error : ℕ → ℕ → SpaceTime → ℝ)
    (hres : ∀ J m x, x ∈ U →
      ‖iteratedFDeriv ℝ m (P.eval (stageComponents u0 s0 A B R J)) x‖ ≤
        Cr J m * (1 + |Real.log (q x)|) ^ Pr J m * q x ^ (rho J - Kr m) + error J m x)
    (he : ∀ J m N, ∃ Ce : ℝ, 0 ≤ Ce ∧ ∀ x ∈ U, error J m x ≤ Ce * q x ^ (N : ℕ))
    (m : ℕ) (N : ℝ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ x ∈ U, 0 < q x → q x < δ →
      ‖iteratedFDeriv ℝ m (P.eval (components (fun j => (a j : ℝ)) q u0 s0 A B R)) x‖ ≤ C * q x ^ N := by
  have hlU := eventually_domain U q
  have hlq := hlU.mono fun w hw => hq w hw
  have hqzero := scale_tendsto U q
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
      (P.eval (stageComponents u0 s0 A B R J)) k (rho J - (Kr k + 1)) := by
    intro J k
    have herr : ∀ M : ℕ, ∃ Ce : ℝ, 0 ≤ Ce ∧
        ∀ᶠ x in scaleApproach U q, error J k x ≤ Ce * q x ^ M := by
      intro M
      obtain ⟨Ce, hCe, hb⟩ := he J k M
      exact ⟨Ce, hCe, hlU.mono fun x hx => hb x hx⟩
    convert jetRate_of_log_bound_add_flat hlq hqzero k (Cr J k) (Pr J k)
      (rho J - Kr k) (hlU.mono fun x hx => hres J k x hx) herr using 1
    ring
  exact H.flat_residual_of_support_local_factors hU hqs hq hu0 hs0 hA hB hR hgtop P hconst region hc
    (fun _ m => Kc m + 1) hcoeffRate hrawsupport hcutsupport rho hrho
    (fun m => Kr m + 1) hresRate m N


end NavierStokes.GenericTupleRealization

import NavierStokes.TangentProjection
import NavierStokes.PhaseCalculus
import NavierStokes.TangentODE
import NavierStokes.GaussianEnvelope
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FinCases
import NavierStokes.ViscousPropagator
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Positivity

/-!
# The actual moving tangent frame

The ambient coordinates are radial, angular, axial.  The two tangent coordinates
are taken in `e_r - ρ K, N`, where `K,N` is an orthonormal frame of the last two
coordinates.  Normal motion, rotation, viscosity and projected forcing are all
retained in the exact equation.
-/
/-! Merged from `NavierStokes.GrowingMode` (in a section, so its `open`s cannot leak). -/
section
/-!
# The actual growing mode stays in a narrow cone

The invariant region is proved using a quadratic boundary function, without
dividing by the growing coordinate or assuming its positivity along the solution.
-/

namespace NavierStokes.GrowingMode

open Set Filter
open scoped Topology

abbrev State := EuclideanSpace ℝ (Fin 2)

/-- The actual two-mode coefficient, including four independent error entries. -/
noncomputable def modalOperator (lam damping e11 e12 e21 e22 : ℝ) : State →L[ℝ] State :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => !₂[(lam - damping + e11) * z 0 + e12 * z 1,
      e21 * z 0 + (-lam - damping + e22) * z 1]
    map_add' := by
      intro x y
      ext i
      fin_cases i <;> simp <;> ring
    map_smul' := by
      intro c x
      ext i
      fin_cases i <;> simp <;> ring }

@[simp] theorem modalOperator_zero (lam damping e11 e12 e21 e22 : ℝ) (z : State) :
    modalOperator lam damping e11 e12 e21 e22 z 0 =
      (lam - damping + e11) * z 0 + e12 * z 1 := rfl

@[simp] theorem modalOperator_one (lam damping e11 e12 e21 e22 : ℝ) (z : State) :
    modalOperator lam damping e11 e12 e21 e22 z 1 =
      e21 * z 0 + (-lam - damping + e22) * z 1 := rfl

/-- A nonzero solution of a continuous homogeneous linear equation cannot hit zero.
This uses backwards uniqueness, not a positivity assumption on any coordinate. -/
theorem linear_solution_ne_zero
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {a b : ℝ} (hab : a ≤ b) (A : ℝ → H →L[ℝ] H)
    (hA : ContinuousOn A (Icc a b)) {z : ℝ → H}
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (A t (z t)) t) (hinit : z a ≠ 0) :
    ∀ t ∈ Icc a b, z t ≠ 0 := by
  obtain ⟨L, hL⟩ := TangentODE.linear_uniform_lipschitz hab A (fun _ => (0 : H)) hA
  intro t ht hzt
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have huniq : EqOn z (fun _ => (0 : H)) (Icc a t) := by
    apply ODE_solution_unique_of_mem_Icc_left
      (v := fun s x => A s x) (s := fun _ => Set.univ) (K := L)
    · intro s hs
      simpa only [add_zero] using (hL s (hsub (Ioc_subset_Icc_self hs))).lipschitzOnWith
    · exact fun s hs => (hz s (hsub hs)).continuousAt.continuousWithinAt
    · exact fun s hs => (hz s (hsub (Ioc_subset_Icc_self hs))).hasDerivWithinAt
    · exact fun _ _ => Set.mem_univ _
    · exact continuousOn_const
    · intro s _
      simpa only [map_zero] using (hasDerivAt_const s (0 : H)).hasDerivWithinAt
    · exact fun _ _ => Set.mem_univ _
    · exact hzt
  exact hinit (huniq ⟨le_rfl, ht.1⟩)

/-- The inward algebra at the upper edge of the cone. -/
theorem upper_edge_factor_negative
    {lam lamMin eps r e11 e12 e21 e22 : ℝ}
    (hr : 0 < r) (hlam : lamMin ≤ lam)
    (he11 : |e11| ≤ eps) (he12 : |e12| ≤ eps)
    (he21 : |e21| ≤ eps) (he22 : |e22| ≤ eps)
    (hgap : eps * (1 + r) ^ 2 < 2 * lamMin * r) :
    e21 + r * (e22 - e11) - r ^ 2 * e12 - 2 * lam * r < 0 := by
  have hlin : r * (e22 - e11) ≤ r * (2 * eps) :=
    mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp he11).1, (abs_le.mp he22).2]) hr.le
  have hquad : -(r ^ 2 * e12) ≤ r ^ 2 * eps := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp he12).1 (sq_nonneg r)
    nlinarith
  have hrate : lamMin * r ≤ lam * r := mul_le_mul_of_nonneg_right hlam hr.le
  nlinarith [(abs_le.mp he21).2]

/-- The inward algebra at the lower edge follows by reversing the off-diagonal signs. -/
theorem lower_edge_factor_negative
    {lam lamMin eps r e11 e12 e21 e22 : ℝ}
    (hr : 0 < r) (hlam : lamMin ≤ lam)
    (he11 : |e11| ≤ eps) (he12 : |e12| ≤ eps)
    (he21 : |e21| ≤ eps) (he22 : |e22| ≤ eps)
    (hgap : eps * (1 + r) ^ 2 < 2 * lamMin * r) :
    -e21 + r * (e22 - e11) + r ^ 2 * e12 - 2 * lam * r < 0 := by
  have h := upper_edge_factor_negative (e12 := -e12) (e21 := -e21)
    hr hlam he11 (by simpa only [abs_neg] using he12)
    (by simpa only [abs_neg] using he21) he22 hgap
  nlinarith

/-- The quadratic cone boundary has strictly negative derivative at every
nonzero boundary point. Scalar damping cancels from this computation. -/
theorem cone_boundary_derivative_negative
    {p q lam damping lamMin eps r e11 e12 e21 e22 : ℝ}
    (hr : 0 < r) (hp : p ≠ 0) (hboundary : q ^ 2 = r ^ 2 * p ^ 2)
    (hlam : lamMin ≤ lam)
    (he11 : |e11| ≤ eps) (he12 : |e12| ≤ eps)
    (he21 : |e21| ≤ eps) (he22 : |e22| ≤ eps)
    (hgap : eps * (1 + r) ^ 2 < 2 * lamMin * r) :
    2 * q * (e21 * p + (-lam - damping + e22) * q) -
      r ^ 2 * (2 * p * ((lam - damping + e11) * p + e12 * q)) < 0 := by
  have hsq : q ^ 2 = (r * p) ^ 2 := by nlinarith [hboundary]
  have hpos : 0 < 2 * r * p ^ 2 := mul_pos (by linarith) (sq_pos_of_ne_zero hp)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hq | hq
  · rw [hq]
    have h := mul_neg_of_pos_of_neg hpos
      (upper_edge_factor_negative hr hlam he11 he12 he21 he22 hgap)
    nlinarith [h]
  · rw [hq]
    have h := mul_neg_of_pos_of_neg hpos
      (lower_edge_factor_negative hr hlam he11 he12 he21 he22 hgap)
    nlinarith [h]

theorem hasDerivAt_coordinate {z : ℝ → State} {z' : State} {t : ℝ}
    (hz : HasDerivAt z z' t) (i : Fin 2) :
    HasDerivAt (fun s => z s i) (z' i) t := by
  exact (PiLp.proj 2 (fun _ : Fin 2 => ℝ) i).hasFDerivAt.comp_hasDerivAt t hz

/-- The actual homogeneous solution stays in the growing cone, and the growing
coordinate is strictly positive. Positivity and nonvanishing are conclusions. -/
theorem positive_invariant_cone
    {a b r eps lamMin : ℝ} (hab : a ≤ b) (hr : 0 < r)
    (hgap : eps * (1 + r) ^ 2 < 2 * lamMin * r)
    (lam damping e11 e12 e21 e22 : ℝ → ℝ) {z : ℝ → State}
    (hA : ContinuousOn (fun t =>
      modalOperator (lam t) (damping t) (e11 t) (e12 t) (e21 t) (e22 t)) (Icc a b))
    (hode : ∀ t ∈ Icc a b, HasDerivAt z
      (modalOperator (lam t) (damping t) (e11 t) (e12 t) (e21 t) (e22 t) (z t)) t)
    (hlam : ∀ t ∈ Icc a b, lamMin ≤ lam t)
    (herr : ∀ t ∈ Icc a b,
      |e11 t| ≤ eps ∧ |e12 t| ≤ eps ∧ |e21 t| ≤ eps ∧ |e22 t| ≤ eps)
    (hplus : 0 < z a 0) (hminus : z a 1 = 0) :
    ∀ t ∈ Icc a b, 0 < z t 0 ∧ |z t 1| ≤ r * z t 0 := by
  have hinit : z a ≠ 0 := by
    intro h
    have : z a 0 = 0 := by simp only [h, PiLp.zero_apply]
    linarith
  have hnonzero := linear_solution_ne_zero hab _ hA hode hinit
  have hp (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (fun s => z s 0)
      ((lam t - damping t + e11 t) * z t 0 + e12 t * z t 1) t :=
    hasDerivAt_coordinate (hode t ht) 0
  have hq (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (fun s => z s 1)
      (e21 t * z t 0 + (-lam t - damping t + e22 t) * z t 1) t :=
    hasDerivAt_coordinate (hode t ht) 1
  let barrier : ℝ → ℝ := fun t => (z t 1) ^ 2 - r ^ 2 * (z t 0) ^ 2
  let barrier' : ℝ → ℝ := fun t =>
    2 * z t 1 * (e21 t * z t 0 + (-lam t - damping t + e22 t) * z t 1) -
      r ^ 2 * (2 * z t 0 * ((lam t - damping t + e11 t) * z t 0 + e12 t * z t 1))
  have hd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt barrier (barrier' t) t := by
    convert! ((hq t ht).pow 2).sub (((hp t ht).pow 2).const_mul (r ^ 2)) using 1
    simp [barrier']
  have hbarrier : ∀ t ∈ Icc a b, barrier t ≤ 0 := by
    apply image_le_of_deriv_right_lt_deriv_boundary'
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (B := fun _ => (0 : ℝ)) (B' := fun _ => (0 : ℝ))
    · dsimp [barrier]
      rw [hminus]
      nlinarith [mul_nonneg (sq_nonneg r) (sq_nonneg (z a 0))]
    · exact continuousOn_const
    · exact fun t _ => (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt
    · intro t ht heq
      have htc := Ico_subset_Icc_self ht
      have hsq : (z t 1) ^ 2 = r ^ 2 * (z t 0) ^ 2 := by
        dsimp [barrier] at heq
        linarith
      have hpn : z t 0 ≠ 0 := by
        intro hpzero
        have hqzero : z t 1 = 0 := by
          apply sq_eq_zero_iff.mp
          simpa only [hpzero, zero_pow (by decide : 2 ≠ 0), mul_zero] using hsq
        apply hnonzero t htc
        ext i
        fin_cases i <;> simp [hpzero, hqzero]
      rcases herr t htc with ⟨h11, h12, h21, h22⟩
      exact cone_boundary_derivative_negative hr hpn hsq (hlam t htc)
        h11 h12 h21 h22 hgap
  have hpne : ∀ t ∈ Icc a b, z t 0 ≠ 0 := by
    intro t ht hpzero
    have hqsq : (z t 1) ^ 2 ≤ 0 := by simpa [barrier, hpzero] using hbarrier t ht
    have hqzero : z t 1 = 0 := sq_eq_zero_iff.mp (le_antisymm hqsq (sq_nonneg _))
    apply hnonzero t ht
    ext i
    fin_cases i <;> simp [hpzero, hqzero]
  have hpcont : ContinuousOn (fun t => z t 0) (Icc a b) :=
    fun t ht => (hp t ht).continuousAt.continuousWithinAt
  intro t ht
  have hppos : 0 < z t 0 := by
    by_contra! hnpos
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
    obtain ⟨s, hs, hszero⟩ :=
      intermediate_value_Icc' ht.1 (hpcont.mono hsub) ⟨hnpos, hplus.le⟩
    exact hpne s (hsub hs) hszero
  refine ⟨hppos, abs_le_of_sq_le_sq ?_ (mul_nonneg hr.le hppos.le)⟩
  have hb := hbarrier t ht
  dsimp [barrier] at hb
  nlinarith

/-- A fixed constant for the manuscript's `O(1/S)` cone width. The added one
allows the same statement when the perturbation bound is zero. -/
noncomputable def coneConstant (lamMin C : ℝ) : ℝ := 4 * (C + 1) / lamMin

/-- An explicit sufficient meaning of "sufficiently large S". -/
theorem scaled_cone_conditions {lamMin C S : ℝ}
    (hlamMin : 0 < lamMin) (hC : 0 ≤ C) (hS : 0 < S)
    (hlarge : 2 * coneConstant lamMin C ≤ S) :
    0 < coneConstant lamMin C / S ∧
      coneConstant lamMin C / S ≤ 1 / 2 ∧
      (C / S) * (1 + coneConstant lamMin C / S) ^ 2 <
        2 * lamMin * (coneConstant lamMin C / S) := by
  have hK : 0 < coneConstant lamMin C :=
    div_pos (mul_pos (by norm_num) (by linarith)) hlamMin
  have hr : 0 < coneConstant lamMin C / S := div_pos hK hS
  have hrhalf : coneConstant lamMin C / S ≤ 1 / 2 := by
    apply (div_le_iff₀ hS).mpr
    linarith
  have hquadratic : (1 + coneConstant lamMin C / S) ^ 2 ≤ 4 := by
    nlinarith
  have hbound : (C / S) * (1 + coneConstant lamMin C / S) ^ 2 ≤ 4 * (C / S) := by
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hquadratic (div_nonneg hC hS.le)
  have hscale : lamMin * (coneConstant lamMin C / S) = 4 * (C + 1) / S := by
    unfold coneConstant
    field_simp
  have hstrict : 4 * (C / S) < lamMin * (coneConstant lamMin C / S) := by
    rw [hscale]
    have h := (div_lt_div_iff_of_pos_right hS).mpr (show 4 * C < 4 * (C + 1) by linarith)
    convert! h using 1
    ring
  refine ⟨hr, hrhalf, ?_⟩
  nlinarith [mul_pos hlamMin hr]

/-- The fixed-width result in the exact `K/S` form used in (28). -/
theorem scaled_positive_invariant_cone
    {a b S C lamMin : ℝ} (hab : a ≤ b)
    (hlamMin : 0 < lamMin) (hC : 0 ≤ C) (hS : 0 < S)
    (hlarge : 2 * coneConstant lamMin C ≤ S)
    (lam damping e11 e12 e21 e22 : ℝ → ℝ) {z : ℝ → State}
    (hA : ContinuousOn (fun t =>
      modalOperator (lam t) (damping t) (e11 t) (e12 t) (e21 t) (e22 t)) (Icc a b))
    (hode : ∀ t ∈ Icc a b, HasDerivAt z
      (modalOperator (lam t) (damping t) (e11 t) (e12 t) (e21 t) (e22 t) (z t)) t)
    (hlam : ∀ t ∈ Icc a b, lamMin ≤ lam t)
    (herr : ∀ t ∈ Icc a b,
      |e11 t| ≤ C / S ∧ |e12 t| ≤ C / S ∧ |e21 t| ≤ C / S ∧ |e22 t| ≤ C / S)
    (hplus : 0 < z a 0) (hminus : z a 1 = 0) :
    ∀ t ∈ Icc a b, 0 < z t 0 ∧ |z t 1| ≤ (coneConstant lamMin C / S) * z t 0 := by
  obtain ⟨hr, _, hgap⟩ := scaled_cone_conditions hlamMin hC hS hlarge
  exact positive_invariant_cone hab hr hgap lam damping e11 e12 e21 e22
    hA hode hlam herr hplus hminus

/-- Derivative of the scalar integrating factor used for both sides of the comparison. -/
theorem hasDerivAt_weighted_scalar
    {p P : ℝ → ℝ} {p' rate μ a t : ℝ}
    (hp : HasDerivAt p p' t) (hP : HasDerivAt P (rate * P t) t) (hPne : P t ≠ 0) :
    HasDerivAt (fun s => Real.exp (μ * (s - a)) * p s / P s)
      (Real.exp (μ * (t - a)) / P t * (p' + (μ - rate) * p t)) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (μ * (s - a)))
      (Real.exp (μ * (t - a)) * μ) t := by
    simpa only [id, mul_one] using (((hasDerivAt_id t).sub_const a).const_mul μ).exp
  convert! (he.fun_mul hp).fun_div hP hPne using 1
  field_simp; ring

/-- A scalar positive envelope comparison from an actual relative derivative bound.
No lower bound on the unknown scalar solution is assumed. -/
theorem scalar_envelope_comparison
    {a b μ : ℝ} {p p' P rate : ℝ → ℝ} (hab : a ≤ b)
    (hPpos : ∀ t ∈ Icc a b, 0 < P t)
    (hP : ∀ t ∈ Icc a b, HasDerivAt P (rate t * P t) t)
    (hp : ∀ t ∈ Icc a b, HasDerivAt p (p' t) t)
    (herror : ∀ t ∈ Icc a b, |p' t - rate t * p t| ≤ μ * p t) :
    ∀ t ∈ Icc a b,
      Real.exp (-μ * (t - a)) * (p a / P a) * P t ≤ p t ∧
      p t ≤ Real.exp (μ * (t - a)) * (p a / P a) * P t := by
  let W : ℝ → ℝ → ℝ := fun m s => Real.exp (m * (s - a)) * p s / P s
  let W' : ℝ → ℝ → ℝ := fun m s =>
    Real.exp (m * (s - a)) / P s * (p' s + (m - rate s) * p s)
  have hd (m t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (W m) (W' m t) t :=
    hasDerivAt_weighted_scalar (hp t ht) (hP t ht) (ne_of_gt (hPpos t ht))
  have hmono : MonotoneOn (W μ) (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      (fun t ht => (hd μ t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd μ t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    dsimp [W']
    apply mul_nonneg (div_nonneg (Real.exp_pos _).le (hPpos t (interior_subset ht)).le)
    linarith [(abs_le.mp (herror t (interior_subset ht))).1]
  have hanti : AntitoneOn (W (-μ)) (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
      (fun t ht => (hd (-μ) t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd (-μ) t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    dsimp [W']
    apply mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg (Real.exp_pos _).le (hPpos t (interior_subset ht)).le)
    linarith [(abs_le.mp (herror t (interior_subset ht))).2]
  intro t ht
  have hlo := hmono ⟨le_rfl, hab⟩ ht ht.1
  have hhi := hanti ⟨le_rfl, hab⟩ ht ht.1
  dsimp [W] at hlo hhi
  simp only [sub_self, mul_zero, Real.exp_zero, one_mul] at hlo hhi
  constructor
  · have h := (le_div_iff₀ (hPpos t ht)).mp hlo
    have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (-μ * (t - a))).le
    have he : Real.exp (-μ * (t - a)) * Real.exp (μ * (t - a)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      Real.exp (-μ * (t - a)) * (p a / P a) * P t =
          Real.exp (-μ * (t - a)) * (p a / P a * P t) := by ring
      _ ≤ Real.exp (-μ * (t - a)) * (Real.exp (μ * (t - a)) * p t) := hmul
      _ = p t := by rw [← mul_assoc, he, one_mul]
  · have h := (div_le_iff₀ (hPpos t ht)).mp hhi
    have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (μ * (t - a))).le
    have he : Real.exp (μ * (t - a)) * Real.exp (-μ * (t - a)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      p t = Real.exp (μ * (t - a)) * (Real.exp (-μ * (t - a)) * p t) := by
        rw [← mul_assoc, he, one_mul]
      _ ≤ Real.exp (μ * (t - a)) * (p a / P a * P t) := hmul
      _ = Real.exp (μ * (t - a)) * (p a / P a) * P t := by ring

/-- Inside the proved cone, the growing coordinate has a multiplicative
derivative error. This is the only estimate used for its lower envelope. -/
theorem relative_error_of_cone
    {p q lam damping referenceDamping e11 e12 eps δ r : ℝ}
    (hp : 0 < p) (heps : 0 ≤ eps) (hcone : |q| ≤ r * p)
    (h11 : |e11| ≤ eps) (h12 : |e12| ≤ eps)
    (hd : |damping - referenceDamping| ≤ δ) :
    |(lam - damping + e11) * p + e12 * q - (lam - referenceDamping) * p| ≤
      (δ + eps * (1 + r)) * p := by
  have hd' : |referenceDamping - damping| ≤ δ := by
    simpa only [abs_sub_comm] using hd
  have hfirst : |(referenceDamping - damping + e11) * p| ≤ (δ + eps) * p := by
    rw [abs_mul, abs_of_pos hp]
    apply mul_le_mul_of_nonneg_right _ hp.le
    exact (abs_add_le _ _).trans (add_le_add hd' h11)
  have hsecond : |e12 * q| ≤ eps * (r * p) := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right h12 (abs_nonneg q)).trans
      (mul_le_mul_of_nonneg_left hcone heps)
  calc
    |(lam - damping + e11) * p + e12 * q - (lam - referenceDamping) * p| =
        |(referenceDamping - damping + e11) * p + e12 * q| := by
      congr 1
      ring
    _ ≤ |(referenceDamping - damping + e11) * p| + |e12 * q| := abs_add_le _ _
    _ ≤ (δ + eps) * p + eps * (r * p) := add_le_add hfirst hsecond
    _ = (δ + eps * (1 + r)) * p := by ring

/-- Positivity, the `K/S` cone, and two-sided bounds by a supplied reference
envelope on a slot of length at most `L*S`. None of these conclusions is assumed.

For the manuscript normalization `z a 0 = P a`, the ratio of initial values is one.
The comparison constants are `exp(±(D+2*C)*L)`, independent of the scale `S`.
-/
theorem scaled_growing_mode_bounds
    {a b S C D L lamMin : ℝ} (hab : a ≤ b)
    (hlamMin : 0 < lamMin) (hC : 0 ≤ C) (hD : 0 ≤ D) (hS : 0 < S)
    (hlarge : 2 * coneConstant lamMin C ≤ S) (hslot : b - a ≤ L * S)
    (lam damping referenceDamping e11 e12 e21 e22 P : ℝ → ℝ) {z : ℝ → State}
    (hA : ContinuousOn (fun t =>
      modalOperator (lam t) (damping t) (e11 t) (e12 t) (e21 t) (e22 t)) (Icc a b))
    (hode : ∀ t ∈ Icc a b, HasDerivAt z
      (modalOperator (lam t) (damping t) (e11 t) (e12 t) (e21 t) (e22 t) (z t)) t)
    (hlam : ∀ t ∈ Icc a b, lamMin ≤ lam t)
    (herr : ∀ t ∈ Icc a b,
      |e11 t| ≤ C / S ∧ |e12 t| ≤ C / S ∧ |e21 t| ≤ C / S ∧ |e22 t| ≤ C / S)
    (hdamping : ∀ t ∈ Icc a b, |damping t - referenceDamping t| ≤ D / S)
    (hPpos : ∀ t ∈ Icc a b, 0 < P t)
    (hP : ∀ t ∈ Icc a b, HasDerivAt P ((lam t - referenceDamping t) * P t) t)
    (hplus : 0 < z a 0) (hminus : z a 1 = 0) :
    ∀ t ∈ Icc a b,
      0 < z t 0 ∧ |z t 1| ≤ (coneConstant lamMin C / S) * z t 0 ∧
      Real.exp (-(D + 2 * C) * L) * (z a 0 / P a) * P t ≤ z t 0 ∧
      z t 0 ≤ Real.exp ((D + 2 * C) * L) * (z a 0 / P a) * P t := by
  have hcone := scaled_positive_invariant_cone hab hlamMin hC hS hlarge
    lam damping e11 e12 e21 e22 hA hode hlam herr hplus hminus
  have hrhalf := (scaled_cone_conditions hlamMin hC hS hlarge).2.1
  have hmu : D / S + (C / S) * (1 + coneConstant lamMin C / S) ≤ (D + 2 * C) / S := by
    have hmul : (C / S) * (coneConstant lamMin C / S) ≤ C / S := by
      have h := mul_le_mul_of_nonneg_left (show coneConstant lamMin C / S ≤ 1 by linarith)
        (div_nonneg hC hS.le)
      simpa only [mul_one] using h
    calc
      D / S + (C / S) * (1 + coneConstant lamMin C / S) ≤ D / S + 2 * (C / S) := by
        nlinarith
      _ = (D + 2 * C) / S := by ring
  let p' : ℝ → ℝ := fun t => (lam t - damping t + e11 t) * z t 0 + e12 t * z t 1
  have hp (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (fun s => z s 0) (p' t) t :=
    hasDerivAt_coordinate (hode t ht) 0
  have he (t : ℝ) (ht : t ∈ Icc a b) :
      |p' t - (lam t - referenceDamping t) * z t 0| ≤ ((D + 2 * C) / S) * z t 0 := by
    rcases herr t ht with ⟨h11, h12, _, _⟩
    have h := relative_error_of_cone (lam := lam t) (hcone t ht).1 (div_nonneg hC hS.le)
      (hcone t ht).2 h11 h12 (hdamping t ht)
    exact h.trans (mul_le_mul_of_nonneg_right hmu (hcone t ht).1.le)
  have hcomparison := scalar_envelope_comparison hab hPpos hP hp he
  have hmu0 : 0 ≤ (D + 2 * C) / S := div_nonneg (by linarith) hS.le
  intro t ht
  have hexponent : ((D + 2 * C) / S) * (t - a) ≤ (D + 2 * C) * L := by
    calc
      ((D + 2 * C) / S) * (t - a) ≤ ((D + 2 * C) / S) * (L * S) :=
        mul_le_mul_of_nonneg_left ((sub_le_sub_right ht.2 a).trans hslot) hmu0
      _ = (D + 2 * C) * L := by
        field_simp
  have hlo : Real.exp (-(D + 2 * C) * L) ≤
      Real.exp (-((D + 2 * C) / S) * (t - a)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hhi : Real.exp (((D + 2 * C) / S) * (t - a)) ≤
      Real.exp ((D + 2 * C) * L) := Real.exp_le_exp.mpr hexponent
  have hratio : 0 ≤ z a 0 / P a := div_nonneg hplus.le (hPpos a ⟨le_rfl, hab⟩).le
  refine ⟨(hcone t ht).1, (hcone t ht).2, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlo hratio)
      (hPpos t ht).le).trans (hcomparison t ht).1
  · exact (hcomparison t ht).2.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hhi hratio) (hPpos t ht).le)

/-- Returning from the modal cone to `x=p+q`, `y=h*(p-q)` gives both the
positive radial amplitude and the ratio error used in equation (28). -/
theorem original_coordinate_bounds {p q h r : ℝ}
    (hp : 0 < p) (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (hcone : |q| ≤ r * p) :
    p / 2 ≤ p + q ∧ p + q ≤ 3 * p / 2 ∧
      |h * (p - q) / (p + q) - h| ≤ 4 * |h| * r := by
  have hq := abs_le.mp hcone
  have hrp : r * p ≤ p / 2 := by nlinarith
  have hxlower : p / 2 ≤ p + q := by linarith
  have hxupper : p + q ≤ 3 * p / 2 := by linarith
  have hxpos : 0 < p + q := by linarith
  refine ⟨hxlower, hxupper, ?_⟩
  have heq : h * (p - q) / (p + q) - h = (-2 * h * q) / (p + q) := by
    field_simp; ring
  rw [heq, abs_div, abs_of_pos hxpos]
  apply (div_le_iff₀ hxpos).mpr
  have hnum : 2 * |h| * |q| ≤ 2 * |h| * (r * p) :=
    mul_le_mul_of_nonneg_left hcone (mul_nonneg (by norm_num) (abs_nonneg h))
  have hden : 4 * |h| * r * (p / 2) ≤ 4 * |h| * r * (p + q) :=
    mul_le_mul_of_nonneg_left hxlower (by positivity)
  simp only [abs_mul, abs_neg]
  rw [abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  nlinarith

end NavierStokes.GrowingMode
end


namespace NavierStokes.MovingFrameODE

open scoped InnerProductSpace ContDiff

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Frame := OrthonormalBasis (Fin 2) ℝ Plane

noncomputable def pack (r : ℝ) (w : Plane) : Space := !₂[r, w 0, w 1]
noncomputable def tail (w : Space) : Plane := !₂[w 1, w 2]
noncomputable def unitTheta : Plane := !₂[1, 0]

@[simp] theorem pack_zero (r : ℝ) (w : Plane) : pack r w 0 = r := rfl
@[simp] theorem pack_one (r : ℝ) (w : Plane) : pack r w 1 = w 0 := rfl
@[simp] theorem pack_two (r : ℝ) (w : Plane) : pack r w 2 = w 1 := rfl
@[simp] theorem tail_pack (r : ℝ) (w : Plane) : tail (pack r w) = w := by
  ext i
  fin_cases i <;> rfl
@[simp] theorem tail_add (u v : Space) : tail (u + v) = tail u + tail v := by
  ext i
  fin_cases i <;> rfl
@[simp] theorem tail_sub (u v : Space) : tail (u - v) = tail u - tail v := by
  ext i
  fin_cases i <;> rfl
@[simp] theorem tail_neg (u : Space) : tail (-u) = -tail u := by
  ext i
  fin_cases i <;> rfl
@[simp] theorem tail_smul (c : ℝ) (u : Space) : tail (c • u) = c • tail u := by
  ext i
  fin_cases i <;> rfl

theorem inner_pack (a b : ℝ) (u v : Plane) :
    ⟪pack a u, pack b v⟫_ℝ = a * b + ⟪u, v⟫_ℝ := by
  simp [pack, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  ring

theorem inner_pack_left (a : ℝ) (u : Plane) (v : Space) :
    ⟪pack a u, v⟫_ℝ = a * v 0 + ⟪u, tail v⟫_ℝ := by
  simp [pack, tail, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  ring

@[simp] theorem inner_unitTheta (w : Plane) : ⟪w, unitTheta⟫_ℝ = w 0 := by
  simp [unitTheta, PiLp.inner_apply, Fin.sum_univ_two]

@[simp] theorem frame_inner (B : Frame) (i j : Fin 2) :
    ⟪B i, B j⟫_ℝ = if i = j then 1 else 0 := (orthonormal_iff_ite.mp B.orthonormal) i j

@[simp] theorem frame_inner00 (B : Frame) : ⟪B 0, B 0⟫_ℝ = 1 := by
  simp only [frame_inner, ite_true]
@[simp] theorem frame_inner11 (B : Frame) : ⟪B 1, B 1⟫_ℝ = 1 := by
  simp only [frame_inner, ite_true]
@[simp] theorem frame_inner01 (B : Frame) : ⟪B 0, B 1⟫_ℝ = 0 := by
  exact B.inner_eq_zero (by decide)
@[simp] theorem frame_inner10 (B : Frame) : ⟪B 1, B 0⟫_ℝ = 0 := by
  exact B.inner_eq_zero (by decide)

theorem frame_expand (B : Frame) (w : Plane) :
    ⟪B 0, w⟫_ℝ • B 0 + ⟪B 1, w⟫_ℝ • B 1 = w := by
  simpa only [Fin.sum_univ_two] using B.sum_repr' w

theorem frame_ext (B : Frame) {u v : Space} (hr : u 0 = v 0)
    (hK : ⟪B 0, tail u⟫_ℝ = ⟪B 0, tail v⟫_ℝ)
    (hN : ⟪B 1, tail u⟫_ℝ = ⟪B 1, tail v⟫_ℝ) : u = v := by
  have ht : tail u = tail v := by
    rw [← frame_expand B (tail u), ← frame_expand B (tail v), hK, hN]
  ext i
  fin_cases i
  · exact hr
  · exact congrArg (fun w : Plane => w 0) ht
  · exact congrArg (fun w : Plane => w 1) ht

noncomputable def normal (β ρ : ℝ) (B : Frame) : Space :=
  pack (β * ρ) (β • B 0)

noncomputable def tangent (ρ : ℝ) (B : Frame) (x y : ℝ) : Space :=
  pack x ((-ρ * x) • B 0 + y • B 1)

noncomputable def normalMotion (β β' ρ ρ' rot : ℝ) (B : Frame) : Space :=
  pack (β' * ρ + β * ρ') (β' • B 0 + (β * rot) • B 1)

noncomputable def tangentMotion (ρ ρ' rot : ℝ) (B : Frame)
    (x y x' y' : ℝ) : Space :=
  pack x' (-(ρ' * x + ρ * x' + rot * y) • B 0 +
    (y' - ρ * rot * x) • B 1)

/-- The exact zeroth-order ambient matrix from the pulse equation. -/
noncomputable def baseAction (F : ℝ) (g : Plane) (t : Space) : Space :=
  pack (-2 * F * (tail t) 0) ((t 0) • ((2 * F) • unitTheta + g))

theorem normal_ne_zero {β ρ : ℝ} (B : Frame) (hβ : β ≠ 0) : normal β ρ B ≠ 0 := by
  intro hz
  have ht := congrArg tail hz
  have hi := congrArg (fun w : Plane => ⟪B 0, w⟫_ℝ) ht
  simp only [normal, tail_pack, show tail (0 : Space) = 0 by ext i; fin_cases i <;> rfl,
    inner_smul_right, frame_inner, ite_true, mul_one, inner_zero_right] at hi
  exact hβ hi

@[simp] theorem normal_tangent (β ρ : ℝ) (B : Frame) (x y : ℝ) :
    ⟪normal β ρ B, tangent ρ B x y⟫_ℝ = 0 := by
  simp only [normal, tangent, inner_pack, real_inner_smul_left, inner_smul_right, inner_add_right,
    frame_inner00, frame_inner01, mul_one, mul_zero, add_zero]
  ring

theorem normal_self (β ρ : ℝ) (B : Frame) :
    ⟪normal β ρ B, normal β ρ B⟫_ℝ = β ^ 2 * (1 + ρ ^ 2) := by
  simp only [normal, inner_pack, real_inner_smul_left, inner_smul_right,
    frame_inner00, mul_one]
  ring

theorem normalMotion_tangent (β β' ρ ρ' rot : ℝ) (B : Frame) (x y : ℝ) :
    ⟪normalMotion β β' ρ ρ' rot B, tangent ρ B x y⟫_ℝ =
      β * (ρ' * x + rot * y) := by
  simp only [normalMotion, tangent, inner_pack, inner_add_left, inner_add_right,
    real_inner_smul_left, inner_smul_right, frame_inner00, frame_inner01, frame_inner10,
    frame_inner11, mul_one, mul_zero, add_zero, zero_add]
  ring

theorem normal_tangentMotion (β ρ ρ' rot : ℝ) (B : Frame) (x y x' y' : ℝ) :
    ⟪normal β ρ B, tangentMotion ρ ρ' rot B x y x' y'⟫_ℝ =
      -β * (ρ' * x + rot * y) := by
  simp only [normal, tangentMotion, inner_pack, inner_add_right,
    real_inner_smul_left, inner_smul_right, frame_inner00, frame_inner01, mul_one, mul_zero, add_zero]
  ring

theorem normal_inner (β ρ : ℝ) (B : Frame) (v : Space) :
    ⟪normal β ρ B, v⟫_ℝ = β * ρ * v 0 + β * ⟪B 0, tail v⟫_ℝ := by
  rw [normal, inner_pack_left, real_inner_smul_left]

theorem normal_baseAction (β ρ F : ℝ) (B : Frame) (g : Plane) (x y : ℝ) :
    ⟪normal β ρ B, baseAction F g (tangent ρ B x y)⟫_ℝ =
      β * ((2 * F * (1 + ρ ^ 2) * (B 0) 0 + ⟪B 0, g⟫_ℝ) * x -
        2 * F * ρ * (B 1) 0 * y) := by
  simp only [normal, baseAction, tangent, inner_pack, inner_add_right,
    real_inner_smul_left, inner_smul_right, inner_unitTheta, tail_pack, pack_zero, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

/-- Coefficients before subtracting the scalar viscous damping. -/
noncomputable def coeff11 (ρ ρ' gK : ℝ) : ℝ := ρ * (gK - ρ') / (1 + ρ ^ 2)
noncomputable def coeff12 (F Nθ ρ rot : ℝ) : ℝ := (2 * F * Nθ - ρ * rot) / (1 + ρ ^ 2)
noncomputable def coeff21 (F Nθ gN ρ rot : ℝ) : ℝ := -(2 * F * Nθ + gN) + ρ * rot

noncomputable def rhsX (F d ρ ρ' rot : ℝ) (B : Frame) (g : Plane)
    (f : Space) (x y : ℝ) : ℝ :=
  (coeff11 ρ ρ' ⟪B 0, g⟫_ℝ - d) * x + coeff12 F ((B 1) 0) ρ rot * y -
    (f 0 - ρ * ⟪B 0, tail f⟫_ℝ) / (1 + ρ ^ 2)

noncomputable def rhsY (F d ρ rot : ℝ) (B : Frame) (g : Plane)
    (f : Space) (x y : ℝ) : ℝ :=
  coeff21 F ((B 1) 0) ⟪B 1, g⟫_ℝ ρ rot * x - d * y - ⟪B 1, tail f⟫_ℝ

theorem projectedRhs_radial {β : ℝ} (hβ : β ≠ 0)
    (β' ρ ρ' rot F d : ℝ) (B : Frame) (g : Plane) (f : Space) (x y : ℝ) :
    TangentProjection.projectedRhs (normal β ρ B) (normalMotion β β' ρ ρ' rot B)
      (tangent ρ B x y) (baseAction F g (tangent ρ B x y)) f d 0 =
        rhsX F d ρ ρ' rot B g f x y := by
  have hden : 1 + ρ ^ 2 ≠ 0 := by positivity
  rw [TangentProjection.projectedRhs, TangentProjection.tangentProj,
    normal_self, normalMotion_tangent, normal_baseAction, normal_inner]
  simp only [normal, tangent, baseAction, rhsX, coeff11, coeff12, pack_zero, tail_pack,
    PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp ; ring

theorem projectedRhs_N (β β' ρ ρ' rot F d : ℝ) (B : Frame) (g : Plane)
    (f : Space) (x y : ℝ) :
    ⟪B 1, tail (TangentProjection.projectedRhs (normal β ρ B)
      (normalMotion β β' ρ ρ' rot B) (tangent ρ B x y)
      (baseAction F g (tangent ρ B x y)) f d)⟫_ℝ =
        rhsY F d ρ rot B g f x y - ρ * rot * x := by
  simp only [TangentProjection.projectedRhs, TangentProjection.tangentProj,
    tail_sub, tail_add, tail_neg, tail_smul, normal, tangent, baseAction, tail_pack,
    pack_zero, rhsY, coeff21, inner_sub_right, inner_add_right, inner_neg_right,
    inner_smul_right, inner_unitTheta, frame_inner10,
    frame_inner11, mul_one, mul_zero, add_zero, zero_add, sub_zero]
  ring

/-- Exact moving-frame reduction of the ambient projected equation. -/
theorem projectedRhs_eq_tangentMotion {β : ℝ} (hβ : β ≠ 0)
    (β' ρ ρ' rot F d : ℝ) (B : Frame) (g : Plane) (f : Space) (x y : ℝ) :
    TangentProjection.projectedRhs (normal β ρ B) (normalMotion β β' ρ ρ' rot B)
      (tangent ρ B x y) (baseAction F g (tangent ρ B x y)) f d =
    tangentMotion ρ ρ' rot B x y
      (rhsX F d ρ ρ' rot B g f x y) (rhsY F d ρ rot B g f x y) := by
  apply frame_ext B
  · exact projectedRhs_radial hβ β' ρ ρ' rot F d B g f x y
  · have hn := TangentProjection.normal_projectedRhs_of_tangent
      (normal_ne_zero B hβ) (normalMotion β β' ρ ρ' rot B) (tangent ρ B x y)
      (baseAction F g (tangent ρ B x y)) f d (normal_tangent β ρ B x y)
    rw [normalMotion_tangent] at hn
    have hm := normal_tangentMotion β ρ ρ' rot B x y
      (rhsX F d ρ ρ' rot B g f x y) (rhsY F d ρ rot B g f x y)
    have heq : ⟪normal β ρ B,
        TangentProjection.projectedRhs (normal β ρ B) (normalMotion β β' ρ ρ' rot B)
          (tangent ρ B x y) (baseAction F g (tangent ρ B x y)) f d⟫_ℝ =
      ⟪normal β ρ B, tangentMotion ρ ρ' rot B x y
        (rhsX F d ρ ρ' rot B g f x y) (rhsY F d ρ rot B g f x y)⟫_ℝ := by
      rw [hn, hm]
      ring
    rw [normal_inner, normal_inner] at heq
    rw [projectedRhs_radial hβ] at heq
    change β * ρ * _ + β * _ = β * ρ * rhsX F d ρ ρ' rot B g f x y + β * _ at heq
    exact (mul_left_cancel₀ hβ) (by linarith [heq])
  · rw [projectedRhs_N]
    simp only [tangentMotion, tail_pack, inner_add_right, inner_smul_right,
      frame_inner10, frame_inner11, mul_zero, mul_one, zero_add]

/-- The moving-coordinate equation has exactly two scalar equations. -/
theorem tangentMotion_eq_projectedRhs_iff {β : ℝ} (hβ : β ≠ 0)
    (β' ρ ρ' rot F d : ℝ) (B : Frame) (g : Plane) (f : Space) (x y x' y' : ℝ) :
    tangentMotion ρ ρ' rot B x y x' y' =
      TangentProjection.projectedRhs (normal β ρ B) (normalMotion β β' ρ ρ' rot B)
        (tangent ρ B x y) (baseAction F g (tangent ρ B x y)) f d ↔
    x' = rhsX F d ρ ρ' rot B g f x y ∧ y' = rhsY F d ρ rot B g f x y := by
  rw [projectedRhs_eq_tangentMotion hβ]
  constructor
  · intro h
    constructor
    · exact congrArg (fun v : Space => v 0) h
    · have hn := congrArg (fun v : Space => ⟪B 1, tail v⟫_ℝ) h
      simp only [tangentMotion, tail_pack, inner_add_right, inner_smul_right,
      frame_inner10, frame_inner11, mul_zero, mul_one, zero_add] at hn
      linarith
  · rintro ⟨rfl, rfl⟩
    rfl

noncomputable def packCLM : (ℝ × Plane) →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap {
    toFun := fun p => pack p.1 p.2
    map_add' := by
      intro u v
      ext i
      fin_cases i <;> simp [pack]
    map_smul' := by
      intro c u
      ext i
      fin_cases i <;> simp [pack] }

noncomputable def tailCLM : Space →L[ℝ] Plane :=
  LinearMap.toContinuousLinearMap {
    toFun := tail
    map_add' := tail_add
    map_smul' := tail_smul }

theorem hasDerivAt_pack {r : ℝ → ℝ} {w : ℝ → Plane} {r' v : ℝ} {w' : Plane}
    (hr : HasDerivAt r r' v) (hw : HasDerivAt w w' v) :
    HasDerivAt (fun s => pack (r s) (w s)) (pack r' w') v :=
  packCLM.hasFDerivAt.comp_hasDerivAt v (hr.prodMk hw)

/-- Differentiation of the actual normal.  The frame derivative is measured in
the same moving orthonormal basis. -/
theorem hasDerivAt_normal {β ρ : ℝ → ℝ} {B : ℝ → Frame}
    {v β' ρ' rot : ℝ} (hβ : HasDerivAt β β' v) (hρ : HasDerivAt ρ ρ' v)
    (hK : HasDerivAt (fun s => B s 0) (rot • B v 1) v) :
    HasDerivAt (fun s => normal (β s) (ρ s) (B s))
      (normalMotion (β v) β' (ρ v) ρ' rot (B v)) v := by
  convert! hasDerivAt_pack (hβ.mul hρ) (hβ.smul hK) using 1
  ext i
  fin_cases i <;> simp [normalMotion, pack] <;> ring

/-- Differentiation of the actual tangent parametrization. -/
theorem hasDerivAt_tangent {ρ x y : ℝ → ℝ} {B : ℝ → Frame}
    {v ρ' rot x' y' : ℝ} (hρ : HasDerivAt ρ ρ' v)
    (hx : HasDerivAt x x' v) (hy : HasDerivAt y y' v)
    (hK : HasDerivAt (fun s => B s 0) (rot • B v 1) v)
    (hN : HasDerivAt (fun s => B s 1) (-rot • B v 0) v) :
    HasDerivAt (fun s => tangent (ρ s) (B s) (x s) (y s))
      (tangentMotion (ρ v) ρ' rot (B v) (x v) (y v) x' y') v := by
  convert! hasDerivAt_pack hx (((hρ.neg.mul hx).smul hK).add (hy.smul hN)) using 1
  ext i
  fin_cases i <;> simp [tangentMotion, pack] <;> ring

/-- The ambient ODE is equivalent to the two explicit coordinate ODEs, using
actual derivatives of the curve and the moving frame. -/
theorem hasDerivAt_projected_iff {β ρ x y : ℝ → ℝ} {B : ℝ → Frame}
    {v β' ρ' rot x' y' F d : ℝ} {g : Plane} {f : Space}
    (hβ0 : β v ≠ 0) (hρ : HasDerivAt ρ ρ' v)
    (hx : HasDerivAt x x' v) (hy : HasDerivAt y y' v)
    (hK : HasDerivAt (fun s => B s 0) (rot • B v 1) v)
    (hN : HasDerivAt (fun s => B s 1) (-rot • B v 0) v) :
    HasDerivAt (fun s => tangent (ρ s) (B s) (x s) (y s))
      (TangentProjection.projectedRhs (normal (β v) (ρ v) (B v))
        (normalMotion (β v) β' (ρ v) ρ' rot (B v))
        (tangent (ρ v) (B v) (x v) (y v))
        (baseAction F g (tangent (ρ v) (B v) (x v) (y v))) f d) v ↔
    x' = rhsX F d (ρ v) ρ' rot (B v) g f (x v) (y v) ∧
      y' = rhsY F d (ρ v) rot (B v) g f (x v) (y v) := by
  have ht := hasDerivAt_tangent hρ hx hy hK hN
  rw [← tangentMotion_eq_projectedRhs_iff hβ0]
  constructor
  · intro h
    exact ht.unique h
  · intro h
    exact h ▸ ht

/-- Counterclockwise quarter-turn in the angular-axial plane. -/
noncomputable def quarterTurn : Plane →L[ℝ] Plane :=
  LinearMap.toContinuousLinearMap {
    toFun := fun w => !₂[-w 1, w 0]
    map_add' := by
      intro u v
      ext i
      fin_cases i <;> simp
      ring
    map_smul' := by
      intro c u
      ext i
      fin_cases i <;> simp }

theorem quarterTurn_square (w : Plane) : quarterTurn (quarterTurn w) = -w := by
  ext i
  fin_cases i <;> simp [quarterTurn]

theorem inner_quarterTurn_self (w : Plane) : ⟪w, quarterTurn w⟫_ℝ = 0 := by
  simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem quarterTurn_inner (u v : Plane) :
    ⟪quarterTurn u, quarterTurn v⟫_ℝ = ⟪u, v⟫_ℝ := by
  simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem unit_pair_orthonormal (K : Plane) (hK : ‖K‖ = 1) :
    Orthonormal ℝ ![K, quarterTurn K] := by
  apply orthonormal_iff_ite.mpr
  intro i j
  fin_cases i <;> fin_cases j
  · change ⟪K, K⟫_ℝ = 1
    rw [real_inner_self_eq_norm_sq, hK]
    norm_num
  · change ⟪K, quarterTurn K⟫_ℝ = 0
    exact inner_quarterTurn_self K
  · change ⟪quarterTurn K, K⟫_ℝ = 0
    rw [real_inner_comm, inner_quarterTurn_self]
  · change ⟪quarterTurn K, quarterTurn K⟫_ℝ = 1
    rw [quarterTurn_inner, real_inner_self_eq_norm_sq, hK]
    norm_num

noncomputable def frameOfUnit (K : Plane) (hK : ‖K‖ = 1) : Frame :=
  (basisOfOrthonormalOfCardEqFinrank (unit_pair_orthonormal K hK) (by simp [Plane])).toOrthonormalBasis
    (by simpa using unit_pair_orthonormal K hK)

@[simp] theorem frameOfUnit_zero (K : Plane) (hK : ‖K‖ = 1) : frameOfUnit K hK 0 = K := by
  simp [frameOfUnit]

@[simp] theorem frameOfUnit_one (K : Plane) (hK : ‖K‖ = 1) :
    frameOfUnit K hK 1 = quarterTurn K := by
  simp [frameOfUnit]

noncomputable def normalScale (n : Space) : ℝ := ‖tail n‖
noncomputable def radialSlope (n : Space) : ℝ := n 0 / normalScale n
noncomputable def normalDirection (n : Space) : Plane := (normalScale n)⁻¹ • tail n

theorem normalScale_pos {n : Space} (hn : tail n ≠ 0) : 0 < normalScale n :=
  norm_pos_iff.mpr hn

theorem normalDirection_unit {n : Space} (hn : tail n ≠ 0) : ‖normalDirection n‖ = 1 := by
  simp only [normalDirection, normalScale, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn)

noncomputable def normalFrame (n : Space) (hn : tail n ≠ 0) : Frame :=
  frameOfUnit (normalDirection n) (normalDirection_unit hn)

@[simp] theorem normalFrame_zero (n : Space) (hn : tail n ≠ 0) :
    normalFrame n hn 0 = normalDirection n := frameOfUnit_zero _ _

@[simp] theorem normalFrame_one (n : Space) (hn : tail n ≠ 0) :
    normalFrame n hn 1 = quarterTurn (normalDirection n) := frameOfUnit_one _ _

/-- Reconstruction of the given normal, not an independent choice of reference
normal.  Only its tangential part is required to be nonzero. -/
theorem normal_reconstructed {n : Space} (hn : tail n ≠ 0) :
    normal (normalScale n) (radialSlope n) (normalFrame n hn) = n := by
  have hscale : normalScale n ≠ 0 := (normalScale_pos hn).ne'
  simp only [normal, radialSlope, normalFrame_zero, normalDirection,
    smul_smul, mul_inv_cancel₀ hscale, one_smul]
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, pack_zero]
    field_simp
  · rfl
  · rfl

section SmoothFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m : WithTop ℕ∞} {n : E → Space} {q : E}

theorem contDiffAt_normalScale (hn : ContDiffAt ℝ m n q) (hne : tail (n q) ≠ 0) :
    ContDiffAt ℝ m (fun p => normalScale (n p)) q := by
  exact (tailCLM.contDiff.contDiffAt.comp q hn).norm ℝ hne

theorem contDiffAt_radialSlope (hn : ContDiffAt ℝ m n q) (hne : tail (n q) ≠ 0) :
    ContDiffAt ℝ m (fun p => radialSlope (n p)) q := by
  exact ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0).contDiff.contDiffAt.comp q hn).div
    (contDiffAt_normalScale hn hne) (normalScale_pos hne).ne'

theorem contDiffAt_normalDirection (hn : ContDiffAt ℝ m n q) (hne : tail (n q) ≠ 0) :
    ContDiffAt ℝ m (fun p => normalDirection (n p)) q := by
  exact ((contDiffAt_normalScale hn hne).inv (normalScale_pos hne).ne').smul
    (tailCLM.contDiff.contDiffAt.comp q hn)


end SmoothFrame


/-- A differentiable unit vector has purely rotational derivative in its
orthonormal frame.  The angular speed is computed from the derivative. -/
theorem unit_curve_rotation {K : ℝ → Plane} {K' : Plane} {v : ℝ}
    (hK : HasDerivAt K K' v) (hunit : ∀ᶠ s in nhds v, ‖K s‖ = 1) :
    K' = ⟪quarterTurn (K v), K'⟫_ℝ • quarterTurn (K v) := by
  have hnorm : ‖K v‖ = 1 := Filter.EventuallyEq.eq_of_nhds hunit
  have heq : (fun s => ⟪K s, K s⟫_ℝ) =ᶠ[nhds v] (fun _ => (1 : ℝ)) := by
    filter_upwards [hunit] with s hs
    rw [real_inner_self_eq_norm_sq, hs, one_pow]
  have hd := (hasDerivAt_const v (1 : ℝ)).congr_of_eventuallyEq heq
  have hh := (hK.inner ℝ hK).unique hd
  have horth : ⟪K v, K'⟫_ℝ = 0 := by
    rw [real_inner_comm (K v) K'] at hh
    linarith
  have hb := frame_expand (frameOfUnit (K v) hnorm) K'
  simpa only [frameOfUnit_zero, frameOfUnit_one, horth, zero_smul, zero_add] using hb.symm

/-- Rotation of the second direction is derived, rather than assumed
independently of the first direction. -/
theorem hasDerivAt_quarterTurn_of_rotation {K : ℝ → Plane} {v rot : ℝ}
    (hK : HasDerivAt K (rot • quarterTurn (K v)) v) :
    HasDerivAt (fun s => quarterTurn (K s)) (-rot • K v) v := by
  have h := quarterTurn.hasFDerivAt.comp_hasDerivAt v hK
  simpa only [Function.comp_def, map_smul, quarterTurn_square, smul_neg, neg_smul] using h


/-! ## Quantitative coefficient comparison -/

theorem abs_div_le_of_one_le (a d : ℝ) (hd : 1 ≤ d) : |a / d| ≤ |a| := by
  rw [abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hd)]
  exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hd)).2
    (by nlinarith [abs_nonneg a])

theorem reciprocal_quadratic_difference (r s : ℝ) :
    |1 / (1 + r ^ 2) - 1 / (1 + s ^ 2)| ≤ |r - s| * (|r| + |s|) := by
  have hr : 1 + r ^ 2 ≠ 0 := by positivity
  have hs : 1 + s ^ 2 ≠ 0 := by positivity
  have heq : 1 / (1 + r ^ 2) - 1 / (1 + s ^ 2) =
      (s - r) * (s + r) / ((1 + r ^ 2) * (1 + s ^ 2)) := by
    field_simp ; ring
  rw [heq]
  calc
    |(s - r) * (s + r) / ((1 + r ^ 2) * (1 + s ^ 2))| ≤ |(s - r) * (s + r)| :=
      abs_div_le_of_one_le _ _ (by
        nlinarith only [sq_nonneg r, sq_nonneg s, mul_nonneg (sq_nonneg r) (sq_nonneg s)])
    _ ≤ |r - s| * (|r| + |s|) := by
      rw [abs_mul, abs_sub_comm s r]
      exact mul_le_mul_of_nonneg_left (by linarith [abs_add_le s r]) (abs_nonneg _)

theorem product_perturbation_le {F F0 N N0 M η : ℝ}
    (hN : |N| ≤ 1) (hF0 : |F0| ≤ M)
    (hF : |F - F0| ≤ η) (hNd : |N - N0| ≤ η) :
    |F * N - F0 * N0| ≤ (1 + M) * η := by
  have hη : 0 ≤ η := (abs_nonneg _).trans hF
  have hM : 0 ≤ M := (abs_nonneg _).trans hF0
  calc
    |F * N - F0 * N0| = |(F - F0) * N + F0 * (N - N0)| := by congr 1; ring
    _ ≤ |(F - F0) * N| + |F0 * (N - N0)| := abs_add_le _ _
    _ = |F - F0| * |N| + |F0| * |N - N0| := by rw [abs_mul, abs_mul]
    _ ≤ η * 1 + M * η := add_le_add
      (mul_le_mul hF hN (abs_nonneg _) hη)
      (mul_le_mul hF0 hNd (abs_nonneg _) hM)
    _ = (1 + M) * η := by ring

/-- Explicit bounds in geometric coordinates.  The four small quantities are
the normal slope error, rotation, radial slope derivative and projected shear.
No coefficient or propagator estimate is included among the assumptions. -/
theorem scalar_coefficients_close
    {F F0 N N0 ρ s ρ' rot gK gN g0 M η : ℝ}
    (hM : 1 ≤ M) (hη : 0 ≤ η) (hρ : |ρ| ≤ M) (hs : |s| ≤ M)
    (hN : |N| ≤ 1) (hN0 : |N0| ≤ 1) (hF0 : |F0| ≤ M)
    (hF : |F - F0| ≤ η) (hNd : |N - N0| ≤ η) (hρd : |ρ - s| ≤ η)
    (hρ' : |ρ'| ≤ η) (hrot : |rot| ≤ η) (hgK : |gK| ≤ η)
    (hgN : |gN - g0| ≤ η) :
    |coeff11 ρ ρ' gK| ≤ 16 * M ^ 2 * η ∧
    |coeff12 F N ρ rot - 2 * F0 * N0 / (1 + s ^ 2)| ≤ 16 * M ^ 2 * η ∧
    |coeff21 F N gN ρ rot - (-(2 * F0 * N0 + g0))| ≤ 16 * M ^ 2 * η := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hprod := product_perturbation_le hN hF0 hF hNd
  have hrotation : |ρ * rot| ≤ M * η := by
    rw [abs_mul]
    exact mul_le_mul hρ hrot (abs_nonneg _) hM0
  have htwoprod : |2 * F * N - 2 * F0 * N0| ≤ 2 * (1 + M) * η := by
    calc
      |2 * F * N - 2 * F0 * N0| = 2 * |F * N - F0 * N0| := by
        calc
          _ = |2 * (F * N - F0 * N0)| := by congr 1; ring
          _ = _ := by rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      _ ≤ 2 * ((1 + M) * η) := mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = _ := by ring
  have hnum : |2 * F * N - ρ * rot - 2 * F0 * N0| ≤ (2 + 3 * M) * η := by
    calc
      |2 * F * N - ρ * rot - 2 * F0 * N0| =
          |(2 * F * N - 2 * F0 * N0) - ρ * rot| := by congr 1; ring
      _ ≤ |2 * F * N - 2 * F0 * N0| + |ρ * rot| := abs_sub _ _
      _ ≤ 2 * (1 + M) * η + M * η := add_le_add htwoprod hrotation
      _ = _ := by ring
  have hinv : |1 / (1 + ρ ^ 2) - 1 / (1 + s ^ 2)| ≤ 2 * M * η := by
    calc
      _ ≤ |ρ - s| * (|ρ| + |s|) := reciprocal_quadratic_difference ρ s
      _ ≤ η * (M + M) := mul_le_mul hρd (add_le_add hρ hs)
        (add_nonneg (abs_nonneg _) (abs_nonneg _)) hη
      _ = _ := by ring
  have hreference : |2 * F0 * N0| ≤ 2 * M := by
    rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    calc
      2 * |F0| * |N0| ≤ (2 * M) * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left hF0 (by norm_num)) hN0 (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  constructor
  · calc
      |coeff11 ρ ρ' gK| ≤ |ρ * (gK - ρ')| := abs_div_le_of_one_le _ _ (by nlinarith only [sq_nonneg ρ])
      _ = |ρ| * |gK - ρ'| := abs_mul _ _
      _ ≤ M * (η + η) := mul_le_mul hρ ((abs_sub _ _).trans (add_le_add hgK hρ'))
        (abs_nonneg _) hM0
      _ ≤ 16 * M ^ 2 * η := by
        have h := mul_le_mul_of_nonneg_right (show 2 * M ≤ 16 * M ^ 2 by nlinarith only [hM, sq_nonneg (M - 1)]) hη
        nlinarith only [h]
  constructor
  · have hρden : 1 + ρ ^ 2 ≠ 0 := by positivity
    have hsden : 1 + s ^ 2 ≠ 0 := by positivity
    have heq : coeff12 F N ρ rot - 2 * F0 * N0 / (1 + s ^ 2) =
        (2 * F * N - ρ * rot - 2 * F0 * N0) / (1 + ρ ^ 2) +
        (2 * F0 * N0) * (1 / (1 + ρ ^ 2) - 1 / (1 + s ^ 2)) := by
      unfold coeff12
      field_simp ; ring
    rw [heq]
    calc
      _ ≤ |(2 * F * N - ρ * rot - 2 * F0 * N0) / (1 + ρ ^ 2)| +
          |(2 * F0 * N0) * (1 / (1 + ρ ^ 2) - 1 / (1 + s ^ 2))| := abs_add_le _ _
      _ ≤ (2 + 3 * M) * η + (2 * M) * (2 * M * η) := add_le_add
        ((abs_div_le_of_one_le _ _ (by nlinarith only [sq_nonneg ρ])).trans hnum)
        (by rw [abs_mul]; exact mul_le_mul hreference hinv (abs_nonneg _) (by positivity))
      _ ≤ 16 * M ^ 2 * η := by
        have h := mul_le_mul_of_nonneg_right
          (show 2 + 3 * M + 4 * M ^ 2 ≤ 16 * M ^ 2 by nlinarith only [hM, sq_nonneg (M - 1)]) hη
        nlinarith only [h]
  · calc
      |coeff21 F N gN ρ rot - (-(2 * F0 * N0 + g0))| =
          |-(2 * F * N - 2 * F0 * N0) - (gN - g0) + ρ * rot| := by
        unfold coeff21
        congr 1
        ring
      _ ≤ |-(2 * F * N - 2 * F0 * N0) - (gN - g0)| + |ρ * rot| := abs_add_le _ _
      _ ≤ (|2 * F * N - 2 * F0 * N0| + |gN - g0|) + |ρ * rot| := by
        exact add_le_add_left (by
          simpa only [abs_neg] using abs_sub (-(2 * F * N - 2 * F0 * N0)) (gN - g0)) _
      _ ≤ (2 * (1 + M) * η + η) + M * η := add_le_add (add_le_add htwoprod hgN) hrotation
      _ ≤ 16 * M ^ 2 * η := by
        have h := mul_le_mul_of_nonneg_right (show 3 + 3 * M ≤ 16 * M ^ 2 by nlinarith only [hM, sq_nonneg (M - 1)]) hη
        nlinarith only [h]

theorem inner_perturbation_le {K K0 g g0 : Plane} {M η : ℝ}
    (hK : ‖K‖ ≤ 1) (hg0 : ‖g0‖ ≤ M)
    (hKd : ‖K - K0‖ ≤ η) (hgd : ‖g - g0‖ ≤ η) :
    |⟪K, g⟫_ℝ - ⟪K0, g0⟫_ℝ| ≤ (1 + M) * η := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hKd
  have hM : 0 ≤ M := (norm_nonneg _).trans hg0
  calc
    |⟪K, g⟫_ℝ - ⟪K0, g0⟫_ℝ| = |⟪K, g - g0⟫_ℝ + ⟪K - K0, g0⟫_ℝ| := by
      rw [inner_sub_left, inner_sub_right]
      congr 1
      ring
    _ ≤ |⟪K, g - g0⟫_ℝ| + |⟪K - K0, g0⟫_ℝ| := abs_add_le _ _
    _ ≤ ‖K‖ * ‖g - g0‖ + ‖K - K0‖ * ‖g0‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ 1 * η + η * M := add_le_add
      (mul_le_mul hK hgd (norm_nonneg _) zero_le_one)
      (mul_le_mul hKd hg0 (norm_nonneg _) hη)
    _ = (1 + M) * η := by ring

theorem frame_coordinate_abs_le_one (B : Frame) (i j : Fin 2) : |B i j| ≤ 1 := by
  simpa only [Real.norm_eq_abs, B.norm_eq_one] using PiLp.norm_apply_le (B i) j

theorem frame_coordinate_difference_le {B B0 : Frame} {i j : Fin 2} {η : ℝ}
    (h : ‖B i - B0 i‖ ≤ η) : |B i j - B0 i j| ≤ η := by
  have h' := (PiLp.norm_apply_le (B i - B0 i) j).trans h
  simpa only [PiLp.sub_apply, Real.norm_eq_abs] using h'

/-- Norm bounds on actual geometric data imply the matrix comparison.
Taking `η = C / S` gives the required `O(1/S)` with the displayed constant.
The reference shear is perpendicular to the reference normal direction. -/
theorem frame_coefficients_close {B B0 : Frame} {g g0 : Plane}
    {F F0 ρ s ρ' rot M η : ℝ}
    (hM : 1 ≤ M) (hη : 0 ≤ η) (hρ : |ρ| ≤ M) (hs : |s| ≤ M)
    (hF0 : |F0| ≤ M) (hg0 : ‖g0‖ ≤ M) (horth : ⟪B0 0, g0⟫_ℝ = 0)
    (hF : |F - F0| ≤ η) (hg : ‖g - g0‖ ≤ η)
    (hK : ‖B 0 - B0 0‖ ≤ η) (hN : ‖B 1 - B0 1‖ ≤ η)
    (hρd : |ρ - s| ≤ η) (hρ' : |ρ'| ≤ η) (hrot : |rot| ≤ η) :
    |coeff11 ρ ρ' ⟪B 0, g⟫_ℝ| ≤ (16 * M ^ 2 * (1 + M)) * η ∧
    |coeff12 F ((B 1) 0) ρ rot - 2 * F0 * ((B0 1) 0) / (1 + s ^ 2)| ≤
      (16 * M ^ 2 * (1 + M)) * η ∧
    |coeff21 F ((B 1) 0) ⟪B 1, g⟫_ℝ ρ rot - (-(2 * F0 * ((B0 1) 0) + ⟪B0 1, g0⟫_ℝ))| ≤
      (16 * M ^ 2 * (1 + M)) * η := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have henlarge : η ≤ (1 + M) * η := by nlinarith only [mul_nonneg hM0 hη]
  have hgK := inner_perturbation_le (le_of_eq (B.norm_eq_one 0)) hg0 hK hg
  rw [horth, sub_zero] at hgK
  have hgN := inner_perturbation_le (le_of_eq (B.norm_eq_one 1)) hg0 hN hg
  have h := scalar_coefficients_close hM (hη.trans henlarge) hρ hs
    (frame_coordinate_abs_le_one B 1 0) (frame_coordinate_abs_le_one B0 1 0) hF0
    (hF.trans henlarge) ((frame_coordinate_difference_le (j := 0) hN).trans henlarge)
    (hρd.trans henlarge) (hρ'.trans henlarge) (hrot.trans henlarge) hgK hgN
  simpa only [mul_assoc] using h

/-! ## The moving eigenbasis, including its derivative -/

noncomputable def modal11 (a b c h rate : ℝ) : ℝ := (a + h * b + c / h - rate) / 2
noncomputable def modal12 (a b c h rate : ℝ) : ℝ := (a - h * b + c / h + rate) / 2
noncomputable def modal21 (a b c h rate : ℝ) : ℝ := (a + h * b - c / h + rate) / 2
noncomputable def modal22 (a b c h rate : ℝ) : ℝ := (a - h * b - c / h - rate) / 2

/-- Exact change to `x = p + q`, `y = h (p - q)`, with `h' = rate * h`.
Here the reference off-diagonal entries are `λ/h` and `λ*h`, and `a,b,c`
are the three errors already estimated by `frame_coefficients_close`. -/
theorem modal_equations_iff {h : ℝ} (hh : h ≠ 0)
    (p q p' q' lam damping a b c rate fx fy : ℝ) :
    (p' + q' = (a - damping) * (p + q) + (lam / h + b) * (h * (p - q)) + fx ∧
      rate * h * (p - q) + h * (p' - q') =
        (lam * h + c) * (p + q) - damping * (h * (p - q)) + fy) ↔
    (p' = (lam - damping + modal11 a b c h rate) * p + modal12 a b c h rate * q +
      (fx + fy / h) / 2 ∧
     q' = modal21 a b c h rate * p + (-lam - damping + modal22 a b c h rate) * q +
      (fx - fy / h) / 2) := by
  constructor
  · rintro ⟨hx, hy⟩
    constructor
    · calc
        p' = ((p' + q') + ((rate * h * (p - q) + h * (p' - q')) / h -
            rate * (p - q))) / 2 := by field_simp ; ring
        _ = _ := by
          rw [hx, hy]
          unfold modal11 modal12
          field_simp ; ring
    · calc
        q' = ((p' + q') - ((rate * h * (p - q) + h * (p' - q')) / h -
            rate * (p - q))) / 2 := by field_simp ; ring
        _ = _ := by
          rw [hx, hy]
          unfold modal21 modal22
          field_simp ; ring
  · rintro ⟨rfl, rfl⟩
    constructor
    · unfold modal11 modal12 modal21 modal22
      field_simp ; ring
    · unfold modal11 modal12 modal21 modal22
      field_simp ; ring

noncomputable def pairCLM : (ℝ × ℝ) →L[ℝ] Plane :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => !₂[z.1, z.2]
    map_add' := by intro u v; ext i; fin_cases i <;> simp
    map_smul' := by intro c u; ext i; fin_cases i <;> simp }


theorem abs_four_sum_div_two_le {a b c d A B C D : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) (hd : |d| ≤ D) :
    |(a + b + c + d) / 2| ≤ A + B + C + D := by
  calc
    _ ≤ |a + b + c + d| := abs_div_le_of_one_le _ _ (by norm_num)
    _ ≤ |a + b + c| + |d| := abs_add_le _ _
    _ ≤ (|a + b| + |c|) + |d| := add_le_add_left (abs_add_le _ _) _
    _ ≤ ((|a| + |b|) + |c|) + |d| := add_le_add_left (add_le_add_left (abs_add_le _ _) _) _
    _ ≤ A + B + C + D := add_le_add (add_le_add (add_le_add ha hb) hc) hd

/-- All four modal errors are bounded explicitly.  `rate = h'/h` is the
extra error arising from the time-dependent eigenbasis. -/
theorem modal_errors_le {a b c h rate H δ κ : ℝ}
    (hH : 0 ≤ H)
    (ha : |a| ≤ δ) (hb : |b| ≤ δ) (hc : |c| ≤ δ)
    (hh : |h| ≤ H) (hhi : |1 / h| ≤ H) (hrate : |rate| ≤ κ) :
    |modal11 a b c h rate| ≤ (1 + 2 * H) * δ + κ ∧
    |modal12 a b c h rate| ≤ (1 + 2 * H) * δ + κ ∧
    |modal21 a b c h rate| ≤ (1 + 2 * H) * δ + κ ∧
    |modal22 a b c h rate| ≤ (1 + 2 * H) * δ + κ := by
  have hhb : |h * b| ≤ H * δ := by rw [abs_mul]; exact mul_le_mul hh hb (abs_nonneg _) hH
  have hch : |c / h| ≤ H * δ := by
    calc
      |c / h| = |1 / h| * |c| := by rw [abs_div, abs_div, abs_one]; ring
      _ ≤ H * δ := mul_le_mul hhi hc (abs_nonneg _) hH
  have hsum : δ + H * δ + H * δ + κ = (1 + 2 * H) * δ + κ := by ring
  have hneg (x A : ℝ) (h : |x| ≤ A) : |-x| ≤ A := by simpa only [abs_neg] using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [modal11, sub_eq_add_neg, hsum] using abs_four_sum_div_two_le ha hhb hch (hneg _ _ hrate)
  · simpa only [modal12, sub_eq_add_neg, hsum] using abs_four_sum_div_two_le ha (hneg _ _ hhb) hch hrate
  · simpa only [modal21, sub_eq_add_neg, hsum] using abs_four_sum_div_two_le ha hhb (hneg _ _ hch) hrate
  · simpa only [modal22, sub_eq_add_neg, hsum] using
      abs_four_sum_div_two_le ha (hneg _ _ hhb) (hneg _ _ hch) (hneg _ _ hrate)


theorem modalOperator_eq_coefficient (lam damping e11 e12 e21 e22 : ℝ) :
    GrowingMode.modalOperator lam damping e11 e12 e21 e22 =
      ViscousPropagator.coefficient lam damping
        (GrowingMode.modalOperator 0 0 e11 e12 e21 e22) := by
  ext z i
  fin_cases i <;> simp [GrowingMode.modalOperator, ViscousPropagator.coefficient,
    ViscousPropagator.diagonal, ViscousPropagator.reflection] <;> ring

theorem plane_norm_le_coordinate_sum (z : Plane) : ‖z‖ ≤ |z 0| + |z 1| := by
  have h := ViscousPropagator.plane_norm_sq z
  nlinarith only [h, norm_nonneg z, sq_abs (z 0), sq_abs (z 1), abs_nonneg (z 0),
    abs_nonneg (z 1), mul_nonneg (abs_nonneg (z 0)) (abs_nonneg (z 1))]

/-- Entrywise control gives a genuine Euclidean operator norm estimate.
The harmless factor four avoids any choice of an equivalent matrix norm. -/
theorem modal_error_opNorm_le {e11 e12 e21 e22 ε : ℝ}
    (he11 : |e11| ≤ ε) (he12 : |e12| ≤ ε) (he21 : |e21| ≤ ε) (he22 : |e22| ≤ ε) :
    ‖GrowingMode.modalOperator 0 0 e11 e12 e21 e22‖ ≤ 4 * ε := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans he11
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hε)
  intro z
  have hz (i : Fin 2) : |z i| ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i
  have hrow {a b : ℝ} (ha : |a| ≤ ε) (hb : |b| ≤ ε) :
      |a * z 0 + b * z 1| ≤ 2 * ε * ‖z‖ := by
    calc
      _ ≤ |a * z 0| + |b * z 1| := abs_add_le _ _
      _ = |a| * |z 0| + |b| * |z 1| := by rw [abs_mul, abs_mul]
      _ ≤ ε * ‖z‖ + ε * ‖z‖ := add_le_add
        (mul_le_mul ha (hz 0) (abs_nonneg _) hε)
        (mul_le_mul hb (hz 1) (abs_nonneg _) hε)
      _ = _ := by ring
  calc
    _ ≤ |(GrowingMode.modalOperator 0 0 e11 e12 e21 e22 z) 0| +
        |(GrowingMode.modalOperator 0 0 e11 e12 e21 e22 z) 1| := plane_norm_le_coordinate_sum _
    _ = |e11 * z 0 + e12 * z 1| + |e21 * z 0 + e22 * z 1| := by simp
    _ ≤ 2 * ε * ‖z‖ + 2 * ε * ‖z‖ := add_le_add (hrow he11 he12) (hrow he21 he22)
    _ = _ := by ring

/-- This is the exact quadratic-form hypothesis accepted by the weighted
propagator and parameter-jet estimates.  Scalar viscosity keeps its sign. -/
theorem modal_energy_le {lam e11 e12 e21 e22 ε : ℝ} (hlam : 0 ≤ lam) (damping : ℝ)
    (he11 : |e11| ≤ ε) (he12 : |e12| ≤ ε) (he21 : |e21| ≤ ε) (he22 : |e22| ≤ ε)
    (z : Plane) :
    ⟪z, GrowingMode.modalOperator lam damping e11 e12 e21 e22 z⟫_ℝ ≤
      (lam - damping + 4 * ε) * ‖z‖ ^ 2 := by
  rw [modalOperator_eq_coefficient]
  exact (ViscousPropagator.coefficient_energy_le hlam damping _ z).trans
    (mul_le_mul_of_nonneg_right
      (add_le_add_right (modal_error_opNorm_le he11 he12 he21 he22) _) (sq_nonneg _))

end NavierStokes.MovingFrameODE

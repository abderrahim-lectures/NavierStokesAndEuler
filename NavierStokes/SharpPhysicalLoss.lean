import NavierStokes.PhysicalGraphBounds
import NavierStokes.SharpPhaseJetAlgebra


/-! Merged from `NavierStokes.SharpLogWeights`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
/-! Merged from `NavierStokes.SharpPhysicalPhase` (in a section, so its `open`s cannot leak). -/
section
/-! Merged from `NavierStokes.SharpGraphBounds` (in a section, so its `open`s cannot leak). -/
section
/-!
# Linear derivative loss for the physical graph

The normalized radial coefficient costs only `Q^(-h κ)`, while a transverse
derivative costs `Q^(-1/2)`. Every positive order `k` of the actual physical
lift therefore costs at most `Q^(-k(1+h))`. Keeping the order in this bound
gives the manuscript's linear, rather than quadratic, graph restriction loss.
-/

noncomputable section

namespace NavierStokes.SharpGraphBounds

open Set Function
open ProblemStatement PhysicalGraphBounds
open scoped ContDiff Topology

private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

theorem native_time_power_le {h : ℝ} (hh : 0 ≤ h)
    {n : ℕ} (hn : 4 ≤ n) :
    ChartScales.Tg ^ ChartScales.nativeIndex h n ≤
      ChartScales.Q n ^ (-(1 + h)) := by
  calc
    _ ≤ ChartScales.Q n ^ (-1 - h) / ChartScales.S n :=
      (ChartScales.native_power_bounds h hh hn).1
    _ ≤ ChartScales.Q n ^ (-1 - h) := div_le_self
      (Real.rpow_nonneg (ChartScales.Q_pos n).le _) (S_ge_one (by omega))
    _ = _ := by congr 1; ring

theorem native_radial_power_le {h : ℝ} (hh : 0 ≤ h)
    {n : ℕ} (hn : 4 ≤ n) :
    ChartScales.radialCoefficient h n ≤ ChartScales.Q n ^ (-h * ChartScales.kappa) := by
  have hs : ChartScales.S n ^ (-ChartScales.rho) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (S_ge_one (by omega))
      (neg_nonpos.mpr ChartScales.rho_pos.le)
  calc
    _ ≤ ChartScales.epsilon h n ^ (-ChartScales.kappa) *
        ChartScales.S n ^ (-ChartScales.rho) :=
      (ChartScales.radialCoefficient_bounds h hh hn).2
    _ ≤ ChartScales.epsilon h n ^ (-ChartScales.kappa) :=
      mul_le_of_le_one_right (Real.rpow_nonneg (ChartScales.epsilon_pos h n).le _) hs
    _ = _ := by
      unfold ChartScales.epsilon
      rw [← Real.rpow_mul (ChartScales.Q_pos n).le]
      congr 1
      ring

theorem nativeGraph_positive_jet_bound {h a b : ℝ} (hh : 0 ≤ h) (ha : 0 < a)
    (m : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ p : SpaceTime,
      scaledRadial n p ∈ annulus a b → |p.1| ≤ 1 → ∀ k, 1 ≤ k → k ≤ m →
      ‖iteratedFDeriv ℝ k (nativeGraph h n) p‖ ≤
        C * ChartScales.Q n ^ (-(k : ℝ) * (1 + h)) := by
  obtain ⟨C, hC, hbound⟩ := compact_jet_bound axisFree_open
    (contDiffOn_radialProfile (ChartScales.radialExponent h)) (isCompact_annulus a b)
    (annulus_axisFree ha) m
  refine ⟨C + ‖timeDirection‖, by linarith [norm_nonneg timeDirection], ?_⟩
  intro n hn p hp ht k hk hkm
  have hq := ChartScales.Q_pos n
  have hq1 := ChartScales.Q_le_one n
  have hC0 : 0 ≤ C := by linarith
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have haxis := annulus_axisFree ha hp
  have hr : ContDiffAt ℝ k
      (radialProfile (ChartScales.radialExponent h) ∘ scaledRadial n) p :=
    (((contDiffOn_radialProfile (ChartScales.radialExponent h)).contDiffAt
      (axisFree_open.mem_nhds haxis)).comp p (scaledRadial n).contDiff.contDiffAt).of_le
        (nat_le_infty k)
  have he : nativeGraph h n = fun z =>
      ChartScales.radialCoefficient h n •
        (radialProfile (ChartScales.radialExponent h) ∘ scaledRadial n) z +
      ChartScales.Tg ^ ChartScales.nativeIndex h n • timeProfile z := by
    funext z
    exact nativeGraph_normalized h n z
  rw [he, fun_iteratedFDeriv_add_apply (hr.const_smul _)
    ((timeProfile.contDiff.contDiffAt (x := p)).const_smul _),
    iteratedFDeriv_const_smul_apply' hr,
    iteratedFDeriv_const_smul_apply' timeProfile.contDiff.contDiffAt]
  apply (norm_add_le _ _).trans
  have hrad : ‖ChartScales.radialCoefficient h n •
      iteratedFDeriv ℝ k (radialProfile (ChartScales.radialExponent h) ∘ scaledRadial n) p‖ ≤
      C * ChartScales.Q n ^ (-(k : ℝ) * (1 + h)) := by
    rw [norm_smul, Real.norm_of_nonneg (ChartScales.radialCoefficient_pos h n).le]
    have hj := norm_jet_comp_linear axisFree_open
      (contDiffOn_radialProfile (ChartScales.radialExponent h)) (scaledRadial n) haxis k
    have hl := pow_le_pow_left₀ (norm_nonneg (scaledRadial n)) (norm_scaledRadial_le n) k
    have hfull := mul_le_mul_of_nonneg_left
      (hj.trans (mul_le_mul (hbound k hkm _ hp) hl (by positivity) hC0))
      (ChartScales.radialCoefficient_pos h n).le
    have hprod := hfull.trans (mul_le_mul_of_nonneg_right
      (native_radial_power_le hh hn) (by positivity))
    have hpow : ChartScales.Q n ^ (-h * ChartScales.kappa) *
        (C * (ChartScales.Q n ^ (-(1 / 2 : ℝ))) ^ k) =
        C * ChartScales.Q n ^ (-h * ChartScales.kappa - (k : ℝ) / 2) := by
      rw [← Real.rpow_mul_natCast hq.le, mul_left_comm, ← Real.rpow_add hq]
      congr 2
      ring
    rw [hpow] at hprod
    apply hprod.trans
    apply mul_le_mul_of_nonneg_left _ hC0
    apply Real.rpow_le_rpow_of_exponent_ge hq hq1
    have hkh : h ≤ (k : ℝ) * h := by nlinarith
    unfold ChartScales.kappa
    nlinarith
  have htime : ‖ChartScales.Tg ^ ChartScales.nativeIndex h n •
      iteratedFDeriv ℝ k timeProfile p‖ ≤
      ‖timeDirection‖ * ChartScales.Q n ^ (-(k : ℝ) * (1 + h)) := by
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg ChartScales.Tg_pos.le _)]
    calc
      _ ≤ ChartScales.Q n ^ (-(1 + h)) * ‖timeDirection‖ :=
        mul_le_mul (native_time_power_le hh hn) (timeProfile_jet_bound p ht k)
          (norm_nonneg _) (Real.rpow_nonneg hq.le _)
      _ ≤ ChartScales.Q n ^ (-(k : ℝ) * (1 + h)) * ‖timeDirection‖ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hq hq1 (by
          nlinarith)) (norm_nonneg _)
      _ = _ := mul_comm _ _
  calc
    _ ≤ C * ChartScales.Q n ^ (-(k : ℝ) * (1 + h)) +
        ‖timeDirection‖ * ChartScales.Q n ^ (-(k : ℝ) * (1 + h)) := add_le_add hrad htime
    _ = _ := by ring

theorem physicalLift_positive_jet_bound {h a b : ℝ} (hh : 0 ≤ h) (ha : 0 < a)
    (m : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ p : SpaceTime,
      scaledRadial n p ∈ annulus a b → |p.1| ≤ 1 → ∀ k, 1 ≤ k → k ≤ m →
      ‖iteratedFDeriv ℝ k (physicalLift h n) p‖ ≤
        C * ChartScales.Q n ^ (-(k : ℝ) * (1 + h)) := by
  obtain ⟨C, hC, hbound⟩ := nativeGraph_positive_jet_bound hh ha m
  refine ⟨C, hC, ?_⟩
  intro n hn p hp ht k hk hkm
  have haxis := scaledRadial_ne_zero (annulus_axisFree ha hp)
  change ‖iteratedFDeriv ℝ k (fun z => (physicalChart h n z, nativeGraph h n z)) p‖ ≤ _
  rw [iteratedFDeriv_pair
    ((physicalChart_smooth h n).contDiffAt.of_le (nat_le_infty k))
    ((contDiffAt_nativeGraph h n haxis).of_le (nat_le_infty k)),
    ContinuousMultilinearMap.opNorm_prod]
  apply max_le
  · calc
      _ ≤ ChartScales.Q n ^ (-1 : ℝ) := physicalChart_jet_bound hh n p hk
      _ ≤ ChartScales.Q n ^ (-(k : ℝ) * (1 + h)) :=
        Real.rpow_le_rpow_of_exponent_ge (ChartScales.Q_pos n) (ChartScales.Q_le_one n) (by
          have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
          nlinarith)
      _ ≤ C * ChartScales.Q n ^ (-(k : ℝ) * (1 + h)) :=
        le_mul_of_one_le_left (Real.rpow_nonneg (ChartScales.Q_pos n).le _) hC
  · exact hbound n hn p hp ht k hk hkm

theorem graphRestriction_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h a b : ℝ} (hh : 0 ≤ h) (ha : 0 < a) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 4 ≤ n → ∀ p : SpaceTime,
      scaledRadial n p ∈ annulus a b → |p.1| ≤ 1 →
      ∀ F : LiftPoint → E, ContDiff ℝ ∞ F → ∀ B : ℝ, 0 ≤ B →
      (∀ k ≤ m, ‖iteratedFDeriv ℝ k F (physicalLift h n p)‖ ≤ B) →
      ‖iteratedFDeriv ℝ m (F ∘ physicalLift h n) p‖ ≤
        C * B * ChartScales.Q n ^ (-(m : ℝ) * (1 + h)) := by
  obtain ⟨C, hC, hbound⟩ := physicalLift_positive_jet_bound hh ha m
  refine ⟨(m.factorial : ℝ) * C ^ m, mul_pos (by positivity) (pow_pos (by linarith) _), ?_⟩
  intro n hn p hp ht F hF B hB hFB
  let U : Set SpaceTime := {p | radialProjection p ≠ 0}
  have hU : IsOpen U := axisFree_open.preimage radialProjection.continuous
  have hx : p ∈ U := scaledRadial_ne_zero (annulus_axisFree ha hp)
  let D := C * ChartScales.Q n ^ (-(1 + h))
  have hj := norm_iteratedFDerivWithin_comp_le hF.contDiffOn (physicalLift_smooth h n)
    (nat_le_infty m) uniqueDiffOn_univ hU.uniqueDiffOn (mapsTo_univ _ _) hx
    (C := B) (D := D)
    (fun k hk => by simpa only [iteratedFDerivWithin_univ] using hFB k hk)
    (fun k hk hkm => by
      rw [iteratedFDerivWithin_of_isOpen k hU hx]
      apply (hbound n hn p hp ht k hk hkm).trans
      dsimp [D]
      rw [mul_pow, ← Real.rpow_mul_natCast (ChartScales.Q_pos n).le]
      have he : -(1 + h) * (k : ℝ) = -(k : ℝ) * (1 + h) := by ring
      rw [he]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (ChartScales.Q_pos n).le _)
      simpa only [pow_one] using (pow_le_pow_right₀ hC hk))
  rw [iteratedFDerivWithin_of_isOpen m hU hx] at hj
  apply hj.trans_eq
  dsimp [D]
  rw [mul_pow, ← Real.rpow_mul_natCast (ChartScales.Q_pos n).le]
  have he : -(1 + h) * (m : ℝ) = -(m : ℝ) * (1 + h) := by ring
  rw [he]
  ring

end NavierStokes.SharpGraphBounds
end

noncomputable section
namespace NavierStokes.SharpPhysicalPhase
open Set Function
open ProblemStatement PhysicalGraphBounds SharpPhaseJetAlgebra
open scoped ContDiff

private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

noncomputable def polarMap (κ : Plane → Plane) (n : ℕ) : SpaceTime → Plane :=
  κ ∘ scaledRadial n

noncomputable def slowMap (κ : Plane → Plane) (h : ℝ) (n : ℕ) (w : SpaceTime) : Slow :=
  ((polarMap κ n w).1, liftZT (physicalLift h n w))

theorem slowMap_formula (κ : Plane → Plane) (h : ℝ) (n : ℕ) (w : SpaceTime) :
    slowMap κ h n w = ((κ (scaledRadial n w)).1,
      (ChartScales.Q n ^ (-CoordinateAlgebra.D h) * w.2 2, (1-w.1)/ChartScales.Q n)) := by
  ext <;> simp [slowMap, polarMap, liftZT, physicalLift, physicalChart,
    chartLinear_apply, Real.rpow_neg_one, div_eq_mul_inv]
  ring

theorem slowMap_eq_slot (κ : Plane → Plane) (h : ℝ) (n : ℕ)
    (center : Plane) (r0 : ℝ) (w : SpaceTime) :
    slowMap κ h n w =
      (slotMap κ (ChartScales.timeCoefficient h n) center r0 (physicalLift h n w)).1 := by
  rw [slotMap_physical, slowMap_formula]

theorem polarMap_smooth {κ : Plane → Plane} (hκ : ContDiff ℝ ∞ κ) (n : ℕ) :
    ContDiff ℝ ∞ (polarMap κ n) := hκ.comp (scaledRadial n).contDiff

theorem slowMap_smooth {κ : Plane → Plane} (hκ : ContDiff ℝ ∞ κ) (h : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (slowMap κ h n) := by
  have he : slowMap κ h n = fun w => ((κ (scaledRadial n w)).1,
      ((physicalChart h n w).2.2.2, (physicalChart h n w).1)) := rfl
  rw [he]
  exact (hκ.comp (scaledRadial n).contDiff).fst.prodMk
    ((physicalChart_smooth h n).snd.snd.snd.prodMk (physicalChart_smooth h n).fst)

theorem slotTime_smooth (h : ℝ) (n : ℕ) (center : Plane) (r0 : ℝ) :
    ContDiff ℝ ∞ (slotTime h n center r0) := by
  have he : slotTime h n center r0 = fun w : SpaceTime =>
      ChartScales.Q n ^ (-1-h) * w.1 +
        (r0-etaCoordinate center)/ChartScales.timeCoefficient h n := by
    funext w
    exact slotTime_affine h n center r0 w
  rw [he]
  exact (contDiff_const.mul contDiff_fst).add contDiff_const

/-- The axial factor `epsilon⁻¹` cancels the axial chart scaling exactly. -/
theorem axial_scale (h : ℝ) (n : ℕ) :
    (ChartScales.epsilon h n)⁻¹ * ChartScales.Q n ^ (-CoordinateAlgebra.D h) =
      ChartScales.Q n ^ (-(1/2 : ℝ)) := by
  rw [ChartScales.epsilon, ← Real.rpow_neg (ChartScales.Q_pos n).le,
    ← Real.rpow_add (ChartScales.Q_pos n)]
  congr 1
  unfold CoordinateAlgebra.D
  ring

theorem phase_formula (κ : Plane → Plane) (h : ℝ) (n : ℕ)
    (center : Plane) (r0 p pz x0 : ℝ) (F G : Slow → ℝ) (w : SpaceTime) :
    liftedPhase κ h n center r0 p pz x0 F G (physicalLift h n w) =
      p * (polarMap κ n w).2 + pz * ChartScales.Q n ^ (-(1/2 : ℝ)) * w.2 2 +
        x0 * (polarMap κ n w).1 -
      slotTime h n center r0 w * (p * F (slowMap κ h n w) + pz * G (slowMap κ h n w)) := by
  unfold liftedPhase
  rw [comp_apply, PhaseCalculus.phase, slotMap_physical, slowMap_formula]
  simp only [polarMap, comp_apply]
  rw [div_eq_mul_inv]
  have he := axial_scale h n
  rw [show pz * (ChartScales.epsilon h n)⁻¹ * (ChartScales.Q n ^ (-CoordinateAlgebra.D h) * w.2 2) =
      pz * ((ChartScales.epsilon h n)⁻¹ * ChartScales.Q n ^ (-CoordinateAlgebra.D h)) * w.2 2 by ring, he]

private theorem pow_scale {h : ℝ} (hh : 0 ≤ h) (n k : ℕ) :
    (ChartScales.Q n ^ (-(1 / 2 : ℝ))) ^ k ≤
      (ChartScales.Q n ^ (-(1 + h))) ^ k := by
  apply pow_le_pow_left₀ (Real.rpow_nonneg (ChartScales.Q_pos n).le _)
  exact Real.rpow_le_rpow_of_exponent_ge (ChartScales.Q_pos n) (ChartScales.Q_le_one n)
    (by linarith)

private theorem scale_one {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    1 ≤ ChartScales.Q n ^ (-(1+h)) := by
  have he := Real.rpow_le_rpow_of_exponent_ge (ChartScales.Q_pos n)
    (ChartScales.Q_le_one n) (show -(1+h) ≤ 0 by linarith)
  simpa only [Real.rpow_zero] using he

theorem polarMap_jets {κ : Plane → Plane} (hκ : ContDiff ℝ ∞ κ)
    {h K : ℝ} (hh : 0 ≤ h) (hK : 0 ≤ K) (n m : ℕ) (w : SpaceTime)
    (hκb : ∀ k ≤ m, ‖iteratedFDeriv ℝ k κ (scaledRadial n w)‖ ≤ K) :
    ∀ k ≤ m, ‖iteratedFDeriv ℝ k (polarMap κ n) w‖ ≤
      K * (ChartScales.Q n ^ (-(1+h))) ^ k := by
  intro k hk
  apply (norm_jet_comp_linear isOpen_univ hκ.contDiffOn (scaledRadial n)
    (mem_univ _) k).trans
  apply mul_le_mul (hκb k hk) _ (by positivity) hK
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_scaledRadial_le n) k).trans (pow_scale hh n k)

theorem slowMap_positive_jets {κ : Plane → Plane} (hκ : ContDiff ℝ ∞ κ)
    {h K : ℝ} (hh : 0 ≤ h) (hK : 1 ≤ K) (n m : ℕ) (w : SpaceTime)
    (hκb : ∀ k ≤ m, ‖iteratedFDeriv ℝ k κ (scaledRadial n w)‖ ≤ K) :
    ∀ k, 1 ≤ k → k ≤ m → ‖iteratedFDeriv ℝ k (slowMap κ h n) w‖ ≤
      (K * ChartScales.Q n ^ (-(1+h))) ^ k := by
  intro k hk hkm
  have hQ := ChartScales.Q_pos n
  have hK0 : 0 ≤ K := by linarith
  have hp := polarMap_jets hκ hh (by linarith : 0 ≤ K) n m w hκb k hkm
  have hpolar := norm_jet_linear_comp (polarMap_smooth hκ n)
    (ContinuousLinearMap.fst ℝ ℝ ℝ) w k
  have hp' : ‖iteratedFDeriv ℝ k (fun z => (polarMap κ n z).1) w‖ ≤
      K * (ChartScales.Q n ^ (-(1+h))) ^ k := by
    exact hpolar.trans ((mul_le_mul (norm_fstCLM_le ℝ ℝ) hp (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hzt : ‖iteratedFDeriv ℝ k (fun z : SpaceTime =>
      ((physicalChart h n z).2.2.2, (physicalChart h n z).1)) w‖ ≤
      ChartScales.Q n ^ (-1 : ℝ) := by
    let L : ChartPoint →L[ℝ] Plane :=
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        ((ContinuousLinearMap.snd ℝ ℝ Plane).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × Plane)))).prod
        (ContinuousLinearMap.fst ℝ ℝ (ℝ × Plane))
    have hL : ‖L‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
      intro x
      change max ‖x.2.2.2‖ ‖x.1‖ ≤ 1 * ‖x‖
      rw [one_mul]
      exact max_le ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
        (le_max_left _ _)
    exact (norm_jet_linear_comp (physicalChart_smooth h n) L w k).trans
      ((mul_le_mul hL (physicalChart_jet_bound hh n w hk) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  change ‖iteratedFDeriv ℝ k (fun z => ((polarMap κ n z).1,
    ((physicalChart h n z).2.2.2, (physicalChart h n z).1))) w‖ ≤ _
  rw [iteratedFDeriv_pair
    (((polarMap_smooth hκ n).fst.contDiffAt).of_le (nat_le_infty k))
    ((((physicalChart_smooth h n).snd.snd.snd.prodMk
      (physicalChart_smooth h n).fst).contDiffAt).of_le (nat_le_infty k)),
    ContinuousMultilinearMap.opNorm_prod, mul_pow]
  apply max_le
  · apply hp'.trans
    exact mul_le_mul_of_nonneg_right (by simpa only [pow_one] using pow_le_pow_right₀ hK hk)
      (by positivity)
  · apply hzt.trans
    have h1 : ChartScales.Q n ^ (-1 : ℝ) ≤ ChartScales.Q n ^ (-(1+h)) :=
      Real.rpow_le_rpow_of_exponent_ge (ChartScales.Q_pos n) (ChartScales.Q_le_one n) (by linarith)
    apply (h1.trans (by simpa only [pow_one] using pow_le_pow_right₀ (scale_one hh n) hk)).trans
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hK)



private theorem norm_jet_add_le {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f g : E → V}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z => f z + g z) w‖ ≤
      ‖iteratedFDeriv ℝ k f w‖ + ‖iteratedFDeriv ℝ k g w‖ := by
  rw [fun_iteratedFDeriv_add_apply (hf.contDiffAt.of_le (nat_le_infty k))
    (hg.contDiffAt.of_le (nat_le_infty k))]
  exact norm_add_le _ _

private theorem norm_jet_sub_le {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f g : E → V}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z => f z - g z) w‖ ≤
      ‖iteratedFDeriv ℝ k f w‖ + ‖iteratedFDeriv ℝ k g w‖ := by
  rw [fun_iteratedFDeriv_sub_apply (hf.contDiffAt.of_le (nat_le_infty k))
    (hg.contDiffAt.of_le (nat_le_infty k))]
  exact norm_sub_le _ _

theorem slotTime_jets {h K V : ℝ} (hh : 0 ≤ h) (hK : 1 ≤ K) (hV : 1 ≤ V)
    (n : ℕ) (center : Plane) (r0 : ℝ) (w : SpaceTime)
    (hv : |slotTime h n center r0 w| ≤ V) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (slotTime h n center r0) w‖ ≤
      V * (K * ChartScales.Q n ^ (-(1+h))) ^ k := by
  have hQ := ChartScales.Q_pos n
  have hU : 1 ≤ K * ChartScales.Q n ^ (-(1+h)) := one_le_mul_of_one_le_of_one_le hK (scale_one hh n)
  cases k with
  | zero => simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, mul_one] using hv
  | succ k =>
    let L := ChartScales.Q n ^ (-(1+h)) • ContinuousLinearMap.fst ℝ ℝ Space
    have he : slotTime h n center r0 = fun w => L w +
        (r0-etaCoordinate center)/ChartScales.timeCoefficient h n := by
      funext w
      rw [slotTime_affine]
      dsimp [L]
      rw [show -1-h = -(1+h) by ring]
      rfl
    have hL : ‖L‖ ≤ ChartScales.Q n ^ (-(1+h)) := by
      dsimp [L]
      rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hQ.le _)]
      exact mul_le_of_le_one_right (Real.rpow_nonneg hQ.le _) (norm_fstCLM_le _ _)
    rw [he]
    apply ((positive_jet_affine_bound L _ w (by omega)).trans hL).trans
    apply (le_mul_of_one_le_left (Real.rpow_nonneg hQ.le _) hK).trans
    apply (show K * ChartScales.Q n ^ (-(1+h)) ≤
        (K * ChartScales.Q n ^ (-(1+h))) ^ (k+1) from by
      simpa only [pow_one] using pow_le_pow_right₀ hU (show 1 ≤ k+1 by omega)).trans
    exact le_mul_of_one_le_left (by positivity) hV

/-- A sharp bound on the actual phase after graph restriction. The pulse
coordinate is differentiated as its exact affine physical function. -/
theorem physicalPhase_positive_jets {κ : Plane → Plane} (hκ : ContDiff ℝ ∞ κ)
    {h K V B : ℝ} (hh : 0 ≤ h) (hK : 1 ≤ K) (hV : 1 ≤ V) (hB : 0 ≤ B)
    (n m : ℕ) (center : Plane) (r0 p pz x0 : ℝ) {F G : Slow → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (w : SpaceTime)
    (hκb : ∀ k ≤ m, ‖iteratedFDeriv ℝ k κ (scaledRadial n w)‖ ≤ K)
    (hv : |slotTime h n center r0 w| ≤ V)
    (hFb : ∀ k ≤ m, ‖iteratedFDeriv ℝ k F (slowMap κ h n w)‖ ≤ B)
    (hGb : ∀ k ≤ m, ‖iteratedFDeriv ℝ k G (slowMap κ h n w)‖ ≤ B) :
    ∀ k, 1 ≤ k → k ≤ m →
      ‖iteratedFDeriv ℝ k
        (liftedPhase κ h n center r0 p pz x0 F G ∘ physicalLift h n) w‖ ≤
      ((|p|+|x0|)*K + |pz| + (2:ℝ)^m * V * ((|p|+|pz|)*(m.factorial:ℝ)*B)) *
        (K * ChartScales.Q n ^ (-(1+h))) ^ k := by
  let U := K * ChartScales.Q n ^ (-(1+h))
  have hQ := ChartScales.Q_pos n
  have hK0 : 0 ≤ K := by linarith
  have hU : 1 ≤ U := one_le_mul_of_one_le_of_one_le hK (scale_one hh n)
  have hUs : 0 ≤ U := by linarith
  have hslow := slowMap_smooth hκ h n
  have hf := hF.comp hslow
  have hg := hG.comp hslow
  have hpos := slowMap_positive_jets hκ hh hK n m w hκb
  have hfj := composition_geometric hslow hF w m hB hUs hFb hpos
  have hgj := composition_geometric hslow hG w m hB hUs hGb hpos
  let base : SpaceTime → ℝ := fun z => p * F (slowMap κ h n z) + pz * G (slowMap κ h n z)
  have hbase : ContDiff ℝ ∞ base := (contDiff_const.mul hf).add (contDiff_const.mul hg)
  have hbasej : ∀ k ≤ m, ‖iteratedFDeriv ℝ k base w‖ ≤
      ((|p|+|pz|)*(m.factorial:ℝ)*B) * U ^ k := by
    intro k hk
    apply (norm_jet_add_le (contDiff_const.mul hf) (contDiff_const.mul hg) w k).trans
    rw [norm_jet_const_mul hf w p k, norm_jet_const_mul hg w pz k]
    calc
      _ ≤ |p| * ((m.factorial:ℝ)*B*U^k) + |pz| * ((m.factorial:ℝ)*B*U^k) :=
        add_le_add (mul_le_mul_of_nonneg_left (hfj k hk) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (hgj k hk) (abs_nonneg _))
      _ = _ := by ring
  have hpolar := polarMap_smooth hκ n
  have hpj := polarMap_jets hκ hh hK0 n m w hκb
  have hproj (L : Plane →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (k : ℕ) (hk : k ≤ m) :
      ‖iteratedFDeriv ℝ k (L ∘ polarMap κ n) w‖ ≤ K * U ^ k := by
    apply (norm_jet_linear_comp hpolar L w k).trans
    apply ((mul_le_mul hL (hpj k hk) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)).trans
    apply mul_le_mul_of_nonneg_left _ hK0
    exact pow_le_pow_left₀ (Real.rpow_nonneg hQ.le _)
      (le_mul_of_one_le_left (Real.rpow_nonneg hQ.le _) hK) k
  let polar : SpaceTime → ℝ := fun z => p*(polarMap κ n z).2+x0*(polarMap κ n z).1
  have hpol : ContDiff ℝ ∞ polar := (contDiff_const.mul hpolar.snd).add (contDiff_const.mul hpolar.fst)
  have hpolj (k : ℕ) (hk : k ≤ m) : ‖iteratedFDeriv ℝ k polar w‖ ≤
      ((|p|+|x0|)*K)*U^k := by
    apply (norm_jet_add_le (contDiff_const.mul hpolar.snd) (contDiff_const.mul hpolar.fst) w k).trans
    rw [norm_jet_const_mul hpolar.snd w p k, norm_jet_const_mul hpolar.fst w x0 k]
    calc
      _ ≤ |p| * (K*U^k)+|x0| * (K*U^k) := add_le_add
        (mul_le_mul_of_nonneg_left (hproj _ (norm_sndCLM_le _ _) k hk) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hproj _ (norm_fstCLM_le _ _) k hk) (abs_nonneg _))
      _ = _ := by ring
  let ax : SpaceTime → ℝ := fun z => pz * ChartScales.Q n ^ (-(1/2:ℝ)) * z.2 2
  have hax : ContDiff ℝ ∞ ax := contDiff_const.mul (coordinateProjection 2).contDiff
  have haxj (k : ℕ) (hk : 1 ≤ k) : ‖iteratedFDeriv ℝ k ax w‖ ≤ |pz| * U^k := by
    change ‖iteratedFDeriv ℝ k (fun z => (pz * ChartScales.Q n ^ (-(1/2:ℝ))) * coordinateProjection 2 z) w‖ ≤ _
    rw [norm_jet_const_mul (coordinateProjection 2).contDiff w _ k, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hQ _)]
    have hc : ‖coordinateProjection 2‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
      intro z
      exact (PiLp.norm_apply_le z.2 2).trans (by simpa only [one_mul, Prod.norm_def] using le_max_right ‖z.1‖ ‖z.2‖)
    have hqscale : ChartScales.Q n ^ (-(1/2:ℝ)) ≤ U :=
      (Real.rpow_le_rpow_of_exponent_ge hQ (ChartScales.Q_le_one n) (by linarith)).trans
        (le_mul_of_one_le_left (Real.rpow_nonneg hQ.le _) hK)
    have hqpow : ChartScales.Q n ^ (-(1/2:ℝ)) ≤ U^k :=
      hqscale.trans (by simpa only [pow_one] using pow_le_pow_right₀ hU hk)
    exact ((mul_le_mul_of_nonneg_left ((norm_positive_jet_linear_le (coordinateProjection 2) w hk).trans hc)
      (by positivity)).trans_eq (mul_one _)).trans
      (mul_le_mul_of_nonneg_left hqpow (abs_nonneg _))
  have he : liftedPhase κ h n center r0 p pz x0 F G ∘ physicalLift h n =
      fun z => polar z + ax z - slotTime h n center r0 z * base z := by
    funext z
    rw [comp_apply, phase_formula]
    dsimp [polar, ax, base]
    ring
  intro k hk hkm
  rw [he]
  apply (norm_jet_sub_le (hpol.add hax) ((slotTime_smooth h n center r0).mul hbase) w k).trans
  have ht := product_geometric (slotTime_smooth h n center r0) hbase w k
    (show 0 ≤ V by linarith) (show 0 ≤ (|p|+|pz|)*(m.factorial:ℝ)*B by positivity) hUs
    (fun i _ => slotTime_jets hh hK hV n center r0 w hv i)
    (fun i hi => hbasej i (hi.trans hkm))
  have ht' := ht.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hkm) (show 0≤V by linarith))
      (show 0 ≤ (|p|+|pz|)*(m.factorial:ℝ)*B by positivity)) (pow_nonneg hUs _))
  apply (add_le_add ((norm_jet_add_le hpol hax w k).trans
    (add_le_add (hpolj k hkm) (haxj k hk))) ht').trans_eq
  dsimp [U]
  ring



theorem physicalPhase_smooth {κ : Plane → Plane} (hκ : ContDiff ℝ ∞ κ)
    (h : ℝ) (n : ℕ) (center : Plane) (r0 p pz x0 : ℝ) {F G : Slow → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (liftedPhase κ h n center r0 p pz x0 F G ∘ physicalLift h n) := by
  have he : liftedPhase κ h n center r0 p pz x0 F G ∘ physicalLift h n =
      fun w => p * (polarMap κ n w).2 + pz * ChartScales.Q n ^ (-(1/2:ℝ)) * w.2 2 +
        x0 * (polarMap κ n w).1 -
      slotTime h n center r0 w * (p * F (slowMap κ h n w) + pz * G (slowMap κ h n w)) := by
    funext w
    exact phase_formula κ h n center r0 p pz x0 F G w
  rw [he]
  have hp := polarMap_smooth hκ n
  have hs := slowMap_smooth hκ h n
  exact (((contDiff_const.mul hp.snd).add (contDiff_const.mul (coordinateProjection 2).contDiff)).add
    (contDiff_const.mul hp.fst)).sub ((slotTime_smooth h n center r0).mul
      ((contDiff_const.mul (hF.comp hs)).add (contDiff_const.mul (hG.comp hs))))

/-- Uniform phase bounds keep all slow factors polynomial in `S`, with no
additional power loss in `Q`. -/
theorem physicalPhase_geometric_bound {h K V P B d : ℝ}
    (hh : 0 ≤ h) (hK : 1 ≤ K) (hV : 1 ≤ V) (hP : 1 ≤ P) (hB : 1 ≤ B)
    (hd : 0 ≤ d) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ κ : Plane → Plane, ContDiff ℝ ∞ κ →
      ∀ n : ℕ, 4 ≤ n → ∀ (center : Plane) (r0 p pz x0 : ℝ),
      |p| ≤ P → |pz| ≤ P → |x0| ≤ P → ∀ F G : Slow → ℝ,
      ContDiff ℝ ∞ F → ContDiff ℝ ∞ G → ∀ w : SpaceTime,
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i κ (scaledRadial n w)‖ ≤ K) →
      |slotTime h n center r0 w| ≤ V * ChartScales.S n →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i F (slowMap κ h n w)‖ ≤ B * ChartScales.S n ^ d) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i G (slowMap κ h n w)‖ ≤ B * ChartScales.S n ^ d) →
      ∀ i, 1 ≤ i → i ≤ m →
      ‖iteratedFDeriv ℝ i
        (liftedPhase κ h n center r0 p pz x0 F G ∘ physicalLift h n) w‖ ≤
        (C * ChartScales.S n ^ (d+1) * ChartScales.Q n ^ (-(1+h))) ^ i := by
  let C0 := 2*P*K+P+(2:ℝ)^m*V*(2*P*(m.factorial:ℝ)*B)+1
  have hC0 : 1 ≤ C0 := by
    have ht : 0 ≤ 2*P*K+P+(2:ℝ)^m*V*(2*P*(m.factorial:ℝ)*B) := by positivity
    dsimp [C0]
    linarith
  refine ⟨C0*K, one_le_mul_of_one_le_of_one_le hC0 hK, ?_⟩
  intro κ hκ n hn center r0 p pz x0 hp hpz hx0 F G hF hG w hκb hv hFb hGb i hi him
  have hS := S_ge_one (show 1 ≤ n by omega)
  have hS0 := ChartScales.S_pos (show 1 ≤ n by omega)
  have hQ := ChartScales.Q_pos n
  have hSd : 1 ≤ ChartScales.S n ^ d := Real.one_le_rpow hS hd
  have hSe : ChartScales.S n ^ (d+1) = ChartScales.S n * ChartScales.S n ^ d := by
    rw [Real.rpow_add hS0, Real.rpow_one, mul_comm]
  have hE : 1 ≤ ChartScales.S n ^ (d+1) := Real.one_le_rpow hS (by linarith)
  have hVS : 1 ≤ V * ChartScales.S n := one_le_mul_of_one_le_of_one_le hV hS
  have hBS : 0 ≤ B * ChartScales.S n ^ d := by positivity
  have hbound := physicalPhase_positive_jets hκ hh hK hVS hBS n m center r0 p pz x0
    hF hG w hκb hv hFb hGb i hi him
  have hcoef : (|p|+|x0|)*K + |pz| + (2:ℝ)^m * (V*ChartScales.S n) *
      ((|p|+|pz|)*(m.factorial:ℝ)*(B*ChartScales.S n^d)) ≤ C0*ChartScales.S n^(d+1) := by
    have hP0 : 0 ≤ P := by linarith
    have hK0 : 0 ≤ K := by linarith
    have hp1 : |p|+|x0| ≤ 2*P := by linarith
    have hp2 : |p|+|pz| ≤ 2*P := by linarith
    calc
      _ ≤ (2*P)*K+P+(2:ℝ)^m*(V*ChartScales.S n)*(2*P*(m.factorial:ℝ)*(B*ChartScales.S n^d)) := by
        gcongr
      _ = (2*P*K+P)+((2:ℝ)^m*V*(2*P*(m.factorial:ℝ)*B))*ChartScales.S n^(d+1) := by
        rw [hSe]
        ring
      _ ≤ (2*P*K+P)*ChartScales.S n^(d+1)+
          ((2:ℝ)^m*V*(2*P*(m.factorial:ℝ)*B))*ChartScales.S n^(d+1) :=
        add_le_add (le_mul_of_one_le_right (show 0 ≤ 2*P*K+P by positivity) hE) le_rfl
      _ ≤ _ := by dsimp [C0]; nlinarith [Real.rpow_nonneg hS0.le (d+1)]
  have hmajor : 1 ≤ C0*ChartScales.S n^(d+1) := one_le_mul_of_one_le_of_one_le hC0 hE
  apply hbound.trans
  calc
    _ ≤ (C0*ChartScales.S n^(d+1)) * (K*ChartScales.Q n^(-(1+h)))^i :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ ≤ (C0*ChartScales.S n^(d+1))^i * (K*ChartScales.Q n^(-(1+h)))^i :=
      mul_le_mul_of_nonneg_right (by simpa only [pow_one] using pow_le_pow_right₀ hmajor hi) (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

end NavierStokes.SharpPhysicalPhase
end

/-! Merged from `NavierStokes.SharpPhysicalCarrier` (in a section, so its `open`s cannot leak). -/
section
noncomputable section
namespace NavierStokes.SharpPhysicalCarrier
open Set Function
open ProblemStatement PhysicalGraphBounds SharpPhaseJetAlgebra SharpPhysicalPhase
open scoped ContDiff

private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

/-- The manuscript's common Cartesian derivative cost for an oscillatory factor. -/
def derivativeCost (h : ℝ) : ℝ := 1 + 3*h/2

/-- The printed physical loss includes one derivative for potential recovery. -/
def physicalLoss (h : ℝ) (m : ℕ) : ℝ :=
  2*CoordinateAlgebra.A h + ((m:ℝ)+1)*derivativeCost h

/-- A real physical phase with sharp positive jets gives the exact linear
carrier loss. Slow powers remain explicit, and are not absorbed into `Q`. -/
theorem carrier_geometric_bound {h a b : ℝ} (hh : 0 ≤ h) (ha : 0 < a)
    (m : ℕ) (g d e A B H : ℝ) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (he : 0 ≤ e) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ w : SpaceTime,
      scaledRadial n w ∈ annulus a b → |w.1| ≤ 1 →
      ∀ (amp : LiftPoint → ℂ) (Φ : SpaceTime → ℝ) (j : ℤ),
      ContDiff ℝ ∞ amp → ContDiff ℝ ∞ Φ → |(j:ℝ)| ≤ H →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i amp (physicalLift h n w)‖ ≤
        A * ChartScales.Q n ^ g * ChartScales.S n ^ d) →
      (∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i Φ w‖ ≤
        (B * ChartScales.S n ^ e * ChartScales.Q n ^ (-(1+h))) ^ i) →
      ‖iteratedFDeriv ℝ m (fun z => amp (physicalLift h n z) *
        character ((ChartScales.carrier h n:ℝ)*(j:ℝ)) (Φ z)) w‖ ≤
        C * ChartScales.Q n ^ (g-(m:ℝ)*derivativeCost h) *
          ChartScales.S n ^ (d+e*(m:ℝ)) := by
  obtain ⟨K, hK, hgraph⟩ := SharpGraphBounds.physicalLift_positive_jet_bound (b := b) hh ha m
  let C := (2:ℝ)^m*(m.factorial:ℝ)^2*A*(1+2*H)^m*(K+B)^m
  have hK0 : 0 ≤ K := by linarith
  have hB0 : 0 ≤ B := by linarith
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro n hn w hw ht amp Φ j hamp hΦ hj hab hph
  have hQ := ChartScales.Q_pos n
  have hS := ChartScales.S_pos (show 1 ≤ n by omega)
  have hS1 := S_ge_one (show 1 ≤ n by omega)
  have hSe : 1 ≤ ChartScales.S n ^ e := Real.one_le_rpow hS1 he
  let U := (K+B)*ChartScales.S n^e*ChartScales.Q n^(-(1+h))
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hscale : 1 ≤ ChartScales.Q n ^ (-h/2) := by
    have hb := Real.rpow_le_rpow_of_exponent_ge hQ (ChartScales.Q_le_one n) (show -h/2 ≤ 0 by linarith)
    simpa only [Real.rpow_zero] using hb
  let M := (1+2*H)*ChartScales.Q n^(-h/2)
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le (by linarith) hscale
  have hM0 : 0 ≤ M := by linarith
  have hc : |(ChartScales.carrier h n:ℝ)*(j:ℝ)| ≤ M := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      _ ≤ (2*ChartScales.Q n^(-h/2))*H :=
        mul_le_mul (carrier_upper hh n) hj (abs_nonneg _) (by positivity)
      _ ≤ M := by dsimp [M]; nlinarith [Real.rpow_nonneg hQ.le (-h/2)]
  let W : Set SpaceTime := {z | radialProjection z ≠ 0}
  have hW : IsOpen W := axisFree_open.preimage radialProjection.continuous
  have hwW : w ∈ W := scaledRadial_ne_zero (annulus_axisFree ha hw)
  have hgraphU : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i (physicalLift h n) w‖ ≤ U^i := by
    intro i hi him
    apply (hgraph n hn w hw ht i hi him).trans
    have hqpow : ChartScales.Q n^(-(i:ℝ)*(1+h)) = (ChartScales.Q n^(-(1+h)))^i := by
      rw [← Real.rpow_mul_natCast hQ.le]
      congr 1
      ring
    rw [hqpow]
    calc
      _ ≤ K^i*(ChartScales.Q n^(-(1+h)))^i :=
        mul_le_mul_of_nonneg_right (by simpa only [pow_one] using pow_le_pow_right₀ hK hi) (by positivity)
      _ = (K*ChartScales.Q n^(-(1+h)))^i := (mul_pow _ _ _).symm
      _ ≤ U^i := by
        apply pow_le_pow_left₀ (by positivity)
        dsimp [U]
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hQ.le _)
        exact (show K ≤ K+B by linarith).trans (le_mul_of_one_le_right (by linarith) hSe)
  have hphaseU : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i Φ w‖ ≤ U^i := by
    intro i hi him
    apply (hph i hi him).trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [U]
    gcongr
    linarith
  have hampj := composition_geometric_on hW (physicalLift_smooth h n) hamp hwW m
    (show 0 ≤ A*ChartScales.Q n^g*ChartScales.S n^d by positivity) hU hab hgraphU
  have hcharj := composition_geometric hΦ (character_smooth ((ChartScales.carrier h n:ℝ)*(j:ℝ)))
    w m (pow_nonneg hM0 m) hU
    (fun i hi => by
      rw [norm_character_jet]
      exact (pow_le_pow_left₀ (abs_nonneg _) hc i).trans (pow_le_pow_right₀ hM hi)) hphaseU
  have hampW : ContDiffOn ℝ ∞ (amp ∘ physicalLift h n) W :=
    hamp.contDiffOn.comp (physicalLift_smooth h n) (mapsTo_univ _ _)
  have hprod := product_geometric_on hW hampW
    ((character_smooth _).comp hΦ).contDiffOn hwW m
    (show 0 ≤ (m.factorial:ℝ)*(A*ChartScales.Q n^g*ChartScales.S n^d) by positivity)
    (show 0 ≤ (m.factorial:ℝ)*M^m by positivity) hU hampj hcharj
  apply hprod.trans_eq
  have hqpow : ChartScales.Q n^g * (ChartScales.Q n^(-h/2))^m *
      (ChartScales.Q n^(-(1+h)))^m = ChartScales.Q n^(g-(m:ℝ)*derivativeCost h) := by
    rw [← Real.rpow_mul_natCast hQ.le, ← Real.rpow_mul_natCast hQ.le,
      ← Real.rpow_add hQ, ← Real.rpow_add hQ]
    congr 1
    unfold derivativeCost
    ring
  have hspow : ChartScales.S n^d * (ChartScales.S n^e)^m = ChartScales.S n^(d+e*(m:ℝ)) := by
    rw [← Real.rpow_mul_natCast hS.le, ← Real.rpow_add hS]
  dsimp [M, U, C]
  rw [mul_pow, mul_pow, mul_pow]
  calc
    _ = (2:ℝ)^m*(m.factorial:ℝ)^2*A*(1+2*H)^m*(K+B)^m *
        (ChartScales.Q n^g*(ChartScales.Q n^(-h/2))^m*(ChartScales.Q n^(-(1+h)))^m) *
        (ChartScales.S n^d*(ChartScales.S n^e)^m) := by ring
    _ = _ := by rw [hqpow,hspow]



/-- The exact native carrier, with genuine base-profile hypotheses and all
polar branches covered, has the printed cost per Cartesian derivative. -/
theorem native_carrier_bound {h a b r0 P B dBase : ℝ}
    (hh : 0 ≤ h) (ha : 0 < a) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B)
    (hdBase : 0 ≤ dBase) (m : ℕ) (g dAmp A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ w : SpaceTime,
      scaledRadial n w ∈ annulus a b → |w.1| ≤ 1 →
      ∀ (chart : PolarCharts.Index) (center : Plane) (p pz x0 : ℝ),
      |p| ≤ P → |pz| ≤ P → |x0| ≤ P →
      |etaCoordinate (nativeGraph h n w - center)| ≤ r0 →
      ∀ (amp : LiftPoint → ℂ) (F G : Slow → ℝ) (j : ℤ),
      ContDiff ℝ ∞ amp → ContDiff ℝ ∞ F → ContDiff ℝ ∞ G → |(j:ℝ)| ≤ H →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i amp (physicalLift h n w)‖ ≤
        A * ChartScales.Q n^g * ChartScales.S n^dAmp) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i F
        (slowMap (PolarCharts.chart a chart) h n w)‖ ≤ B*ChartScales.S n^dBase) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i G
        (slowMap (PolarCharts.chart a chart) h n w)‖ ≤ B*ChartScales.S n^dBase) →
      ‖iteratedFDeriv ℝ m ((fun y => amp y *
        character ((ChartScales.carrier h n:ℝ)*(j:ℝ))
          (liftedPhase (PolarCharts.chart a chart) h n center r0 p pz x0 F G y)) ∘
            physicalLift h n) w‖ ≤
      C*ChartScales.Q n^(g-(m:ℝ)*derivativeCost h)*
        ChartScales.S n^(dAmp+(dBase+1)*(m:ℝ)) := by
  obtain ⟨K, hK, hpolar⟩ := PolarCharts.chart_finiteJets_uniform ha b m
  let V := 1+2*r0*ChartScales.Tg
  have hV : 1 ≤ V := by dsimp [V]; nlinarith [ChartScales.Tg_pos]
  obtain ⟨BP, hBP, hphase⟩ := SharpPhysicalPhase.physicalPhase_geometric_bound hh hK hV hP hB hdBase m
  obtain ⟨C, hC, hbound⟩ := carrier_geometric_bound (b := b) hh ha m
    g dAmp (dBase+1) A BP H hA hBP (by linarith) hH
  refine ⟨C,hC,?_⟩
  intro n hn w hw ht chart center p pz x0 hp hpz hx0 hslot amp F G j hamp hF hG hj hab hFb hGb
  have hκ := PolarCharts.chart_contDiff ha chart
  have hκb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i (PolarCharts.chart a chart) (scaledRadial n w)‖ ≤ K :=
    fun i hi => hpolar chart i hi _ hw.1
  have hv : |slotTime h n center r0 w| ≤ V*ChartScales.S n := by
    unfold slotTime
    rw [abs_div, abs_of_pos (ChartScales.timeCoefficient_pos h n), div_eq_mul_inv]
    have hnum : |etaCoordinate (nativeGraph h n w-center)+r0| ≤ 2*r0 := by
      have ht := abs_add_le (etaCoordinate (nativeGraph h n w-center)) r0
      rw [abs_of_nonneg hr0] at ht
      linarith
    calc
      _ ≤ (2*r0)*(ChartScales.Tg*ChartScales.S n) :=
        mul_le_mul hnum (ChartScales.timeCoefficient_inv_upper h hh hn)
          (inv_nonneg.mpr (ChartScales.timeCoefficient_pos h n).le) (by positivity)
      _ ≤ _ := by dsimp [V]; nlinarith [ChartScales.S_pos (show 1 ≤ n by omega)]
  exact hbound n hn w hw ht amp
    (liftedPhase (PolarCharts.chart a chart) h n center r0 p pz x0 F G ∘ physicalLift h n) j
    hamp (SharpPhysicalPhase.physicalPhase_smooth hκ h n center r0 p pz x0 hF hG) hj hab
    (hphase _ hκ n hn center r0 p pz x0 hp hpz hx0 F G hF hG w hκb hv hFb hGb)

end NavierStokes.SharpPhysicalCarrier
end

section

noncomputable section
namespace NavierStokes.SharpLogWeights
open PhysicalGraphBounds

/-- Dyadic slow powers become a polynomial in the physical logarithm,
without sacrificing any power of the physical scale. -/
theorem slow_power_log_bound (e : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ P : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ q : ℝ,
      0 < q → q/2 ≤ ChartScales.Q n →
      ChartScales.S n^e ≤ C*(1+|Real.log q|)^P := by
  let D := (Real.log 2+1)/Real.log 2
  let P := ⌈2*e⌉₊
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D^P, pow_pos hD P, P, ?_⟩
  intro n hn q hq hlo
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlogQ : Real.log (ChartScales.Q n) = -(n:ℝ)*Real.log 2 := by
    simp only [ChartScales.Q, SlotColoring.dyadicQ, Real.log_rpow (by norm_num : (0:ℝ)<2)]
  have hl := Real.log_le_log (by positivity : 0 < q/2) hlo
  rw [Real.log_div hq.ne' (by norm_num : (2:ℝ)≠0), hlogQ] at hl
  have hnlog : (n:ℝ) ≤ D*(1+|Real.log q|) := by
    dsimp [D]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hlog).mpr
    nlinarith [neg_le_abs (Real.log q), abs_nonneg (Real.log q)]
  calc
    ChartScales.S n^e = (n:ℝ)^(2*e) := by
      unfold ChartScales.S
      rw [← Real.rpow_natCast_mul (show 0 ≤ (n:ℝ) by positivity)]
      norm_num
    _ ≤ (n:ℝ)^(P:ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (Nat.le_ceil _)
    _ = (n:ℝ)^P := Real.rpow_natCast _ _
    _ ≤ (D*(1+|Real.log q|))^P := pow_le_pow_left₀ (by positivity) hnlog P
    _ = _ := mul_pow _ _ _

/-- Preserve the exact real exponent while comparing a dyadic chart with
its physical scale and converting the remaining slow factor to logarithms. -/
theorem chart_weight_bound (g e : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ P : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ q : ℝ,
      0 < q → q/2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2*q →
      ChartScales.Q n^g * ChartScales.S n^e ≤ C*q^g*(1+|Real.log q|)^P := by
  obtain ⟨D,hD,P,hslow⟩ := slow_power_log_bound e
  refine ⟨2^|g| * D, by positivity, P, ?_⟩
  intro n hn q hq hlo hhi
  calc
    _ ≤ (2^|g| * q^g)*(D*(1+|Real.log q|)^P) :=
      mul_le_mul (comparable_rpow (ChartScales.Q_pos n) hq hlo hhi g)
        (hslow n hn q hq hlo) (Real.rpow_nonneg (sq_nonneg _) _) (by positivity)
    _ = _ := by ring

end NavierStokes.SharpLogWeights


end

noncomputable section
namespace NavierStokes.SharpPhysicalLoss
open Set Function
open ProblemStatement PhysicalGraphBounds SharpPhysicalPhase SharpPhysicalCarrier
open scoped ContDiff

private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top




end NavierStokes.SharpPhysicalLoss

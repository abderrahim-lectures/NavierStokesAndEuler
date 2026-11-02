import NavierStokes.R3.ActualCandidate
import NavierStokes.R3.WholeSpaceUniqueness
import NavierStokes.R3.ViscosityScaling
import NavierStokes.R3.ViscousEnergyBalance
import NavierStokes.R3.CompactEnergy
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Theorem 1.1: unconditional whole-space forced Navier–Stokes blowup

The actual selected construction supplies the viscosity-one fields. Spatial
rescaling gives every positive viscosity while retaining singular time one,
compact support in strictly positive time for the force, and one kinetic-energy
bound for all times before the singularity. Whole-space comparison excludes a
global smooth finite-energy solution with the same prescribed force and datum.
-/
/-! Merged from `NavierStokes.R3.IntegratedDissipation` (in a section, so its `open`s cannot leak). -/
section
/-!
# Finite integrated dissipation up to the singular time

The time integrability statement is explicit: a totalized real integral is not
used as a substitute for finiteness of the dissipation. The energy balance is
first integrated on shorter closed time intervals, then an exhaustion proves
integrability on the entire half-open interval.
-/

/-! Merged from `NavierStokes.R3.ForceL2Norm`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# The time primitive of the spatial L² norm of a compact force

All spatial and temporal integrals use ordinary Lebesgue volume.
-/

noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology BigOperators ContDiff InnerProductSpace

namespace NavierStokesR3.CompactEnergy

open NavierStokes.ProblemStatement

/-- The ordinary spatial L² norm, used with square-integrable slices. -/
def l2Norm (f : VelocityField) (t : ℝ) : ℝ := Real.sqrt (l2Sq f t)

/-- The time integral of the spatial L² norm starting at time zero. -/
def cumulativeForceNorm (f : VelocityField) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, l2Norm f t

theorem l2Norm_nonneg (f : VelocityField) (t : ℝ) : 0 ≤ l2Norm f t :=
  Real.sqrt_nonneg _

/-- A compact spacetime support supplies one compact spatial support for every
slice, and therefore continuity of the full spatial square integral. -/
theorem l2Sq_continuous {f : VelocityField} (hf : Continuous f)
    (hcf : HasCompactSupport f) : Continuous (l2Sq f) := by
  let K : Set Space := Prod.snd '' tsupport f
  have hK : IsCompact K := hcf.isCompact.image continuous_snd
  rw [← continuousOn_univ]
  apply CompactTimeIntegral.continuousOn_integral
    (F := fun z : SpaceTime => ‖f z‖ ^ 2) hK (hf.norm.pow 2).continuousOn
  intro t ht x hx
  have hz : f (t, x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hx ⟨(t, x), h, rfl⟩
  simp [hz]

theorem l2Norm_continuous {f : VelocityField} (hf : Continuous f)
    (hcf : HasCompactSupport f) : Continuous (l2Norm f) :=
  (l2Sq_continuous hf hcf).sqrt

theorem l2Norm_intervalIntegrable {f : VelocityField} (hf : Continuous f)
    (hcf : HasCompactSupport f) (a b : ℝ) :
    IntervalIntegrable (l2Norm f) volume a b :=
  (l2Norm_continuous hf hcf).intervalIntegrable a b

@[simp] theorem cumulativeForceNorm_zero (f : VelocityField) :
    cumulativeForceNorm f 0 = 0 := by
  simp [cumulativeForceNorm]

theorem cumulativeForceNorm_continuous {f : VelocityField} (hf : Continuous f)
    (hcf : HasCompactSupport f) : Continuous (cumulativeForceNorm f) :=
  intervalIntegral.continuous_primitive (l2Norm_intervalIntegrable hf hcf) 0

theorem cumulativeForceNorm_hasDerivAt {f : VelocityField} (hf : Continuous f)
    (hcf : HasCompactSupport f) (t : ℝ) :
    HasDerivAt (cumulativeForceNorm f) (l2Norm f t) t := by
  have hc := l2Norm_continuous hf hcf
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt



/-- The exact square-primitive identity needed in the integrated energy bound. -/
theorem integral_l2Norm_cumulative_eq_sq {f : VelocityField} (hf : Continuous f)
    (hcf : HasCompactSupport f) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, 2 * l2Norm f t * cumulativeForceNorm f t) =
      (cumulativeForceNorm f T) ^ 2 := by
  have hc := l2Norm_continuous hf hcf
  have hF := cumulativeForceNorm_continuous hf hcf
  have hderiv (t : ℝ) :
      HasDerivAt (fun s => (cumulativeForceNorm f s) ^ 2)
        (2 * l2Norm f t * cumulativeForceNorm f t) t := by
    convert! (cumulativeForceNorm_hasDerivAt hf hcf t).pow 2 using 1
    norm_num
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) (((continuous_const.mul hc).mul hF).intervalIntegrable 0 T)
  simpa using h

end NavierStokesR3.CompactEnergy


end


/-! Merged from `NavierStokes.R3.SharpEnergyBound`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# The sharp scalar estimate for forced kinetic energy

Regularizing the square root removes the apparent singularity at zero energy.
The estimate requires derivatives only in the interior of the time interval.
-/

noncomputable section

open Set MeasureTheory

namespace NavierStokesR3.SharpEnergyBound

/-- A zero-initial-energy differential inequality controls the square root of
the energy by the time integral of the forcing norm. -/
theorem sqrt_energy_le_integral {T : ℝ} {E E' q : ℝ → ℝ}
    (hT : 0 ≤ T) (hcont : ContinuousOn E (Icc 0 T))
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ E t) (hinitial : E 0 = 0)
    (hq : ContinuousOn q (Icc 0 T)) (hqnonneg : ∀ t ∈ Ioo 0 T, 0 ≤ q t)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ 2 * Real.sqrt (E t) * q t) :
    Real.sqrt (E T) ≤ ∫ t in 0..T, q t := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hpos (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < E t + ε ^ 2 :=
    add_pos_of_nonneg_of_pos (hnonneg t ht) (sq_pos_of_pos hε)
  have hscont : ContinuousOn (fun t => Real.sqrt (E t + ε ^ 2)) (Icc 0 T) :=
    Real.continuous_sqrt.comp_continuousOn (hcont.add continuousOn_const)
  have hsderiv (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivWithinAt (fun t => Real.sqrt (E t + ε ^ 2))
        (E' t / (2 * Real.sqrt (E t + ε ^ 2))) (Ioi t) t :=
    ((hderiv t ht).add_const (ε ^ 2)).sqrt
      (ne_of_gt (hpos t ⟨ht.1.le, ht.2.le⟩)) |>.hasDerivWithinAt
  have hsbound (t : ℝ) (ht : t ∈ Ioo 0 T) :
      E' t / (2 * Real.sqrt (E t + ε ^ 2)) ≤ q t := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2)
      (Real.sqrt_pos.2 (hpos t ⟨ht.1.le, ht.2.le⟩)))).2
    have hsqrt : Real.sqrt (E t) ≤ Real.sqrt (E t + ε ^ 2) :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))
    have hmul := mul_le_mul_of_nonneg_right hsqrt (hqnonneg t ht)
    nlinarith [hbound t ht]
  have h := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
    hT hscont hsderiv (hq.integrableOn_Icc) hsbound
  have hzero : Real.sqrt (E 0 + ε ^ 2) = ε := by
    rw [hinitial, zero_add, Real.sqrt_sq hε.le]
  rw [hzero] at h
  have hsqrt : Real.sqrt (E T) ≤ Real.sqrt (E T + ε ^ 2) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))
  linarith


end NavierStokesR3.SharpEnergyBound


end


/-! Merged from `NavierStokes.R3.SpatialCauchySchwarz`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# Spatial Cauchy--Schwarz for the force work

The integrals use ordinary Euclidean volume. Square integrability supplies
the two finite L² norms appearing in the bound.
-/

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

namespace NavierStokesR3.CompactEnergy

open NavierStokes.ProblemStatement

/-- Cauchy--Schwarz bounds the force work by the product of the ordinary
spatial L² norms. The force only needs finite L² norm and continuity. -/
theorem work_le_sqrt_l2Sq {u f : VelocityField} {t : ℝ}
    (hu : Continuous (fun x : Space => u (t, x)))
    (hf : Continuous (fun x : Space => f (t, x)))
    (hcu : HasCompactSupport (fun x : Space => u (t, x)))
    (hf_sq : Integrable (fun x : Space => ‖f (t, x)‖ ^ 2)) :
    (∫ x : Space, ⟪u (t, x), f (t, x)⟫_ℝ) ≤
      Real.sqrt (l2Sq u t) * Real.sqrt (l2Sq f t) := by
  have huLp : MemLp (fun x : Space => u (t, x)) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mpr
      (integrable_norm_sq hu hcu)
  have hfLp : MemLp (fun x : Space => f (t, x)) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hf_sq
  have hholder := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using huLp) (by simpa using hfLp)
  have hprod : Integrable (fun x : Space => ‖u (t, x)‖ * ‖f (t, x)‖) :=
    huLp.norm.integrable_mul hfLp.norm
  calc
    (∫ x : Space, ⟪u (t, x), f (t, x)⟫_ℝ) ≤
        ∫ x : Space, ‖u (t, x)‖ * ‖f (t, x)‖ :=
      integral_mono (integrable_inner_left hu hf hcu) hprod
        (fun x => real_inner_le_norm _ _)
    _ ≤ Real.sqrt (l2Sq u t) * Real.sqrt (l2Sq f t) := by
      simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, l2Sq] using hholder

end NavierStokesR3.CompactEnergy


end


noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace NavierStokesR3.CompactEnergy

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicUniqueness

/-- The exact energy identity integrated over any shorter time interval. -/
theorem integrated_energy_balance {ν T : ℝ} {u f : VelocityField}
    {p : PressureField} {K : Set Space} (hT : 0 < T)
    (hK : IsCompact K) (hu : ContDiffOn ℝ ∞ u (slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (slab 0 T)) (hf : Continuous f)
    (hsupp : ∀ r ∈ Icc (0 : ℝ) T, tsupport (fun x => u (r, x)) ⊆ K)
    (hinitial : ∀ x : Space, u (0, x) = 0)
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      ProblemStatement.navierStokesResidual ν u p t x = f (t, x)) :
    l2Sq u T + 2 * ν * (∫ t in (0 : ℝ)..T, dissipation u t) =
      2 * ∫ t in (0 : ℝ)..T, ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ := by
  have hd : IntervalIntegrable (dissipation u) volume 0 T := (dissipation_continuousOn hT hK hu hsupp).intervalIntegrable_of_Icc hT.le
  have hw : IntervalIntegrable (fun t => ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) volume 0 T := (forceWork_continuousOn hK hu.continuousOn hf.continuousOn hsupp).intervalIntegrable_of_Icc hT.le
  have hb := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le
    (l2Sq_continuousOn hK hu hsupp)
    (fun t ht => hasDerivAt_energy_balance_viscosity hK hu hp
      (hf.comp (continuous_const.prodMk continuous_id)) hsupp ht (hdiv t ht) (hNS t ht))
    ((hd.const_mul (-2 * ν)).add (hw.const_mul 2))
  rw [intervalIntegral.integral_add (hd.const_mul (-2 * ν)) (hw.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hb
  have hzero : l2Sq u 0 = 0 := by simp [l2Sq, hinitial]
  rw [hzero] at hb
  linarith

/-- Young's inequality, before discarding the viscous dissipation. -/
theorem force_work_le {u f : VelocityField} {t : ℝ}
    (hu : Continuous (fun x : Space => u (t, x)))
    (hf : Continuous (fun x : Space => f (t, x)))
    (hcu : HasCompactSupport (fun x : Space => u (t, x)))
    (hfi : Integrable (fun x : Space => ‖f (t, x)‖ ^ 2)) :
    2 * (∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) ≤ l2Sq u t + l2Sq f t := by
  have hui := integrable_norm_sq hu hcu
  have hip := integrable_inner_left hu hf hcu
  rw [← integral_const_mul]
  unfold l2Sq
  rw [← integral_add hui hfi]
  apply integral_mono (hip.const_mul 2) (hui.add hfi)
  intro x
  have hi := (le_abs_self ⟪u (t, x), f (t, x)⟫_ℝ).trans
    (abs_real_inner_le_norm (u (t, x)) (f (t, x)))
  dsimp only [Pi.add_apply] at *
  nlinarith [sq_nonneg (‖u (t, x)‖ - ‖f (t, x)‖)]

/-- The dissipation of a paper candidate is integrable in time on the whole
interval before blowup. This is the finite total dissipation conclusion of
Lemma 10.4, in addition to the uniform kinetic-energy bound. -/
theorem candidate_integrable_dissipation {ν : ℝ} (hν : 0 < ν)
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K) :
    IntegrableOn (dissipation u) (Ico (0 : ℝ) 1) := by
  obtain ⟨E, hE, henergy⟩ := hc.energy_bounded
  obtain ⟨C, hC, hforce⟩ := CompactForceBound.exists_uniform_l2sq_bound
    hc.force_smooth.continuous hc.force_support.1
  have hlocal (T : ℝ) (hT : T ∈ Ioo (0 : ℝ) 1) :
      IntegrableOn (dissipation u) (Ioc (0 : ℝ) T) ∧
      (∫ t in Ioc (0 : ℝ) T, ‖dissipation u t‖) ≤ (2 * E + C) / (2 * ν) := by
    have hsub : slab 0 T ⊆ preSingularDomain := by
      intro z hz
      exact ⟨⟨hz.1.1, hz.1.2.trans_lt hT.2⟩, hz.2⟩
    have hu := hc.velocity_smooth.mono hsub
    have hp := hc.pressure_smooth.mono hsub
    have hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => u (t, x)) ⊆ K := by
      intro t ht
      exact hc.velocity_support t ⟨ht.1, ht.2.trans_lt hT.2⟩
    have hdcont := dissipation_continuousOn hT.1 hc.support_compact hu hsupp
    have hd : IntervalIntegrable (dissipation u) volume 0 T := hdcont.intervalIntegrable_of_Icc hT.1.le
    refine ⟨hd.1, ?_⟩
    have hwork : IntervalIntegrable (fun t => ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) volume 0 T := (forceWork_continuousOn hc.support_compact hu.continuousOn
      hc.force_smooth.continuous.continuousOn hsupp).intervalIntegrable_of_Icc hT.1.le
    have hbal := integrated_energy_balance hT.1 hc.support_compact hu hp
      hc.force_smooth.continuous hsupp hc.zero_initial_velocity
      (fun t ht => hc.divergence_free t ⟨ht.1.le, ht.2.trans hT.2⟩)
      (fun t ht => hc.navier_stokes t ⟨ht.1, ht.2.trans hT.2⟩)
    have hworkbound : 2 * (∫ t in (0 : ℝ)..T, ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) ≤
        (2 * E + C) * T := by
      rw [← intervalIntegral.integral_const_mul]
      calc
        (∫ t in (0 : ℝ)..T, 2 * ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) ≤
            ∫ t in (0 : ℝ)..T, (2 * E + C) := by
          apply intervalIntegral.integral_mono_on hT.1.le (hwork.const_mul 2)
            intervalIntegrable_const
          intro t ht
          have ht1 : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1, ht.2.trans_lt hT.2⟩
          have hfT := hforce t ⟨ht.1, ht1.2.le⟩
          have huT := henergy t ht1
          have hyoung := force_work_le (spatial_smooth hu ht).continuous
            (hc.force_smooth.continuous.comp (continuous_const.prodMk continuous_id))
            (slice_compact hc.support_compact (hsupp t ht)) hfT.1
          change ProblemStatement.SquareIntegrableAtTime u t ∧ (1 / 2 : ℝ) * l2Sq u t ≤ E at huT
          change Integrable (fun x => ‖f (t, x)‖ ^ 2) ∧ l2Sq f t ≤ C at hfT
          linarith [huT.2, hfT.2]
        _ = (2 * E + C) * T := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]; ring
    have hnonneg : 0 ≤ l2Sq u T := integral_nonneg (fun _ => sq_nonneg _)
    have hd_bound : (∫ t in (0 : ℝ)..T, dissipation u t) ≤ (2 * E + C) / (2 * ν) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * ν)).2
      have hsize : (2 * E + C) * T ≤ 2 * E + C := by
        exact mul_le_of_le_one_right (by positivity) hT.2.le
      nlinarith
    simpa only [Real.norm_of_nonneg (dissipation_nonneg u _),
      intervalIntegral.integral_of_le hT.1.le] using hd_bound
  let b : Ioo (0 : ℝ) 1 → ℝ := fun t => t.1
  have hb : Tendsto b (comap b (𝓝[<] (1 : ℝ))) (𝓝 1) := by
    exact tendsto_comap.trans nhdsWithin_le_nhds
  have : NeBot (comap b (𝓝[<] (1 : ℝ))) := by
    apply (inferInstance : NeBot (𝓝[<] (1 : ℝ))).comap_of_range_mem
    rw [show Set.range b = Ioo (0 : ℝ) 1 from Subtype.range_coe_subtype]
    exact Ioo_mem_nhdsLT zero_lt_one
  have hwhole : IntegrableOn (dissipation u) (Ioc (0 : ℝ) 1) :=
    integrableOn_Ioc_of_intervalIntegral_norm_bounded_right
      (l := comap b (𝓝[<] (1 : ℝ))) (b := b)
      (fun t => (hlocal t.1 t.2).1) hb
      (Filter.Eventually.of_forall (fun t => (hlocal t.1 t.2).2))
  exact (integrableOn_Ico_iff_integrableOn_Ioo).mpr
    ((integrableOn_Ioc_iff_integrableOn_Ioo).mp hwhole)

/-- The velocity's L² norm is at most the accumulated L² norm of its force. -/
theorem candidate_l2Norm_le_cumulativeForceNorm {ν : ℝ} (hν : 0 < ν)
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K)
    {T : ℝ} (hT : T ∈ Ico (0 : ℝ) 1) :
    l2Norm u T ≤ cumulativeForceNorm f T := by
  have hsub : slab 0 T ⊆ preSingularDomain := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_lt hT.2⟩, hz.2⟩
  have hu := hc.velocity_smooth.mono hsub
  have hp := hc.pressure_smooth.mono hsub
  have hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => u (t, x)) ⊆ K := by
    intro t ht
    exact hc.velocity_support t ⟨ht.1, ht.2.trans_lt hT.2⟩
  obtain ⟨C, hC, hforce⟩ := CompactForceBound.exists_uniform_l2sq_bound
    hc.force_smooth.continuous hc.force_support.1
  apply SharpEnergyBound.sqrt_energy_le_integral hT.1
    (l2Sq_continuousOn hc.support_compact hu hsupp)
    (fun t _ => integral_nonneg (fun _ => sq_nonneg _))
    (by simp [l2Sq, hc.zero_initial_velocity])
    (l2Norm_continuous hc.force_smooth.continuous hc.force_support.1).continuousOn
    (fun t _ => l2Norm_nonneg f t)
    (fun t ht => energy_hasDerivAt hc.support_compact hu hsupp ht)
  intro t ht
  have ht1 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hT.2⟩
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
  have huT := spatial_smooth hu htT
  have hpT := spatial_smooth hp htT
  have hcompact := slice_compact hc.support_compact (hsupp t htT)
  have hfT : Continuous (fun x : Space => f (t, x)) := hc.force_smooth.continuous.comp (continuous_const.prodMk continuous_id)
  have hwork := work_le_sqrt_l2Sq huT.continuous hfT hcompact
    (hforce t ⟨ht1.1.le, ht1.2.le⟩).1
  rw [energy_balance_viscosity huT hpT hfT hcompact
    (hc.divergence_free t ⟨ht1.1.le, ht1.2⟩) (hc.navier_stokes t ht1)]
  dsimp only [l2Norm]
  have hd := dissipation_nonneg u t
  have hνd : 0 ≤ ν * dissipation u t := mul_nonneg hν.le hd
  nlinarith


/-- The sharp energy and accumulated dissipation inequality from Lemma 10.4,
with the viscosity restored. Both norms use ordinary spatial volume. -/
theorem candidate_energy_dissipation_le {ν : ℝ} (hν : 0 < ν)
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K)
    {T : ℝ} (hT : T ∈ Ico (0 : ℝ) 1) :
    l2Sq u T + 2 * ν * (∫ t in (0 : ℝ)..T, dissipation u t) ≤
      (cumulativeForceNorm f T) ^ 2 := by
  rcases hT.1.eq_or_lt with hzero | hpos
  · subst T
    simp [l2Sq, hc.zero_initial_velocity]
  have hsub : slab 0 T ⊆ preSingularDomain := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_lt hT.2⟩, hz.2⟩
  have hu := hc.velocity_smooth.mono hsub
  have hp := hc.pressure_smooth.mono hsub
  have hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => u (t, x)) ⊆ K := by
    intro t ht
    exact hc.velocity_support t ⟨ht.1, ht.2.trans_lt hT.2⟩
  have hbal := integrated_energy_balance hpos hc.support_compact hu hp
    hc.force_smooth.continuous hsupp hc.zero_initial_velocity
    (fun t ht => hc.divergence_free t ⟨ht.1.le, ht.2.trans hT.2⟩)
    (fun t ht => hc.navier_stokes t ⟨ht.1, ht.2.trans hT.2⟩)
  rw [hbal, ← integral_l2Norm_cumulative_eq_sq hc.force_smooth.continuous hc.force_support.1,
    ← intervalIntegral.integral_const_mul]
  have hwork : IntervalIntegrable (fun t => ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) volume 0 T :=
    (forceWork_continuousOn hc.support_compact hu.continuousOn
      hc.force_smooth.continuous.continuousOn hsupp).intervalIntegrable_of_Icc hT.1
  have hq := l2Norm_continuous hc.force_smooth.continuous hc.force_support.1
  have hF := cumulativeForceNorm_continuous hc.force_smooth.continuous hc.force_support.1
  apply intervalIntegral.integral_mono_on hT.1 (hwork.const_mul 2)
    (((continuous_const.mul hq).mul hF).intervalIntegrable 0 T)
  intro t ht
  have ht1 : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1, ht.2.trans_lt hT.2⟩
  obtain ⟨C, hC, hforce⟩ := CompactForceBound.exists_uniform_l2sq_bound
    hc.force_smooth.continuous hc.force_support.1
  have hcs := work_le_sqrt_l2Sq (spatial_smooth hu ht).continuous
    (hc.force_smooth.continuous.comp (continuous_const.prodMk continuous_id))
    (slice_compact hc.support_compact (hsupp t ht)) (hforce t ⟨ht.1, ht1.2.le⟩).1
  have hb := mul_le_mul_of_nonneg_right
    (candidate_l2Norm_le_cumulativeForceNorm hν hc ht1) (l2Norm_nonneg f t)
  change (∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) ≤ l2Norm u t * l2Norm f t at hcs
  dsimp only [Pi.mul_apply]
  nlinarith

/-- Passing to the singular endpoint retains the sharp bound on the total
viscous dissipation. Integrability has already been proved independently. -/
theorem candidate_total_dissipation_le {ν : ℝ} (hν : 0 < ν)
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K) :
    2 * ν * (∫ t in Ico (0 : ℝ) 1, dissipation u t) ≤
      (cumulativeForceNorm f 1) ^ 2 := by
  have hint := candidate_integrable_dissipation hν hc
  have hicc : IntegrableOn (dissipation u) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (integrableOn_Icc_iff_integrableOn_Ico).mpr hint
  have hcont : ContinuousOn
      (fun T => 2 * ν * ∫ t in (0 : ℝ)..T, dissipation u t) (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using
      (intervalIntegral.continuousOn_primitive_interval hicc).const_mul (2 * ν)
  have hF := (cumulativeForceNorm_continuous hc.force_smooth.continuous hc.force_support.1).pow 2
  have hbound (T : ℝ) (hT : T ∈ Ico (0 : ℝ) 1) :
      2 * ν * (∫ t in (0 : ℝ)..T, dissipation u t) ≤ (cumulativeForceNorm f T) ^ 2 := by
    have h := candidate_energy_dissipation_le hν hc hT
    have hE : 0 ≤ l2Sq u T := integral_nonneg (fun _ => sq_nonneg _)
    linarith
  have hlimit := le_on_closure hbound
    (by simpa only [closure_Ico (zero_ne_one : (0 : ℝ) ≠ 1)] using hcont)
    hF.continuousOn
    (show (1 : ℝ) ∈ closure (Ico (0 : ℝ) 1) by
      rw [closure_Ico zero_ne_one]
      exact ⟨zero_le_one, le_rfl⟩)
  simpa only [integral_Ico_eq_integral_Ioc,
    intervalIntegral.integral_of_le zero_le_one] using hlimit

/-- The complete energy conclusions of Lemma 10.4 for one paper candidate:
finite accumulated force norm, genuine total dissipation integrability, the
sharp inequality on every shorter interval, and its total-dissipation bound. -/
theorem candidate_energy_estimates {ν : ℝ} (hν : 0 < ν)
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K) :
    IntervalIntegrable (l2Norm f) volume 0 1 ∧
    IntegrableOn (dissipation u) (Ico (0 : ℝ) 1) ∧
    (∀ T ∈ Ico (0 : ℝ) 1,
      l2Sq u T + 2 * ν * (∫ t in (0 : ℝ)..T, dissipation u t) ≤
        (cumulativeForceNorm f T) ^ 2) ∧
    2 * ν * (∫ t in Ico (0 : ℝ) 1, dissipation u t) ≤
      (cumulativeForceNorm f 1) ^ 2 :=
  ⟨l2Norm_intervalIntegrable hc.force_smooth.continuous hc.force_support.1 0 1,
    candidate_integrable_dissipation hν hc,
    fun _ hT => candidate_energy_dissipation_le hν hc hT,
    candidate_total_dissipation_le hν hc⟩

end NavierStokesR3.CompactEnergy
end


/-! Merged from `NavierStokes.R3.CandidateBreakdown`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# A compact singular candidate excludes a global finite-energy solution

The comparison theorem identifies the two velocities before time one. The
candidate's fixed compact spatial support then confines its unbounded speed
to a compact spacetime set on which a global smooth velocity is bounded.
-/

noncomputable section

open Set
open scoped ContDiff

namespace NavierStokesR3.ProblemStatement

theorem CandidateProperties.not_global_agreement {ν : ℝ}
    {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (h : CandidateProperties ν u p f K) {v : VelocityField}
    (hv : ContDiffOn ℝ ∞ v futureDomain) :
    ¬ (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, u (t, x) = v (t, x)) := by
  intro heq
  have hsub : Icc (0 : ℝ) 1 ×ˢ K ⊆ futureDomain :=
    fun _ hz => ⟨hz.1.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod h.support_compact).exists_bound_of_continuousOn
    (hv.continuousOn.mono hsub)
  have hpos : 0 < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨t, x, ht, _, hlarge⟩ := h.speed_unbounded (max M 1) hpos 1 zero_lt_one
  have hx : x ∈ K := by
    apply h.velocity_support t ⟨ht.1.le, ht.2⟩
    apply subset_tsupport
    intro hz
    change u (t, x) = 0 at hz
    rw [hz, norm_zero] at hlarge
    exact (not_lt_of_ge hpos.le) hlarge
  have hb := hM (t, x) ⟨⟨ht.1.le, ht.2.le⟩, hx⟩
  rw [heq t ⟨ht.1.le, ht.2⟩ x] at hlarge
  exact (not_lt_of_ge (hb.trans (le_max_left M 1))) hlarge

/-- The comparison class has only smoothness, the equation, zero initial
velocity, and a uniform energy bound; no support assumption is imposed on it. -/
theorem CandidateProperties.no_global_solution_one
    {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (h : CandidateProperties 1 u p f K) :
    ¬ Nonempty (GlobalFiniteEnergySolution 1 f) := by
  rintro ⟨v⟩
  exact h.not_global_agreement v.velocity_smooth
    (WholeSpaceUniqueness.candidate_global_agrees_before_one h v)


/-- One bound for the actual spatial square integrals, with integrability
proved separately so that the totalized integral cannot hide infinite energy. -/
theorem CandidateProperties.uniform_l2_sq_bound {ν : ℝ}
    {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (h : CandidateProperties ν u p f K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico (0 : ℝ) 1,
      SquareIntegrableAtTime u t ∧ (∫ x : Space, ‖u (t, x)‖ ^ 2) ≤ C := by
  obtain ⟨E, hE, hb⟩ := h.energy_bounded
  refine ⟨2 * E, by positivity, ?_⟩
  intro t ht
  obtain ⟨hi, he⟩ := hb t ht
  refine ⟨hi, ?_⟩
  change (1 / 2 : ℝ) * (∫ x : Space, ‖u (t, x)‖ ^ 2) ≤ E at he
  linarith

end NavierStokesR3.ProblemStatement


end


noncomputable section

open Set MeasureTheory

namespace NavierStokesR3

open ProblemStatement ViscosityScaling

/-- The full paper conclusion, together with the initial time interval on
which the constructed velocity is at rest. No construction hypotheses remain. -/
theorem theorem_1_1_with_initial_rest (ν : ℝ) (hν : 0 < ν) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧
      ¬ Nonempty (GlobalFiniteEnergySolution ν f) ∧
      ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space,
        u (t, x) = 0 ∧ p (t, x) = 0 := by
  obtain ⟨u, p, f, K, hc, hzero⟩ := ActualCandidate.selected_candidate_one_with_initial_rest
  refine ⟨scaledVelocity ν u, scaledPressure ν p, scaledVelocity ν f,
    (fun x : Space => Real.sqrt ν • x) '' K, candidate_at_viscosity hc hν, ?_, ?_⟩
  · rintro ⟨v⟩
    exact hc.no_global_solution_one ⟨normalized_global_solution hν v⟩
  · intro t ht x
    constructor
    · change Real.sqrt ν • u (t, (Real.sqrt ν)⁻¹ • x) = 0
      rw [(hzero t ht _).1, smul_zero]
    · change ν • p (t, (Real.sqrt ν)⁻¹ • x) = 0
      rw [(hzero t ht _).2, smul_zero]

/-- Theorem 1.1, with all properties of the same velocity, pressure, force,
and compact support witnessed simultaneously, for every positive viscosity. -/
theorem theorem_1_1 : ProblemStatement.breakdownStatement := by
  intro ν hν
  obtain ⟨u, p, f, K, hc, hg, _⟩ := theorem_1_1_with_initial_rest ν hν
  exact ⟨u, p, f, K, hc, hg⟩

/-- The primary whole-space candidate-existence assertion at any positive viscosity. -/
theorem candidateStatement (ν : ℝ) (hν : 0 < ν) :
    ProblemStatement.candidateStatement ν := by
  obtain ⟨u, p, f, K, hc, _⟩ := theorem_1_1 ν hν
  exact ⟨u, p, f, K, hc⟩

/-- The candidate construction is unconditional for every positive viscosity. -/
theorem coreBreakdownStatement : ProblemStatement.coreBreakdownStatement :=
  candidateStatement

/-- The whole-space breakdown assertion is an unconditional theorem. -/
theorem breakdownStatement : ProblemStatement.breakdownStatement := theorem_1_1

/-- Theorem 1.1 and all energy conclusions of Lemma 10.4 hold for the same
constructed fields. Total dissipation is explicitly integrable up to time one. -/
theorem theorem_1_1_with_dissipation (ν : ℝ) (hν : 0 < ν) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧
      ¬ Nonempty (GlobalFiniteEnergySolution ν f) ∧
      IntervalIntegrable (CompactEnergy.l2Norm f) volume 0 1 ∧
      IntegrableOn (CompactEnergy.dissipation u) (Ico (0 : ℝ) 1) ∧
      (∀ T ∈ Ico (0 : ℝ) 1,
        CompactEnergy.l2Sq u T +
          2 * ν * (∫ t in (0 : ℝ)..T, CompactEnergy.dissipation u t) ≤
            (CompactEnergy.cumulativeForceNorm f T) ^ 2) ∧
      2 * ν * (∫ t in Ico (0 : ℝ) 1, CompactEnergy.dissipation u t) ≤
        (CompactEnergy.cumulativeForceNorm f 1) ^ 2 := by
  obtain ⟨u, p, f, K, hc, hg⟩ := theorem_1_1 ν hν
  exact ⟨u, p, f, K, hc, hg, CompactEnergy.candidate_energy_estimates hν hc⟩

end NavierStokesR3

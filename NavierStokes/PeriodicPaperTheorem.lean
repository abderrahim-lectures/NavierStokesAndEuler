import NavierStokes.PeriodicLocalization
import NavierStokes.R3.ProblemStatement
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Tactic.Linarith
import NavierStokes.R3.ViscosityScaling
import NavierStokes.R3.SpatialSupportScaling
import NavierStokes.ResidualRegularity
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import NavierStokes.R3.Theorem
import NavierStokes.PeriodizePDE
import NavierStokes.PeriodicUniqueness
import NavierStokes.ComparatorBridge
import NavierStokes.MaximalLifespan
import NavierStokes.CandidateConsequences

/-!
# The full periodic corollary of the paper

The torus is represented by spatially periodic lifts to R³. The support
clauses intersect topological support with the closed fundamental cube:
they do not assert compact support of a nonzero periodic lift on all of R³.
-/
/-! Merged from `NavierStokes.R3.ParabolicDefinitions`. -/
/-! Merged from `NavierStokes.R3.DelayedExtension`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# Smooth extension by zero to negative times

A field that vanishes on a time interval around zero has a smooth extension by
zero to all negative times. The agreement with zero on an open neighborhood of
the seam proves every differentiability order at once.
-/

noncomputable section

namespace NavierStokesR3.ParabolicScaling

open NavierStokes.ProblemStatement Set Filter
open scoped ContDiff Topology

/-- Keep the original field at nonnegative times and use zero before time zero. -/
def zeroBefore {V : Type*} [Zero V] (g : SpaceTime → V) (z : SpaceTime) : V :=
  if 0 ≤ z.1 then g z else 0

theorem zeroBefore_eq_of_nonneg {V : Type*} [Zero V] (g : SpaceTime → V)
    {z : SpaceTime} (hz : 0 ≤ z.1) : zeroBefore g z = g z := by
  simp only [zeroBefore, ite_eq_left hz]

theorem zeroBefore_eq_zero_of_neg {V : Type*} [Zero V] (g : SpaceTime → V)
    {z : SpaceTime} (hz : z.1 < 0) : zeroBefore g z = 0 := by
  simp only [zeroBefore, ite_eq_right (not_le.mpr hz)]

theorem zeroBefore_eventuallyEq_of_pos {V : Type*} [Zero V] (g : SpaceTime → V)
    {z : SpaceTime} (hz : 0 < z.1) : zeroBefore g =ᶠ[𝓝 z] g := by
  filter_upwards [continuous_fst.continuousAt.eventually_const_lt hz] with y hy
  exact zeroBefore_eq_of_nonneg g hy.le


theorem zeroBefore_eq_zero_of_le {V : Type*} [Zero V] {g : SpaceTime → V}
    (hzero : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, g (t, x) = 0)
    {z : SpaceTime} (hz : z.1 ≤ 3 / 8) : zeroBefore g z = 0 := by
  by_cases ht : 0 ≤ z.1
  · rw [zeroBefore_eq_of_nonneg g ht]
    exact hzero z.1 (by rwa [abs_of_nonneg ht]) z.2
  · simp only [zeroBefore, ite_eq_right ht]

theorem zeroBefore_eq_zero_of_nonpos {V : Type*} [Zero V] {g : SpaceTime → V}
    (hzero : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, g (t, x) = 0)
    {z : SpaceTime} (hz : z.1 ≤ 0) : zeroBefore g z = 0 := by
  exact zeroBefore_eq_zero_of_le hzero (by linarith)

theorem zeroBefore_eventuallyEq_zero {V : Type*} [Zero V] {g : SpaceTime → V}
    (hzero : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, g (t, x) = 0)
    {z : SpaceTime} (hz : z.1 < 3 / 8) :
    zeroBefore g =ᶠ[𝓝 z] (fun _ => 0) := by
  filter_upwards [continuous_fst.continuousAt.eventually_lt_const hz] with y hy
  exact zeroBefore_eq_zero_of_le hzero hy.le

theorem zeroBefore_eventually_eq {V : Type*} [Zero V] (g : SpaceTime → V)
    {z : SpaceTime} (hz : 0 < z.1) : zeroBefore g =ᶠ[𝓝 z] g :=
  zeroBefore_eventuallyEq_of_pos g hz

theorem zeroBefore_eventually_zero {V : Type*} [Zero V] {g : SpaceTime → V}
    (hzero : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, g (t, x) = 0)
    {z : SpaceTime} (hz : z.1 ≤ 0) : zeroBefore g =ᶠ[𝓝 z] (fun _ => 0) :=
  zeroBefore_eventuallyEq_zero hzero (by linarith)

/-- Extending by zero is smooth even at time zero, because the field vanishes
on a fixed interval there. -/
theorem zeroBefore_smooth_on {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : SpaceTime → V} (hg : ContDiffOn ℝ ∞ g preSingularDomain)
    (hzero : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, g (t, x) = 0) :
    ContDiffOn ℝ ∞ (zeroBefore g) (Iio 1 ×ˢ univ) := by
  intro z hz
  by_cases ht : z.1 < 3 / 8
  · exact (contDiffAt_const.congr_of_eventuallyEq
      (zeroBefore_eventuallyEq_zero hzero ht)).contDiffWithinAt
  · have htpos : 0 < z.1 := by linarith
    have hdomain : preSingularDomain ∈ 𝓝 z := by
      filter_upwards [continuous_fst.continuousAt.eventually_const_lt htpos,
        continuous_fst.continuousAt.eventually_lt_const hz.1] with y hy0 hy1
      exact ⟨⟨hy0.le, hy1⟩, mem_univ _⟩
    exact ((hg.contDiffAt hdomain).congr_of_eventuallyEq
      (zeroBefore_eventuallyEq_of_pos g htpos)).contDiffWithinAt

end NavierStokesR3.ParabolicScaling


end

noncomputable section

namespace NavierStokesR3.ParabolicScaling

open ProblemStatement Set

/-- The affine clock sends time one to itself and starts at `1-l⁻²`. -/
def clock (l t : ℝ) : ℝ := l ^ 2 * (t - 1) + 1

/-- Simultaneous affine time change, spatial dilation, and amplitude change. -/
def pull {V : Type*} [SMul ℝ V] (a l : ℝ) (g : SpaceTime → V) : SpaceTime → V :=
  fun z => a • g (clock l z.1, l • z.2)

def velocity (l : ℝ) (u : VelocityField) : VelocityField :=
  pull l l (zeroBefore u)

def pressure (l : ℝ) (p : PressureField) : PressureField :=
  pull (l ^ 2) l (zeroBefore p)

def force (l : ℝ) (f : VelocityField) : VelocityField :=
  pull (l ^ 3) l f

theorem clock_lt_one {l t : ℝ} (hl : 0 < l) (ht : t < 1) : clock l t < 1 := by
  dsimp [clock]
  nlinarith [sq_pos_of_pos hl]

theorem clock_zero_nonpos {l : ℝ} (hl : 1 ≤ l) : clock l 0 ≤ 0 := by
  dsimp [clock]
  nlinarith

end NavierStokesR3.ParabolicScaling

/-! Merged from `NavierStokes.R3.ParabolicSupport`. -/
/-!
# Support after affine time and spatial rescaling

Positive affine time slopes and nonpositive time offsets preserve the force
class. A sufficiently large spatial dilation puts any compact spatial support
inside the central coordinate cube.
-/

noncomputable section

open Set

namespace NavierStokesR3.ProblemStatement

/-- The inverse affine spacetime transform maps compact sets to compact sets. -/
theorem isCompact_affineSpacetime_image {K : Set SpaceTime} (hK : IsCompact K)
    (b c d : ℝ) :
    IsCompact ((fun z : SpaceTime => ((z.1 - d) / c, b⁻¹ • z.2)) '' K) := by
  exact hK.image (((continuous_fst.sub continuous_const).div_const c).prodMk
    (continuous_snd.const_smul b⁻¹))

/-- Affine pullback with a positive time slope and a nonpositive offset
preserves compact support in strictly positive time. -/
theorem CompactPositiveTimeSupport.affineScale {f : VelocityField}
    (hf : CompactPositiveTimeSupport f) (a b c d : ℝ) (hb : b ≠ 0)
    (hc : 0 < c) (hd : d ≤ 0) :
    CompactPositiveTimeSupport
      (fun z : SpaceTime => a • f (c * z.1 + d, b • z.2)) := by
  have hsub : tsupport (fun z : SpaceTime => a • f (c * z.1 + d, b • z.2)) ⊆
      (fun z : SpaceTime => ((z.1 - d) / c, b⁻¹ • z.2)) '' tsupport f := by
    intro z hz
    have hz' : (c * z.1 + d, b • z.2) ∈ tsupport f :=
      tsupport_comp_subset_preimage f
        (((continuous_fst.const_mul c).add continuous_const).prodMk
          (continuous_snd.const_smul b))
        (tsupport_smul_subset_right (fun _ : SpaceTime => a)
          (fun z => f (c * z.1 + d, b • z.2)) hz)
    refine ⟨(c * z.1 + d, b • z.2), hz', ?_⟩
    apply Prod.ext
    · dsimp
      field_simp
      ring
    · simp [smul_smul, hb]
  constructor
  · exact (isCompact_affineSpacetime_image hf.1 b c d).of_isClosed_subset
      (isClosed_tsupport _) hsub
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := hsub hz
    refine ⟨div_pos (sub_pos.mpr ?_) hc, mem_univ _⟩
    exact hd.trans_lt (hf.2 hw).1

/-- Every compact spatial set can be put in the central quarter cube by an
inverse dilation whose factor is greater than one. -/
theorem exists_spatialScale_into_quarterCube {K : Set Space} (hK : IsCompact K) :
    ∃ b : ℝ, 1 < b ∧ ∀ x ∈ (fun y : Space => b⁻¹ • y) '' K,
      ∀ i : Fin 3, |x i| ≤ (1 / 4 : ℝ) := by
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨4 * R + 2, by linarith, ?_⟩
  rintro x ⟨y, hy, rfl⟩ i
  have hb : 0 < 4 * R + 2 := by linarith
  have hyi : |y i| ≤ R := (PiLp.norm_apply_le y i).trans (hbound y hy)
  change |(4 * R + 2)⁻¹ * y i| ≤ _
  rw [abs_mul, abs_of_pos (inv_pos.mpr hb)]
  have hdiv : |y i| / (4 * R + 2) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ hb).mpr
    linarith
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

end NavierStokesR3.ProblemStatement

/-! Merged from `NavierStokes.R3.ParabolicScaling` (in a section, so its `open`s cannot leak). -/
section
/-!
# Parabolic compression with singular time fixed at one

The clock is `l²(t-1)+1`. Extension by zero before the original initial time
makes the compressed solution start from rest, while the spatial support is
divided by the arbitrary factor `l > 1`. Viscosity remains unchanged.
-/

/-! Merged from `NavierStokes.R3.ParabolicCalculus`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

noncomputable section

namespace NavierStokesR3.ParabolicScaling

open NavierStokes.ProblemStatement Set Filter
open scoped ContDiff Topology

theorem pull_temporalDerivative (a l : ℝ) (u : VelocityField) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun s => u (s, l • x)) (clock l t)) :
    temporalDerivative (pull a l u) t x =
      (a * l ^ 2) • temporalDerivative u (clock l t) (l • x) := by
  have hc : HasDerivAt (clock l) (l ^ 2) t := by
    convert ((((hasDerivAt_id t).sub_const 1).const_mul (l ^ 2)).add_const 1) using 1
    all_goals first | rfl | simp
  have hd := (hu.hasDerivAt.scomp t hc).const_smul a
  change deriv (fun s => a • u (clock l s, l • x)) t =
    (a * l ^ 2) • deriv (fun s => u (s, l • x)) (clock l t)
  simpa only [Function.comp_def, Pi.smul_def, smul_smul] using hd.deriv


theorem pull_divergence (a l : ℝ) (u : VelocityField) (t : ℝ) (x : Space) :
    spatialDivergence (pull a l u) t x = (a * l) * spatialDivergence u (clock l t) (l • x) := by
  exact ViscosityScaling.rescale_divergence a l
    (fun z => u (clock l z.1, z.2)) t x

theorem pull_advection (a l : ℝ) (u : VelocityField) (t : ℝ) (x : Space) :
    advection (pull a l u) t x = (a ^ 2 * l) • advection u (clock l t) (l • x) := by
  exact ViscosityScaling.rescale_advection a l
    (fun z => u (clock l z.1, z.2)) t x

theorem pull_laplacian (a l : ℝ) (u : VelocityField) (t : ℝ) (x : Space) :
    spatialLaplacian (pull a l u) t x = (a * l ^ 2) • spatialLaplacian u (clock l t) (l • x) := by
  exact ViscosityScaling.rescale_laplacian a l
    (fun z => u (clock l z.1, z.2)) t x

theorem pull_gradient (a l : ℝ) (p : PressureField) (t : ℝ) (x : Space) :
    pressureGradient (pull a l p) t x = (a * l) • pressureGradient p (clock l t) (l • x) := by
  exact ViscosityScaling.rescale_gradient a l
    (fun z => p (clock l z.1, z.2)) t x

theorem pull_residual (ν l : ℝ) (u : VelocityField) (p : PressureField) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun s => u (s, l • x)) (clock l t)) :
    ProblemStatement.navierStokesResidual ν (pull l l u) (pull (l ^ 2) l p) t x =
      l ^ 3 • ProblemStatement.navierStokesResidual ν u p (clock l t) (l • x) := by
  have h1 : l * l ^ 2 = l ^ 3 := by ring
  have h2 : l ^ 2 * l = l ^ 3 := by ring
  have h3 : ν * l ^ 3 = l ^ 3 * ν := mul_comm _ _
  simp only [ProblemStatement.navierStokesResidual, pull_temporalDerivative _ _ _ _ _ hu,
    pull_advection, pull_laplacian, pull_gradient, smul_add, smul_sub, smul_smul, h1, h2, h3]

theorem residual_congr (ν : ℝ) {u v : VelocityField} {p q : PressureField} {z : SpaceTime}
    (hu : u =ᶠ[𝓝 z] v) (hp : p =ᶠ[𝓝 z] q) :
    ProblemStatement.navierStokesResidual ν u p z.1 z.2 =
      ProblemStatement.navierStokesResidual ν v q z.1 z.2 := by
  unfold ProblemStatement.navierStokesResidual
  rw [NavierStokes.ResidualRegularity.temporalDerivative_congr hu,
    NavierStokes.ResidualRegularity.advection_congr hu,
    NavierStokes.ResidualRegularity.spatialLaplacian_congr hu,
    NavierStokes.ResidualRegularity.pressureGradient_congr hp]

theorem zeroBefore_residual {ν : ℝ} {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K)
    (hrest : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, u (t, x) = 0 ∧ p (t, x) = 0)
    {t : ℝ} (ht : t < 1) (x : Space) :
    ProblemStatement.navierStokesResidual ν (zeroBefore u) (zeroBefore p) t x = f (t, x) := by
  by_cases ht0 : 0 < t
  · rw [residual_congr ν (z := (t, x))
      (zeroBefore_eventually_eq u ht0) (zeroBefore_eventually_eq p ht0)]
    exact hc.navier_stokes t ⟨ht0, ht⟩ x
  · rw [residual_congr ν (z := (t, x))
      (zeroBefore_eventually_zero (fun s hs y => (hrest s hs y).1) (le_of_not_gt ht0))
      (zeroBefore_eventually_zero (fun s hs y => (hrest s hs y).2) (le_of_not_gt ht0))]
    rw [hc.force_support.eq_zero_of_nonpos (le_of_not_gt ht0)]
    simp [ProblemStatement.navierStokesResidual, temporalDerivative, advection,
      spatialLaplacian, spatialDerivative, pressureGradient]

end NavierStokesR3.ParabolicScaling


end


/-! Merged from `NavierStokes.R3.ParabolicEnergy`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# Energy and blowup under an affine parabolic change of variables

The affine clock fixes time one.  Extension by zero before time zero lets a
uniform kinetic-energy bound pass through the change of variables on the
entire interval starting at zero.
-/

noncomputable section

namespace NavierStokesR3.ParabolicScaling

open ProblemStatement Set MeasureTheory

theorem velocity_energy_bounded {u : VelocityField} {l : ℝ}
    (hu : UniformFiniteEnergy (Ico 0 1) u) (hl : 1 < l) :
    UniformFiniteEnergy (Ico 0 1) (velocity l u) := by
  have hp : 0 < l := lt_trans zero_lt_one hl
  have htime : UniformFiniteEnergy (Ico 0 1)
      (fun z => zeroBefore u (clock l z.1, z.2)) := by
    obtain ⟨E, hE, hu⟩ := hu
    refine ⟨E, hE, ?_⟩
    intro t ht
    by_cases hc : 0 ≤ clock l t
    · simpa only [SquareIntegrableAtTime, kineticEnergy, zeroBefore,
        ite_eq_left hc] using hu (clock l t) ⟨hc, clock_lt_one hp ht.2⟩
    · constructor
      · simp [SquareIntegrableAtTime, zeroBefore, hc]
      · simpa [kineticEnergy, zeroBefore, hc] using hE
  exact htime.spatial_smul l l hp.ne'

theorem velocity_speed_unbounded {u : VelocityField} {l : ℝ}
    (hu : SpeedUnboundedAtOne u) (hl : 1 < l) :
    SpeedUnboundedAtOne (velocity l u) := by
  have hp : 0 < l := lt_trans zero_lt_one hl
  have hq : 0 < l ^ 2 := sq_pos_of_pos hp
  have hq1 : 1 ≤ l ^ 2 := by nlinarith
  intro M hM δ hδ
  obtain ⟨t, x, ht, hδt, hMtx⟩ := hu M hM δ hδ
  let s : ℝ := (t - 1) / l ^ 2 + 1
  have hs1 : s < 1 := by
    dsimp [s]
    have : (t - 1) / l ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith [ht.2]) hq
    linarith
  have hts : t ≤ s := by
    have hprod : (t - 1) * (l ^ 2 - 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith [ht.2]) (by linarith)
    have hd : t - 1 ≤ (t - 1) / l ^ 2 := (le_div_iff₀ hq).2 (by nlinarith)
    dsimp [s]
    linarith
  have hclock : clock l s = t := by
    dsimp [clock, s]
    field_simp
    ring
  refine ⟨s, l⁻¹ • x, ⟨lt_of_lt_of_le ht.1 hts, hs1⟩, lt_of_lt_of_le hδt hts, ?_⟩
  simp only [velocity, pull, hclock, smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
  rw [zeroBefore_eq_of_nonneg u ht.1.le, norm_smul, Real.norm_eq_abs, abs_of_pos hp]
  have hn : 0 ≤ ‖u (t, x)‖ := norm_nonneg _
  nlinarith

end NavierStokesR3.ParabolicScaling


end


noncomputable section

namespace NavierStokesR3.ParabolicScaling

open NavierStokes.ProblemStatement Set
open scoped ContDiff

theorem pull_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : SpaceTime → V} (hg : ContDiff ℝ ∞ g) (a l : ℝ) :
    ContDiff ℝ ∞ (pull a l g) := by
  exact (hg.comp (((contDiff_fst.sub contDiff_const).const_smul (l ^ 2)).add
    contDiff_const |>.prodMk (contDiff_snd.const_smul l))).const_smul a

theorem pull_smooth_on {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : SpaceTime → V} (hg : ContDiffOn ℝ ∞ g (Iio 1 ×ˢ univ))
    (a : ℝ) {l : ℝ} (hl : 0 < l) :
    ContDiffOn ℝ ∞ (pull a l g) (Iio 1 ×ˢ univ) := by
  apply (hg.comp ?_ ?_).const_smul a
  · exact (((contDiff_fst.sub contDiff_const).const_smul (l ^ 2)).add
      contDiff_const |>.prodMk (contDiff_snd.const_smul l)).contDiffOn
  · intro z hz
    exact ⟨clock_lt_one hl hz.1, mem_univ _⟩

theorem velocity_smooth {ν : ℝ} {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K)
    (hrest : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, u (t, x) = 0 ∧ p (t, x) = 0)
    {l : ℝ} (hl : 1 < l) :
    ContDiffOn ℝ ∞ (velocity l u) (Iio 1 ×ˢ univ) :=
  pull_smooth_on (zeroBefore_smooth_on hc.velocity_smooth
    (fun t ht x => (hrest t ht x).1)) l (by linarith)

theorem pressure_smooth {ν : ℝ} {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K)
    (hrest : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, u (t, x) = 0 ∧ p (t, x) = 0)
    {l : ℝ} (hl : 1 < l) :
    ContDiffOn ℝ ∞ (pressure l p) (Iio 1 ×ˢ univ) :=
  pull_smooth_on (zeroBefore_smooth_on hc.pressure_smooth
    (fun t ht x => (hrest t ht x).2)) (l ^ 2) (by linarith)

theorem zeroBefore_support {V : Type*} [Zero V] {g : SpaceTime → V} {K : Set Space}
    (hg : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x => g (t, x)) ⊆ K)
    {t : ℝ} (ht : t < 1) : tsupport (fun x => zeroBefore g (t, x)) ⊆ K := by
  by_cases ht0 : 0 ≤ t
  · simpa only [zeroBefore, ite_eq_left ht0] using hg t ⟨ht0, ht⟩
  · simp [zeroBefore, ht0]

theorem pull_zeroBefore_support {V : Type*} [Zero V] [SMulZeroClass ℝ V]
    {g : SpaceTime → V} {K : Set Space}
    (hg : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x => g (t, x)) ⊆ K)
    (a : ℝ) {l : ℝ} (hl : 0 < l) {t : ℝ} (ht : t < 1) :
    tsupport (fun x => pull a l (zeroBefore g) (t, x)) ⊆
      (fun x : Space => l⁻¹ • x) '' K :=
  ProblemStatement.tsupport_spatialScale_subset
    (zeroBefore_support hg (clock_lt_one hl ht)) a l hl.ne'

theorem velocity_support_before_one {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space} (hc : ProblemStatement.CandidateProperties ν u p f K)
    {l t : ℝ} (hl : 1 < l) (ht : t < 1) :
    tsupport (fun x => velocity l u (t, x)) ⊆ (fun x : Space => l⁻¹ • x) '' K :=
  pull_zeroBefore_support hc.velocity_support l (by linarith) ht

theorem pressure_support_before_one {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space} (hc : ProblemStatement.CandidateProperties ν u p f K)
    {l t : ℝ} (hl : 1 < l) (ht : t < 1) :
    tsupport (fun x => pressure l p (t, x)) ⊆ (fun x : Space => l⁻¹ • x) '' K :=
  pull_zeroBefore_support hc.pressure_support (l ^ 2) (by linarith) ht

theorem force_support {f : VelocityField} (hf : ProblemStatement.CompactPositiveTimeSupport f)
    {l : ℝ} (hl : 1 < l) : ProblemStatement.CompactPositiveTimeSupport (force l f) := by
  have hl0 : 0 < l := by linarith
  have hd : 1 - l ^ 2 ≤ 0 := by nlinarith
  have h := hf.affineScale (l ^ 3) l (l ^ 2) (1 - l ^ 2) hl0.ne'
    (sq_pos_of_pos hl0) hd
  have he : force l f = (fun z : SpaceTime => l ^ 3 • f (l ^ 2 * z.1 + (1 - l ^ 2), l • z.2)) := by
    funext z
    apply congrArg (fun s : ℝ => l ^ 3 • f (s, l • z.2))
    dsimp [clock]
    ring
  rw [he]
  exact h

/-- The precise delayed parabolic scaling used in the periodic corollary. -/
theorem compressedCandidate {ν : ℝ} {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K)
    (hrest : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, u (t, x) = 0 ∧ p (t, x) = 0)
    {l : ℝ} (hl : 1 < l) :
    ProblemStatement.CandidateProperties ν (velocity l u) (pressure l p) (force l f)
      ((fun x : Space => l⁻¹ • x) '' K) := by
  have hl0 : 0 < l := by linarith
  have hu := zeroBefore_smooth_on hc.velocity_smooth (fun t ht x => (hrest t ht x).1)
  refine {
    velocity_smooth := (velocity_smooth hc hrest hl).mono (fun z hz => ⟨hz.1.2, hz.2⟩)
    pressure_smooth := (pressure_smooth hc hrest hl).mono (fun z hz => ⟨hz.1.2, hz.2⟩)
    support_compact := ProblemStatement.isCompact_spatialScale_image hc.support_compact l
    velocity_support := fun t ht => velocity_support_before_one hc hl ht.2
    pressure_support := fun t ht => pressure_support_before_one hc hl ht.2
    force_smooth := pull_smooth hc.force_smooth _ _
    force_support := force_support hc.force_support hl
    zero_initial_velocity := ?_
    divergence_free := ?_
    navier_stokes := ?_
    energy_bounded := velocity_energy_bounded hc.energy_bounded hl
    speed_unbounded := velocity_speed_unbounded hc.speed_unbounded hl
  }
  · intro x
    change l • zeroBefore u (clock l 0, l • x) = 0
    rw [zeroBefore_eq_zero_of_nonpos (z := (clock l 0, l • x))
      (fun t ht y => (hrest t ht y).1) (clock_zero_nonpos hl.le), smul_zero]
  · intro t ht x
    rw [velocity, pull_divergence]
    by_cases hs : 0 ≤ clock l t
    · have he : (fun y => zeroBefore u (clock l t, y)) = fun y => u (clock l t, y) := by
        funext y; exact zeroBefore_eq_of_nonneg u hs
      simp only [spatialDivergence, spatialDerivative, he]
      change (l * l) * spatialDivergence u (clock l t) (l • x) = 0
      rw [hc.divergence_free _ ⟨hs, clock_lt_one hl0 ht.2⟩, mul_zero]
    · have he : (fun y => zeroBefore u (clock l t, y)) = fun _ => 0 := by
        funext y; exact zeroBefore_eq_zero_of_neg u (lt_of_not_ge hs)
      simp [spatialDivergence, spatialDerivative, he]
  · intro t ht x
    have htime : DifferentiableAt ℝ (fun s => zeroBefore u (s, l • x)) (clock l t) := by
      have hat := hu.contDiffAt (x := (clock l t, l • x)) ((isOpen_Iio.prod isOpen_univ).mem_nhds
        ⟨clock_lt_one hl0 ht.2, mem_univ (l • x)⟩)
      exact (hat.comp (clock l t) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    rw [velocity, pressure, pull_residual ν l _ _ t x htime,
      zeroBefore_residual hc hrest (clock_lt_one hl0 ht.2)]
    rfl

end NavierStokesR3.ParabolicScaling
end

/-! Merged from `NavierStokes.PeriodicPaperSupport` (in a section, so its `open`s cannot leak). -/
section
/-!
# Support of the periodic construction on its fundamental cube

The periodic lift is not compactly supported on all of R³. These lemmas
record the correct support statement after intersecting its topological
support with the closed fundamental cube. An extension after the singular
time is used only to make the periodizing lattice family uniformly locally finite.
-/

noncomputable section

namespace NavierStokes.PeriodicPaper

open ProblemStatement PeriodicLocalization Set Filter
open scoped Topology ContDiff

/-- The interior of the centered fundamental unit cube. -/
def fundamentalInterior : Set Space := {x | ∀ i : Fin 3, |x i| < 1 / 2}

/-- The closed centered fundamental unit cube. -/
def fundamentalCube : Set Space := {x | ∀ i : Fin 3, |x i| ≤ 1 / 2}

/-- An arbitrary zero extension after the singular time. -/
def beforeOne {V : Type*} [Zero V] (g : SpaceTime → V) (z : SpaceTime) : V :=
  if z.1 < 1 then g z else 0

theorem beforeOne_eq {V : Type*} [Zero V] (g : SpaceTime → V)
    {z : SpaceTime} (hz : z.1 < 1) : beforeOne g z = g z := by
  simp only [beforeOne, ite_eq_left hz]

theorem beforeOne_eventuallyEq {V : Type*} [Zero V] (g : SpaceTime → V)
    {z : SpaceTime} (hz : z.1 < 1) : beforeOne g =ᶠ[𝓝 z] g := by
  filter_upwards [continuous_fst.continuousAt.eventually_lt_const hz] with w hw
  exact beforeOne_eq g hw

theorem beforeOne_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : SpaceTime → V} (hg : ContDiffOn ℝ ∞ g preSingularDomain) :
    ContDiffOn ℝ ∞ (beforeOne g) preSingularDomain := by
  apply hg.congr
  intro z hz
  exact beforeOne_eq g hz.1.2

theorem beforeOne_supported {V : Type*} [NormedAddCommGroup V]
    {g : SpaceTime → V} {r : ℝ}
    (hg : ∀ t < (1 : ℝ), ∀ x : Space, g (t, x) ≠ 0 → ∀ i, |x i| ≤ r) :
    SupportedInCube r (beforeOne g) := by
  intro z hz
  by_cases ht : z.1 < 1
  · exact hg z.1 ht z.2 (by simpa only [beforeOne, ite_eq_left ht] using hz)
  · exact False.elim (hz (by simp only [beforeOne, ite_eq_right ht]))

/-- Lattice periodization preserves unbounded speed when the original
support is contained strictly within the fundamental cube. -/
theorem speedUnbounded_periodize {u : VelocityField} {r : ℝ}
    (hu : SupportedInCube r u) (hr : r < 1 / 2) (h : SpeedUnboundedAtOne u) :
    SpeedUnboundedAtOne (periodize u) := by
  intro M hM δ hδ
  obtain ⟨t, x, ht, hnear, hlarge⟩ := h M hM δ hδ
  have hne : u (t, x) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hlarge
    linarith
  have hx : ∀ i : Fin 3, |x i| ≤ 1 / 2 :=
    fun i => (hu (t, x) hne i).trans hr.le
  exact ⟨t, x, ht, hnear, by rwa [periodize_eq_on_unitCube hu hr hx]⟩

theorem speedUnbounded_beforeOne {u : VelocityField} (h : SpeedUnboundedAtOne u) :
    SpeedUnboundedAtOne (beforeOne u) := by
  intro M hM δ hδ
  obtain ⟨t, x, ht, hnear, hlarge⟩ := h M hM δ hδ
  exact ⟨t, x, ht, hnear, by rwa [beforeOne_eq u ht.2]⟩

/-- Inside the closed fundamental cube the support of the periodized field
is contained in the original compact set, including at cube boundary points. -/
theorem periodize_tsupport_on_fundamentalCube {V : Type*} [NormedAddCommGroup V]
    {g : SpaceTime → V} {r : ℝ} {K : Set Space}
    (hg : SupportedInCube r g) (hr : r < 1 / 2) {t : ℝ}
    (hK : tsupport (fun x : Space => g (t, x)) ⊆ K) :
    tsupport (fun x : Space => periodize g (t, x)) ∩ fundamentalCube ⊆ K := by
  rintro x ⟨hx, hcube⟩
  by_contra hnot
  have hnotg : x ∉ tsupport (fun y : Space => g (t, y)) := fun h => hnot (hK h)
  have hzero := notMem_tsupport_iff_eventuallyEq.mp hnotg
  have hinner : x ∈ innerCube r := by
    intro i
    have := hcube i
    linarith
  have heq : (fun y : Space => periodize g (t, y)) =ᶠ[𝓝 x]
      (fun y : Space => g (t, y)) := by
    filter_upwards [(isOpen_innerCube r).mem_nhds hinner] with y hy
    exact periodize_eq_on_innerCube hg hy t
  exact (notMem_tsupport_iff_eventuallyEq.mpr (heq.trans hzero)) hx

/-- Compact spacetime support gives a common future time endpoint. -/
theorem compactFutureTimeSupport_of_hasCompactSupport {f : VelocityField}
    (hf : HasCompactSupport f) : CompactFutureTimeSupport f := by
  obtain ⟨B, hB⟩ := (hf.image continuous_fst).bddAbove
  refine ⟨max B 0 + 1, by positivity, ?_⟩
  intro t ht x
  apply image_eq_zero_of_notMem_tsupport
  intro hz
  have hBt : t ≤ B := hB ⟨(t, x), hz, rfl⟩
  have := le_max_left B 0
  linarith

end NavierStokes.PeriodicPaper
end

/-! Merged from `NavierStokes.PeriodicViscosityUniqueness` (in a section, so its `open`s cannot leak). -/
section
/-!
# Periodic classical uniqueness for every positive viscosity

An inverse change of time and amplitude reduces the two solutions to the
already proved viscosity-one uniqueness theorem. Their spatial periods and
initial time agree throughout the reduction.
-/

noncomputable section

open Set
open scoped ContDiff

namespace NavierStokes.PeriodicViscosityUniqueness

open ProblemStatement PeriodicUniqueness ComparatorBridge

theorem normalized_time_mem_Icc {ν a b t : ℝ} (hν : 0 < ν)
    (ht : t ∈ Icc (ν * a) (ν * b)) : ν⁻¹ * t ∈ Icc a b := by
  constructor
  · simpa only [← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul] using
      mul_le_mul_of_nonneg_left ht.1 (inv_pos.mpr hν).le
  · simpa only [← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul] using
      mul_le_mul_of_nonneg_left ht.2 (inv_pos.mpr hν).le

theorem normalized_time_mem_Ioo {ν a b t : ℝ} (hν : 0 < ν)
    (ht : t ∈ Ioo (ν * a) (ν * b)) : ν⁻¹ * t ∈ Ioo a b := by
  constructor
  · simpa only [← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul] using
      mul_lt_mul_of_pos_left ht.1 (inv_pos.mpr hν)
  · simpa only [← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul] using
      mul_lt_mul_of_pos_left ht.2 (inv_pos.mpr hν)

theorem normalize_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ν a b : ℝ} (hν : 0 < ν) {g : SpaceTime → V}
    (hg : ContDiffOn ℝ ∞ g (slab a b)) (amplitude : ℝ) :
    ContDiffOn ℝ ∞ (rescale amplitude ν⁻¹ g) (slab (ν * a) (ν * b)) := by
  apply (hg.comp (s := slab (ν * a) (ν * b)) (t := slab a b)
    ((contDiff_fst.const_smul ν⁻¹).prodMk contDiff_snd).contDiffOn
    (fun z hz => ⟨normalized_time_mem_Icc hν hz.1, mem_univ _⟩)).const_smul amplitude

theorem normalize_periodic {V : Type*} [SMul ℝ V] {ν a b : ℝ}
    (hν : 0 < ν) {g : SpaceTime → V} (hg : UnitSpatialPeriodsOn (Icc a b) g)
    (amplitude : ℝ) :
    UnitSpatialPeriodsOn (Icc (ν * a) (ν * b)) (rescale amplitude ν⁻¹ g) := by
  intro t ht x i
  exact congrArg (fun y => amplitude • y) (hg _ (normalized_time_mem_Icc hν ht) x i)

theorem normalize_residual {ν : ℝ} (hν : 0 < ν)
    (u : VelocityField) (p : PressureField) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun s => u (s, x)) (ν⁻¹ * t)) :
    navierStokesResidual (rescale ν⁻¹ ν⁻¹ u) (rescale (ν⁻¹ ^ 2) ν⁻¹ p) t x =
      ν⁻¹ ^ 2 • NavierStokesR3.ProblemStatement.navierStokesResidual ν u p (ν⁻¹ * t) x := by
  have hcoef : ν⁻¹ * ν⁻¹ * ν = ν⁻¹ := by field_simp
  rw [navierStokesResidual, rescale_temporalDerivative _ _ _ _ _ hu,
    rescale_advection, rescale_laplacian, rescale_gradient]
  simp only [NavierStokesR3.ProblemStatement.navierStokesResidual,
    smul_add, smul_sub, smul_smul, hcoef, pow_two]

/-- Two smooth periodic solutions with the same force and initial datum agree
on a closed time interval, at every positive viscosity. -/
theorem classical_uniqueness_on_Icc {ν a b : ℝ} (hν : 0 < ν)
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
    (hNSu : ∀ t ∈ Ioo a b, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x))
    (hNSv : ∀ t ∈ Ioo a b, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν v q t x = f (t, x))
    (hinitial : ∀ x : Space, u (a, x) = v (a, x)) :
    ∀ t ∈ Icc a b, ∀ x : Space, u (t, x) = v (t, x) := by
  have heq := PeriodicUniqueness.classical_uniqueness_on_Icc
    (u := rescale ν⁻¹ ν⁻¹ u) (v := rescale ν⁻¹ ν⁻¹ v)
    (p := rescale (ν⁻¹ ^ 2) ν⁻¹ p) (q := rescale (ν⁻¹ ^ 2) ν⁻¹ q)
    (f := rescale (ν⁻¹ ^ 2) ν⁻¹ f)
    (normalize_smooth hν hu _) (normalize_smooth hν hv _)
    (normalize_smooth hν hp _) (normalize_smooth hν hq _)
    (normalize_periodic hν hpu _) (normalize_periodic hν hpv _)
    (normalize_periodic hν hpp _) (normalize_periodic hν hpq _) ?_ ?_ ?_ ?_ ?_
  · intro t ht x
    have hscaled := heq (ν * t)
      ⟨mul_le_mul_of_nonneg_left ht.1 hν.le, mul_le_mul_of_nonneg_left ht.2 hν.le⟩ x
    have h := congrArg (fun z : Space => ν • z) hscaled
    simpa [rescale, smul_smul, ← mul_assoc, hν.ne'] using h
  · intro t ht x
    rw [rescale_divergence, hdu _ (normalized_time_mem_Ioo hν ht), mul_zero]
  · intro t ht x
    rw [rescale_divergence, hdv _ (normalized_time_mem_Ioo hν ht), mul_zero]
  · intro t ht x
    rw [normalize_residual hν u p t x
      (time_differentiable_at_interior hu (normalized_time_mem_Ioo hν ht) x),
      hNSu _ (normalized_time_mem_Ioo hν ht)]
    rfl
  · intro t ht x
    rw [normalize_residual hν v q t x
      (time_differentiable_at_interior hv (normalized_time_mem_Ioo hν ht) x),
      hNSv _ (normalized_time_mem_Ioo hν ht)]
    rfl
  · intro x
    simp only [rescale, ← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul, hinitial]

end NavierStokes.PeriodicViscosityUniqueness
end

/-! Merged from `NavierStokes.PeriodicPaperScalingSupport`. -/
/-! # Support bounds for the compressed fields used on the torus -/

noncomputable section

namespace NavierStokes.PeriodicPaper

open ProblemStatement PeriodicLocalization Set

/-- The compressed velocity has the required coordinate bound at every
presingular time, including the negative-time extension used in the lattice sum. -/
theorem compressed_velocity_supported {ν l r : ℝ} {u f : VelocityField}
    {p : PressureField} {K : Set Space}
    (hc : NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K)
    (hl : 0 < l)
    (hK : ∀ x ∈ (fun y : Space => l⁻¹ • y) '' K, ∀ i, |x i| ≤ r) :
    ∀ t < (1 : ℝ), ∀ x : Space,
      NavierStokesR3.ParabolicScaling.velocity l u (t, x) ≠ 0 → ∀ i, |x i| ≤ r := by
  intro t ht x hne
  have hclock := NavierStokesR3.ParabolicScaling.clock_lt_one hl ht
  by_cases ht0 : 0 ≤ NavierStokesR3.ParabolicScaling.clock l t
  · have hu : u (NavierStokesR3.ParabolicScaling.clock l t, l • x) ≠ 0 := by
      intro hz
      apply hne
      simp only [NavierStokesR3.ParabolicScaling.velocity,
        NavierStokesR3.ParabolicScaling.pull,
        NavierStokesR3.ParabolicScaling.zeroBefore, ht0, ite_eq_left, hz, smul_zero]
    apply hK
    refine ⟨l • x, hc.velocity_support _ ⟨ht0, hclock⟩ (subset_tsupport _ hu), ?_⟩
    simp [smul_smul, hl.ne']
  · exfalso
    apply hne
    simp [NavierStokesR3.ParabolicScaling.velocity, NavierStokesR3.ParabolicScaling.pull,
      NavierStokesR3.ParabolicScaling.zeroBefore, ht0]

/-- Pressure has the same fixed coordinate support as the velocity. -/
theorem compressed_pressure_supported {ν l r : ℝ} {u f : VelocityField}
    {p : PressureField} {K : Set Space}
    (hc : NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K)
    (hl : 0 < l)
    (hK : ∀ x ∈ (fun y : Space => l⁻¹ • y) '' K, ∀ i, |x i| ≤ r) :
    ∀ t < (1 : ℝ), ∀ x : Space,
      NavierStokesR3.ParabolicScaling.pressure l p (t, x) ≠ 0 → ∀ i, |x i| ≤ r := by
  intro t ht x hne
  have hclock := NavierStokesR3.ParabolicScaling.clock_lt_one hl ht
  by_cases ht0 : 0 ≤ NavierStokesR3.ParabolicScaling.clock l t
  · have hp : p (NavierStokesR3.ParabolicScaling.clock l t, l • x) ≠ 0 := by
      intro hz
      apply hne
      simp only [NavierStokesR3.ParabolicScaling.pressure,
        NavierStokesR3.ParabolicScaling.pull,
        NavierStokesR3.ParabolicScaling.zeroBefore, ht0, ite_eq_left, hz, smul_zero]
    apply hK
    refine ⟨l • x, hc.pressure_support _ ⟨ht0, hclock⟩ (subset_tsupport _ hp), ?_⟩
    simp [smul_smul, hl.ne']
  · exfalso
    apply hne
    simp [NavierStokesR3.ParabolicScaling.pressure, NavierStokesR3.ParabolicScaling.pull,
      NavierStokesR3.ParabolicScaling.zeroBefore, ht0]

/-- The force has the coordinate support bound uniformly over all times. -/
theorem compressed_force_supported {l r : ℝ} {f : VelocityField}
    (hl : 0 < l)
    (hf : ∀ x ∈ (fun y : Space => l⁻¹ • y) '' (Prod.snd '' tsupport f),
      ∀ i, |x i| ≤ r) :
    SupportedInCube r (NavierStokesR3.ParabolicScaling.force l f) := by
  intro z hz
  have hne : f (NavierStokesR3.ParabolicScaling.clock l z.1, l • z.2) ≠ 0 := by
    intro hfzero
    apply hz
    simp only [NavierStokesR3.ParabolicScaling.force,
      NavierStokesR3.ParabolicScaling.pull, hfzero, smul_zero]
  apply hf
  refine ⟨l • z.2, ⟨(_, l • z.2), subset_tsupport _ hne, rfl⟩, ?_⟩
  simp [smul_smul, hl.ne']

/-- One spatial scaling factor simultaneously compresses the velocity,
pressure, and all spacetime slices of the force into the quarter cube. -/
theorem exists_compression_scale {ν : ℝ} {u f : VelocityField}
    {p : PressureField} {K : Set Space}
    (hc : NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K) :
    ∃ l : ℝ, 1 < l ∧
      (fun y : Space => l⁻¹ • y) '' K ⊆ fundamentalInterior ∧
      (∀ t < (1 : ℝ), ∀ x : Space,
        NavierStokesR3.ParabolicScaling.velocity l u (t, x) ≠ 0 →
          ∀ i, |x i| ≤ 1 / 4) ∧
      (∀ t < (1 : ℝ), ∀ x : Space,
        NavierStokesR3.ParabolicScaling.pressure l p (t, x) ≠ 0 →
          ∀ i, |x i| ≤ 1 / 4) ∧
      SupportedInCube (1 / 4) (NavierStokesR3.ParabolicScaling.force l f) := by
  have hcompact : IsCompact (K ∪ Prod.snd '' tsupport f) :=
    hc.support_compact.union (hc.force_support.1.image continuous_snd)
  obtain ⟨l, hl, hbound⟩ :=
    NavierStokesR3.ProblemStatement.exists_spatialScale_into_quarterCube hcompact
  have hlpos : 0 < l := lt_trans zero_lt_one hl
  have hK : ∀ x ∈ (fun y : Space => l⁻¹ • y) '' K, ∀ i, |x i| ≤ (1 / 4 : ℝ) := by
    intro x hx
    exact hbound x ((image_mono subset_union_left) hx)
  have hF : ∀ x ∈ (fun y : Space => l⁻¹ • y) '' (Prod.snd '' tsupport f),
      ∀ i, |x i| ≤ (1 / 4 : ℝ) := by
    intro x hx
    exact hbound x ((image_mono subset_union_right) hx)
  refine ⟨l, hl, ?_, compressed_velocity_supported hc hlpos hK,
    compressed_pressure_supported hc hlpos hK, compressed_force_supported hlpos hF⟩
  intro x hx i
  exact (hK x hx i).trans_lt (by norm_num)

end NavierStokes.PeriodicPaper


/-! Merged from `NavierStokes.PeriodicViscosity`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-!
# Global exclusion for positive-viscosity periodic solutions

Periodic classical uniqueness identifies any global competitor with a given
pre-singular solution on every compact interval before time one. Uniform
boundedness of the global competitor then contradicts unbounded speed.
-/

noncomputable section

open Set
open scoped ContDiff

namespace NavierStokes.PeriodicViscosity

open ProblemStatement

/-- A smooth periodic solution with unbounded speed at time one excludes every
global smooth periodic solution with the same positive viscosity, force and
zero initial datum. No kinetic-energy assumption is imposed on the competitor. -/
theorem excludes_global_solution {ν : ℝ} (hν : 0 < ν)
    {u v : VelocityField} {p q : PressureField} {f : VelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain)
    (hpu : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u)
    (hpp : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p)
    (huzero : ∀ x : Space, u (0, x) = 0)
    (hdu : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0)
    (hNSu : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x))
    (hblow : SpeedUnboundedAtOne u)
    (hv : ContDiffOn ℝ ∞ v futureDomain)
    (hq : ContDiffOn ℝ ∞ q futureDomain)
    (hpv : UnitSpatialPeriodsOn (Ici (0 : ℝ)) v)
    (hpq : UnitSpatialPeriodsOn (Ici (0 : ℝ)) q)
    (hvzero : ∀ x : Space, v (0, x) = 0)
    (hdv : ∀ t : ℝ, 0 ≤ t → ∀ x : Space, spatialDivergence v t x = 0)
    (hNSv : ∀ t : ℝ, 0 < t → ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν v q t x = f (t, x)) :
    False := by
  apply MaximalLifespan.unbounded_excludes_continuous_extension hblow
    (hv.continuousOn.mono (fun z hz => ⟨hz.1.1, hz.2⟩))
  · intro t ht x i
    exact hpv t ht.1 x i
  · intro t ht x
    have hsubu : PeriodicUniqueness.slab 0 t ⊆ preSingularDomain := by
      intro z hz
      exact ⟨⟨hz.1.1, hz.1.2.trans_lt ht.2⟩, hz.2⟩
    have hsubv : PeriodicUniqueness.slab 0 t ⊆ futureDomain := by
      intro z hz
      exact ⟨hz.1.1, hz.2⟩
    have hagree : ∀ r ∈ Icc (0 : ℝ) t, ∀ y : Space, u (r, y) = v (r, y) := by
      apply PeriodicViscosityUniqueness.classical_uniqueness_on_Icc hν
        (hu.mono hsubu) (hv.mono hsubv) (hp.mono hsubu) (hq.mono hsubv)
      · intro r hr y i
        exact hpu r ⟨hr.1, hr.2.trans_lt ht.2⟩ y i
      · intro r hr y i
        exact hpv r hr.1 y i
      · intro r hr y i
        exact hpp r ⟨hr.1, hr.2.trans_lt ht.2⟩ y i
      · intro r hr y i
        exact hpq r hr.1 y i
      · intro r hr y
        exact hdu r ⟨hr.1.le, hr.2.trans ht.2⟩ y
      · intro r hr y
        exact hdv r hr.1.le y
      · intro r hr y
        exact hNSu r ⟨hr.1, hr.2.trans ht.2⟩ y
      · intro r hr y
        exact hNSv r hr.1 y
      · intro y
        exact (huzero y).trans (hvzero y).symm
    exact hagree t ⟨ht.1, le_rfl⟩ x

end NavierStokes.PeriodicViscosity


end


noncomputable section

namespace NavierStokes.PeriodicPaper

open ProblemStatement PeriodicLocalization Set
open scoped ContDiff

/-- The same velocity, pressure, and force satisfy every assertion of the
periodic corollary before its singular time, which is exactly one. -/
structure CandidateProperties (ν : ℝ) (u : VelocityField) (p : PressureField)
    (f : VelocityField) (K : Set Space) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ u preSingularDomain
  pressure_smooth : ContDiffOn ℝ ∞ p preSingularDomain
  force_smooth : ContDiff ℝ ∞ f
  velocity_periodic : UnitSpatialPeriodsOn (Ico 0 1) u
  pressure_periodic : UnitSpatialPeriodsOn (Ico 0 1) p
  force_periodic : UnitSpatialPeriodsOn (Ici 0) f
  support_compact : IsCompact K
  support_interior : K ⊆ fundamentalInterior
  velocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => u (t, x)) ∩ fundamentalCube ⊆ K
  pressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => p (t, x)) ∩ fundamentalCube ⊆ K
  zero_initial_velocity : ∀ x : Space, u (0, x) = 0
  force_time_support : CompactFutureTimeSupport f
  force_zero_nonpos : ∀ t ≤ (0 : ℝ), ∀ x : Space, f (t, x) = 0
  divergence_free : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
    spatialDivergence u t x = 0
  navier_stokes : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x)
  speed_unbounded : SpeedUnboundedAtOne u

/-- A global smooth periodic competitor for precisely the prescribed force
and zero initial datum. No energy or pressure normalization is required. -/
structure GlobalSmoothSolution (ν : ℝ) (f : VelocityField) where
  velocity : VelocityField
  pressure : PressureField
  velocity_smooth : ContDiffOn ℝ ∞ velocity futureDomain
  pressure_smooth : ContDiffOn ℝ ∞ pressure futureDomain
  velocity_periodic : UnitSpatialPeriodsOn (Ici 0) velocity
  pressure_periodic : UnitSpatialPeriodsOn (Ici 0) pressure
  zero_initial_velocity : ∀ x : Space, velocity (0, x) = 0
  divergence_free : ∀ t ∈ Ici (0 : ℝ), ∀ x : Space,
    spatialDivergence velocity t x = 0
  navier_stokes : ∀ t ∈ Ioi (0 : ℝ), ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν velocity pressure t x = f (t, x)

/-- Every periodic candidate excludes a global smooth periodic competitor. -/
theorem CandidateProperties.no_global_solution {ν : ℝ} {u f : VelocityField}
    {p : PressureField} {K : Set Space} (h : CandidateProperties ν u p f K)
    (hν : 0 < ν) : ¬ Nonempty (GlobalSmoothSolution ν f) := by
  rintro ⟨v⟩
  exact PeriodicViscosity.excludes_global_solution hν
    h.velocity_smooth h.pressure_smooth h.velocity_periodic h.pressure_periodic
    h.zero_initial_velocity h.divergence_free h.navier_stokes h.speed_unbounded
    v.velocity_smooth v.pressure_smooth v.velocity_periodic v.pressure_periodic
    v.zero_initial_velocity v.divergence_free v.navier_stokes

/-- Every order of the ordinary spacetime derivative of the prescribed force
has arbitrary polynomial decay, as asserted in the periodic corollary proof. -/
theorem CandidateProperties.force_derivative_decay {ν : ℝ} {u f : VelocityField}
    {p : PressureField} {K : Set Space} (h : CandidateProperties ν u p f K)
    (m : ℕ) (N : ℝ) (hN : 0 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ‖iteratedFDeriv ℝ m f (t, x)‖ ≤ C * (1 + t) ^ (-N) := by
  obtain ⟨C, hC, hbound⟩ := CandidateConsequences.futureJet_decay
    h.force_smooth.contDiffOn h.force_periodic h.force_time_support m N hN
  refine ⟨C, hC, ?_⟩
  intro t ht x
  rw [← CandidateConsequences.futureJet_eq_full ht x m h.force_smooth.contDiffAt]
  exact hbound t ht x

/-- Periodize a compact whole-space candidate after its supports have been
compressed into the central quarter cube. The arbitrary post-one extensions
are discarded before forming the lattice sum. -/
theorem of_compact_candidate {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space} (h : NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K)
    (hK : K ⊆ fundamentalInterior)
    (hu : ∀ t < (1 : ℝ), ∀ x : Space, u (t, x) ≠ 0 → ∀ i, |x i| ≤ 1 / 4)
    (hp : ∀ t < (1 : ℝ), ∀ x : Space, p (t, x) ≠ 0 → ∀ i, |x i| ≤ 1 / 4)
    (hf : SupportedInCube (1 / 4) f) :
    CandidateProperties ν (periodize (beforeOne u)) (periodize (beforeOne p))
      (periodize f) K := by
  have hsu := beforeOne_supported hu
  have hsp := beforeOne_supported hp
  have hr : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  refine {
    velocity_smooth := contDiffOn_periodize hsu (beforeOne_smooth h.velocity_smooth)
    pressure_smooth := contDiffOn_periodize hsp (beforeOne_smooth h.pressure_smooth)
    force_smooth := contDiff_periodize hf h.force_smooth
    velocity_periodic := unitSpatialPeriodsOn_periodize _ _
    pressure_periodic := unitSpatialPeriodsOn_periodize _ _
    force_periodic := unitSpatialPeriodsOn_periodize _ _
    support_compact := h.support_compact
    support_interior := hK
    velocity_support := ?_
    pressure_support := ?_
    zero_initial_velocity := ?_
    force_time_support := compactFutureTimeSupport_periodize
      (compactFutureTimeSupport_of_hasCompactSupport h.force_support.1)
    force_zero_nonpos := ?_
    divergence_free := ?_
    navier_stokes := ?_
    speed_unbounded := speedUnbounded_periodize hsu hr
      (speedUnbounded_beforeOne h.speed_unbounded)
  }
  · intro t ht
    apply periodize_tsupport_on_fundamentalCube hsu hr
    simpa only [beforeOne, ht.2, ite_eq_left] using h.velocity_support t ht
  · intro t ht
    apply periodize_tsupport_on_fundamentalCube hsp hr
    simpa only [beforeOne, ht.2, ite_eq_left] using h.pressure_support t ht
  · intro x
    apply periodize_eq_zero_of_timeSlice
    intro y
    rw [beforeOne_eq u (by norm_num : (0 : ℝ) < 1)]
    exact h.zero_initial_velocity y
  · intro t ht x
    exact periodize_eq_zero_of_timeSlice (h.force_support.eq_zero_of_nonpos ht) x
  · apply divergence_free_periodize hsu hr
    intro t ht x
    rw [spatialDivergence_congr (beforeOne_eventuallyEq u (z := (t, x)) ht.2)]
    exact h.divergence_free t ht x
  · apply navier_stokes_periodize hsu hsp hf hr
    intro t ht x
    rw [residual_viscosity_congr ν (beforeOne_eventuallyEq u (z := (t, x)) ht.2)
      (beforeOne_eventuallyEq p (z := (t, x)) ht.2)]
    exact h.navier_stokes t ht x

/-- The full quantified periodic corollary, including support in the interior
of the fundamental cube and absence of a global smooth periodic solution. -/
def breakdownStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → ∃ u : VelocityField, ∃ p : PressureField,
    ∃ f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧ ¬ Nonempty (GlobalSmoothSolution ν f)

/-- The full periodic corollary is unconditional for every positive
viscosity. The affine parabolic clock preserves singular time exactly one. -/
theorem periodic_corollary : breakdownStatement := by
  intro ν hν
  obtain ⟨u, p, f, K, hc, _, hrest⟩ :=
    NavierStokesR3.theorem_1_1_with_initial_rest ν hν
  obtain ⟨l, hl, hK, hu, hp, hf⟩ := exists_compression_scale hc
  have hcompressed := NavierStokesR3.ParabolicScaling.compressedCandidate hc hrest hl
  have hperiodic := of_compact_candidate hcompressed hK hu hp hf
  exact ⟨_, _, _, _, hperiodic, hperiodic.no_global_solution hν⟩

end NavierStokes.PeriodicPaper

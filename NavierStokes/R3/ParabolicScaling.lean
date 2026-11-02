import NavierStokes.R3.ParabolicDefinitions
import NavierStokes.ResidualRegularity
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import NavierStokes.R3.ParabolicSupport

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

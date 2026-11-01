import NavierStokes.R3.H3Comparison
import NavierStokes.R3.SchwartzCompactApproximation
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Weak derivatives of L² fields and the curl of an arbitrary C¹ pressure
gradient. The pressure itself need not be integrable at infinity. -/

noncomputable section

open Set Filter MeasureTheory LineDeriv
open scoped ContDiff Topology BigOperators SchwartzMap LineDeriv

namespace NavierStokesR3.H3PressureDistribution

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness (spatial_partial_contDiff)
open H3Comparison

abbrev ComplexTest := SchwartzMap Space ℂ
abbrev ComplexL2 := Lp ℂ 2 (volume : Measure Space)
abbrev ComplexDistribution := TemperedDistribution Space ℂ

def distribution (f : ComplexL2) : ComplexDistribution := Lp.toTemperedDistribution f

theorem partial_continuous {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (i : Fin 3) :
    Continuous (spatialPartial i f) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- Compact support is required only of the first factor. -/
theorem compact_integration_by_parts {f g : Space → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hcf : HasCompactSupport f) (i : Fin 3) :
    (∫ x, f x * spatialPartial i g x) = -(∫ x, spatialPartial i f x * g x) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact ((partial_continuous hf i).mul hg.continuous).integrable_of_hasCompactSupport
      (hcf.fderiv_apply ℝ (coordinateVector i)).mul_right
  · exact (hf.continuous.mul (partial_continuous hg i)).integrable_of_hasCompactSupport
      hcf.mul_right
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hcf.mul_right
  · intro x _; exact hf.differentiable (by norm_num) x
  · intro x _; exact hg.differentiable (by norm_num) x




/-- Formula for a distributional derivative, using any L² representative. -/
theorem derivative_toLp_apply {f : Space → ℂ} (hf : MemLp f 2 volume)
    (i : Fin 3) (ψ : ComplexTest) :
    (∂_{coordinateVector i} (distribution (hf.toLp f))) ψ =
      -(∫ x, spatialPartial i (ψ : Space → ℂ) x * f x) := by
  rw [TemperedDistribution.lineDerivOp_apply_apply, distribution, Lp.toTemperedDistribution_apply]
  calc
    (∫ x : Space, (-∂_{coordinateVector i} ψ) x • (hf.toLp f) x) =
        ∫ x : Space, -(spatialPartial i (ψ : Space → ℂ) x * f x) := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]
      simp only [neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
        smul_eq_mul, neg_mul, spatialPartial]
    _ = _ := integral_neg _

/-- For a smooth compact function, the weak derivative is the ordinary one. -/
theorem derivative_toLp_of_compact {f : Space → ℂ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) (i : Fin 3) :
    ∂_{coordinateVector i} (distribution ((smooth_compact_memLp hf hcf).toLp f)) =
      distribution ((smooth_compact_memLp (spatial_partial_contDiff hf i)
        (hcf.fderiv_apply ℝ (coordinateVector i))).toLp (spatialPartial i f)) := by
  ext ψ
  rw [derivative_toLp_apply, distribution, Lp.toTemperedDistribution_apply]
  have he := compact_integration_by_parts (hf.of_le (by simp))
    ((ψ.smooth ⊤).of_le (by simp)) hcf i
  have hswap : (∫ x, spatialPartial i (ψ : Space → ℂ) x * f x) =
      -(∫ x, (ψ : Space → ℂ) x * spatialPartial i f x) := by
    simpa only [mul_comm] using he
  rw [hswap, neg_neg]
  apply integral_congr_ae
  filter_upwards [(smooth_compact_memLp (spatial_partial_contDiff hf i)
    (hcf.fderiv_apply ℝ (coordinateVector i))).coeFn_toLp] with x hx
  exact congrArg (fun z : ℂ => ψ x * z) hx.symm

/-- Passing the actual smooth approximation through continuous distributional
differentiation identifies the ordinary weak derivative. -/
theorem H1Approximation.derivative_distribution {f : Space → ℂ}
    {df : Fin 3 → Space → ℂ} (h : H1Approximation f df) (i : Fin 3) :
    ∂_{coordinateVector i} (distribution (h.memLp.toLp f)) =
      distribution ((h.derivative_memLp i).toLp (df i)) := by
  let T : ComplexL2 →L[ℂ] ComplexDistribution := Lp.toTemperedDistributionCLM ℂ volume 2
  have hl := ((lineDerivOpCLM ℂ ComplexDistribution (coordinateVector i)).continuous.comp
    T.continuous).tendsto _ |>.comp h.tendsto
  have hr := T.continuous.tendsto _ |>.comp (h.derivative_tendsto i)
  have he (n : ℕ) :
      ∂_{coordinateVector i} (T ((h.approx_memLp n).toLp (h.approx n))) =
        T ((h.derivative_approx_memLp n i).toLp (spatialPartial i (h.approx n))) :=
    derivative_toLp_of_compact (h.smooth n) (h.compact n) i
  exact tendsto_nhds_unique (hl.congr (fun n => he n)) hr


end NavierStokesR3.H3PressureDistribution

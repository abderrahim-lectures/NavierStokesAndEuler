import NavierStokes.PeriodicSobolev
import NavierStokes.R3.ProblemStatement
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Group.Integral
import NavierStokes.R3.H3Approximation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import NavierStokes.R3.CompactTimeIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import NavierStokes.R3.ViscousEnergyBalance
import NavierStokes.R3.H3Products
import NavierStokes.R3.ComparisonGronwall
import NavierStokes.R3.H3Comparison
import NavierStokes.R3.SchwartzCompactApproximation
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import NavierStokes.R3.WeakFourierUniqueness
import Mathlib.Analysis.Fourier.LpSpace
import NavierStokes.R3.CompactComparisonBounds
import NavierStokes.R3.Theorem

/-! # Exact maximal classical H³ lifespan on ℝ³

The solution class uses genuine weak H³ jets with their L² topology, actual
L² time differentiation, and the same forcing and initial velocity. No
periodicity or pressure normalization is imposed on competing solutions.
-/
/-! Merged from `NavierStokes.R3.H3Definitions`. -/
/-! # Derivative H³ norms on Euclidean three-space

All integrals in this file use Lebesgue measure on the whole of `ℝ³`.
The positive multiplicities of the eight mixed derivatives agree with the
existing periodic derivative norm and define an equivalent H³ norm.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NavierStokesR3.H3Embedding

open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration

def squareEnergy (f : Space → Space) : ℝ := ∫ x, ‖f x‖ ^ 2

def mixedEnergy (f : Space → Space) : ℝ :=
  squareEnergy f +
  squareEnergy (spatialPartial 0 f) +
  squareEnergy (spatialPartial 1 f) +
  squareEnergy (spatialPartial 2 f) +
  squareEnergy (spatialPartial 1 (spatialPartial 0 f)) +
  squareEnergy (spatialPartial 2 (spatialPartial 0 f)) +
  squareEnergy (spatialPartial 2 (spatialPartial 1 f)) +
  squareEnergy (spatialPartial 2 (spatialPartial 1 (spatialPartial 0 f)))

/-- Every ordered coordinate derivative of order at most three is included. -/
def derivativeH3Energy (f : Space → Space) : ℝ :=
  mixedEnergy f +
    (∑ i : Fin 3, ∑ j : Fin 3,
      squareEnergy (spatialPartial i (spatialPartial j f))) +
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      squareEnergy (spatialPartial i (spatialPartial j (spatialPartial k f))))

def derivativeH3Norm (f : Space → Space) : ℝ := Real.sqrt (derivativeH3Energy f)

/-- Genuine square integrability, to exclude the totalized-integral convention
for a nonintegrable derivative. -/
def HasFiniteH3 (f : Space → Space) : Prop :=
  Integrable (fun x => ‖f x‖ ^ 2) ∧
    (∀ i, Integrable (fun x => ‖spatialPartial i f x‖ ^ 2)) ∧
    (∀ i j, Integrable (fun x => ‖spatialPartial i (spatialPartial j f) x‖ ^ 2)) ∧
    (∀ i j k, Integrable
      (fun x => ‖spatialPartial i (spatialPartial j (spatialPartial k f)) x‖ ^ 2))

theorem squareEnergy_nonneg (f : Space → Space) : 0 ≤ squareEnergy f :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem mixedEnergy_nonneg (f : Space → Space) : 0 ≤ mixedEnergy f := by
  unfold mixedEnergy
  repeat' apply add_nonneg
  all_goals exact squareEnergy_nonneg _

theorem mixedEnergy_le_derivativeH3Energy (f : Space → Space) :
    mixedEnergy f ≤ derivativeH3Energy f := by
  have h2 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      squareEnergy (spatialPartial i (spatialPartial j f)) := by
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => squareEnergy_nonneg _))
  have h3 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      squareEnergy (spatialPartial i (spatialPartial j (spatialPartial k f))) := by
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
      (fun _ _ => Finset.sum_nonneg (fun _ _ => squareEnergy_nonneg _)))
  unfold derivativeH3Energy
  linarith

theorem derivativeH3Energy_nonneg (f : Space → Space) : 0 ≤ derivativeH3Energy f :=
  (mixedEnergy_nonneg f).trans (mixedEnergy_le_derivativeH3Energy f)

theorem derivativeH3Norm_nonneg (f : Space → Space) : 0 ≤ derivativeH3Norm f :=
  Real.sqrt_nonneg _

end NavierStokesR3.H3Embedding

/-! Merged from `NavierStokes.R3.H3WeakEmbedding`. -/
/-! # Sobolev embedding for genuine weak H³ fields

The estimate is passed through a smooth compact approximation in L² of all
weak jets. No classical derivatives of the limiting field are used.
-/
/-! Merged from `NavierStokes.R3.H3Embedding`. -/
/-! # The whole-space H³ supremum estimate

The unit-cube fundamental-theorem-of-calculus estimate is applied after
translation to an arbitrary point. Each local derivative integral is bounded
by its genuine Lebesgue integral over all of ℝ³.
-/

/-! Merged from `NavierStokes.R3.H3BoxIntegral`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

noncomputable section

open Set MeasureTheory

namespace NavierStokesR3.H3Embedding

open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration

private def unitMeasure : Measure ℝ := volume.restrict (Icc 0 1)

private instance : IsFiniteMeasure unitMeasure := by
  unfold unitMeasure
  infer_instance

private theorem unitPi_eq (n : ℕ) :
    Measure.pi (fun _ : Fin n => unitMeasure) = volume.restrict (Icc 0 1) := by
  unfold unitMeasure
  rw [← Measure.restrict_pi_pi]
  congr 1
  ext x
  simp [Set.mem_Icc, Pi.le_def]

private theorem integrable_unitPi {n : ℕ} {g : (Fin n → ℝ) → ℝ}
    (hg : Continuous g) : Integrable g (Measure.pi (fun _ : Fin n => unitMeasure)) := by
  rw [unitPi_eq]
  exact hg.integrableOn_Icc

/-- The iterated coordinate integral used by the elementary FTC proof is
exactly the ordinary product-volume integral on the cube. -/
theorem boxIntegral_eq_cubeIntegral {h : Space → ℝ} (hh : Continuous h) :
    NavierStokes.PeriodicSobolev.boxIntegral h = cubeIntegral h := by
  have hi := integrable_unitPi (hh.comp toSpace.continuous)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => unitMeasure) 0).symm
  have hei : Integrable (fun z : ℝ × (Fin 2 → ℝ) => h (toSpace (e.symm z)))
      (unitMeasure.prod (Measure.pi (fun _ : Fin 2 => unitMeasure))) := by
    exact (he.integrable_comp_emb e.symm.measurableEmbedding).2 hi
  have h2 (a : ℝ) : Integrable (fun y : Fin 2 → ℝ => h (toSpace (Fin.cons a y)))
      (Measure.pi (fun _ : Fin 2 => unitMeasure)) := by
    apply integrable_unitPi
    apply hh.comp
    apply toSpace.continuous.comp
    fun_prop
  have h2e := (measurePreserving_piFinTwo (fun _ : Fin 2 => unitMeasure)).symm
  have h2i (a : ℝ) : Integrable (fun z : ℝ × ℝ => h (toSpace ![a, z.1, z.2]))
      (unitMeasure.prod unitMeasure) := by
    exact (h2e.integrable_comp_emb
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).symm.measurableEmbedding).2 (h2 a)
  symm
  calc
    cubeIntegral h = ∫ y : Fin 3 → ℝ, h (toSpace y)
        ∂Measure.pi (fun _ : Fin 3 => unitMeasure) := by
      rw [unitPi_eq]
      rfl
    _ = ∫ z : ℝ × (Fin 2 → ℝ), h (toSpace (e.symm z))
        ∂unitMeasure.prod (Measure.pi (fun _ : Fin 2 => unitMeasure)) :=
      (he.integral_comp' (fun y => h (toSpace y))).symm
    _ = ∫ a, (∫ y : Fin 2 → ℝ, h (toSpace (Fin.cons a y))
        ∂Measure.pi (fun _ : Fin 2 => unitMeasure)) ∂unitMeasure := by
      rw [integral_prod _ hei]
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq]
    _ = ∫ a, (∫ z : ℝ × ℝ, h (toSpace ![a, z.1, z.2])
        ∂unitMeasure.prod unitMeasure) ∂unitMeasure := by
      apply integral_congr_ae
      filter_upwards with a
      exact (h2e.integral_comp' (fun y : Fin 2 → ℝ => h (toSpace (Fin.cons a y)))).symm
    _ = NavierStokes.PeriodicSobolev.boxIntegral h := by
      apply integral_congr_ae
      filter_upwards with a
      exact integral_prod _ (h2i a)

/-- A nonnegative box integral is at most the integral on all of ℝ³. -/
theorem boxIntegral_le_integral {h : Space → ℝ} (hh : Continuous h)
    (hi : Integrable h) (hn : ∀ x, 0 ≤ h x) :
    NavierStokes.PeriodicSobolev.boxIntegral h ≤ ∫ x, h x := by
  rw [boxIntegral_eq_cubeIntegral hh]
  have he : MeasurePreserving toSpace volume volume := PiLp.volume_preserving_toLp (Fin 3)
  have hei : Integrable (fun y : Coords => h (toSpace y)) :=
    (he.integrable_comp_emb toSpace.toHomeomorph.measurableEmbedding).2 hi
  calc
    cubeIntegral h ≤ ∫ y : Coords, h (toSpace y) :=
      integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall (fun y => hn (toSpace y))) hei
    _ = ∫ x, h x := he.integral_comp toSpace.toHomeomorph.measurableEmbedding h

end NavierStokesR3.H3Embedding


end


noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NavierStokesR3.H3Embedding

open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration

theorem spatialPartial_translate (i : Fin 3) (f : Space → Space) (a : Space) :
    spatialPartial i (fun x => f (x + a)) = fun x => spatialPartial i f (x + a) := by
  funext x
  exact congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector i))
    (fderiv_comp_add_right a)

theorem squareEnergy_translate (f : Space → Space) (a : Space) :
    squareEnergy (fun x => f (x + a)) = squareEnergy f :=
  integral_add_right_eq_self (fun x => ‖f x‖ ^ 2) a

theorem mixedEnergy_translate (f : Space → Space) (a : Space) :
    mixedEnergy (fun x => f (x + a)) = mixedEnergy f := by
  simp only [mixedEnergy, spatialPartial_translate, squareEnergy_translate]

theorem HasFiniteH3.translate {f : Space → Space} (h : HasFiniteH3 f) (a : Space) :
    HasFiniteH3 (fun x => f (x + a)) := by
  have hi {g : Space → ℝ} (hg : Integrable g) : Integrable (fun x => g (x + a)) :=
    ((measurePreserving_add_right volume a).integrable_comp hg.aestronglyMeasurable).2 hg
  refine ⟨hi h.1, ?_, ?_, ?_⟩
  · intro i
    simpa only [spatialPartial_translate] using hi (h.2.1 i)
  · intro i j
    simpa only [spatialPartial_translate] using hi (h.2.2.1 i j)
  · intro i j k
    simpa only [spatialPartial_translate] using hi (h.2.2.2 i j k)

theorem cubeMixedEnergy_le_mixedEnergy {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hi : HasFiniteH3 f) :
    NavierStokes.PeriodicSobolev.mixedEnergy f ≤ mixedEnergy f := by
  have hd (g : Space → Space) (hg : ContDiff ℝ ∞ g) (i : Fin 3) :=
    NavierStokes.PeriodicUniqueness.spatial_partial_contDiff hg i
  have h0 := hd f hf 0
  have h1 := hd f hf 1
  have h2 := hd f hf 2
  have h10 := hd _ h0 1
  have h20 := hd _ h0 2
  have h21 := hd _ h1 2
  have h210 := hd _ h10 2
  have hb {g : Space → Space} (hg : Continuous g)
      (hgi : Integrable (fun x => ‖g x‖ ^ 2)) :
      NavierStokes.PeriodicSobolev.boxIntegral
        (NavierStokes.PeriodicSobolev.sqField g) ≤ squareEnergy g :=
    boxIntegral_le_integral (hg.norm.pow 2) hgi (fun x => sq_nonneg _)
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (hb hf.continuous hi.1) (hb h0.continuous (hi.2.1 0)))
    (hb h1.continuous (hi.2.1 1))) (hb h2.continuous (hi.2.1 2)))
    (hb h10.continuous (hi.2.2.1 1 0))) (hb h20.continuous (hi.2.2.1 2 0)))
    (hb h21.continuous (hi.2.2.1 2 1))) (hb h210.continuous (hi.2.2.2 2 1 0))

/-- H³(ℝ³) controls the value at every spatial point, with a universal
constant independent of the support or of the chosen point. -/
theorem norm_sq_le_eight_derivativeH3Energy {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hi : HasFiniteH3 f) (x : Space) :
    ‖f x‖ ^ 2 ≤ 8 * derivativeH3Energy f := by
  have hs : ContDiff ℝ ∞ (fun y => f (y + x)) :=
    hf.comp (contDiff_id.add contDiff_const)
  have hlocal := NavierStokes.PeriodicSobolev.norm_sq_le_eight_mixedEnergy_on_cube hs 0
    (fun _ => by simp)
  have hglobal := cubeMixedEnergy_le_mixedEnergy hs (hi.translate x)
  rw [mixedEnergy_translate] at hglobal
  have hm := mixedEnergy_le_derivativeH3Energy f
  simpa only [zero_add] using hlocal.trans (mul_le_mul_of_nonneg_left
    (hglobal.trans hm) (by norm_num : (0 : ℝ) ≤ 8))

/-- A convenient linear form of the whole-space Sobolev bound. -/
theorem norm_le_three_derivativeH3Norm {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hi : HasFiniteH3 f) (x : Space) :
    ‖f x‖ ≤ 3 * derivativeH3Norm f := by
  have he := norm_sq_le_eight_derivativeH3Energy hf hi x
  have hn := derivativeH3Norm_nonneg f
  have hs : derivativeH3Norm f ^ 2 = derivativeH3Energy f :=
    Real.sq_sqrt (derivativeH3Energy_nonneg f)
  nlinarith [derivativeH3Energy_nonneg f]

end NavierStokesR3.H3Embedding


noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace BigOperators

namespace NavierStokesR3.H3Embedding

open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open H3Comparison

def weakH3Energy (f : Space → Space) (df : Fin 3 → Space → Space)
    (ddf : Fin 3 → Fin 3 → Space → Space)
    (dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space) : ℝ :=
  squareEnergy f + squareEnergy (df 0) + squareEnergy (df 1) + squareEnergy (df 2) +
    squareEnergy (ddf 1 0) + squareEnergy (ddf 2 0) + squareEnergy (ddf 2 1) +
    squareEnergy (dddf 2 1 0) + (∑ i, ∑ j, squareEnergy (ddf i j)) +
    (∑ i, ∑ j, ∑ k, squareEnergy (dddf i j k))

def weakH3Norm (f : Space → Space) (df : Fin 3 → Space → Space)
    (ddf : Fin 3 → Fin 3 → Space → Space)
    (dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space) : ℝ :=
  Real.sqrt (weakH3Energy f df ddf dddf)

theorem weakH3Energy_nonneg (f : Space → Space) (df : Fin 3 → Space → Space)
    (ddf : Fin 3 → Fin 3 → Space → Space)
    (dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space) :
    0 ≤ weakH3Energy f df ddf dddf := by
  have h2 : 0 ≤ ∑ i, ∑ j, squareEnergy (ddf i j) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => squareEnergy_nonneg _))
  have h3 : 0 ≤ ∑ i, ∑ j, ∑ k, squareEnergy (dddf i j k) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => squareEnergy_nonneg _)))
  unfold weakH3Energy
  apply add_nonneg (add_nonneg _ h2) h3
  repeat' apply add_nonneg
  all_goals exact squareEnergy_nonneg _

theorem squareEnergy_eq_norm_toLp {f : Space → Space} (hf : MemLp f 2 volume) :
    squareEnergy f = ‖hf.toLp f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem squareEnergy_tendsto_of_toLp {f : ℕ → Space → Space} {g : Space → Space}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (ht : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g))) :
    Tendsto (fun n => squareEnergy (f n)) atTop (𝓝 (squareEnergy g)) := by
  have he : (fun n => squareEnergy (f n)) = fun n => ‖(hf n).toLp (f n)‖ ^ 2 :=
    funext (fun n => squareEnergy_eq_norm_toLp (hf n))
  rw [he, squareEnergy_eq_norm_toLp hg]
  exact ht.norm.pow 2

theorem approximation_energy_tendsto {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) :
    Tendsto (fun n => derivativeH3Energy (h.approx n)) atTop
      (𝓝 (weakH3Energy f df ddf dddf)) := by
  have h0 := squareEnergy_tendsto_of_toLp h.approx_memLp h.memLp h.tendsto
  have h1 (i) := squareEnergy_tendsto_of_toLp (fun n => h.derivative_approx_memLp n i)
    (h.derivative_memLp i) (h.derivative_tendsto i)
  have h2 (i j) := squareEnergy_tendsto_of_toLp (fun n => h.second_approx_memLp n i j)
    (h.second_memLp i j) (h.second_tendsto i j)
  have h3 (i j k) := squareEnergy_tendsto_of_toLp (fun n => h.third_approx_memLp n i j k)
    (h.third_memLp i j k) (h.third_tendsto i j k)
  apply ((((((((h0.add (h1 0)).add (h1 1)).add (h1 2)).add (h2 1 0)).add
    (h2 2 0)).add (h2 2 1)).add (h3 2 1 0)).add ?_).add ?_
  · exact tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ => h2 i j))
  · exact tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ =>
      tendsto_finsetSum _ (fun k _ => h3 i j k)))

theorem approximation_finiteH3 {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) (n : ℕ) : HasFiniteH3 (h.approx n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (memLp_two_iff_integrable_sq_norm (h.approx_memLp n).aestronglyMeasurable).1
      (h.approx_memLp n)
  · intro i
    exact (memLp_two_iff_integrable_sq_norm
      (h.derivative_approx_memLp n i).aestronglyMeasurable).1 (h.derivative_approx_memLp n i)
  · intro i j
    exact (memLp_two_iff_integrable_sq_norm
      (h.second_approx_memLp n i j).aestronglyMeasurable).1 (h.second_approx_memLp n i j)
  · intro i j k
    exact (memLp_two_iff_integrable_sq_norm
      (h.third_approx_memLp n i j k).aestronglyMeasurable).1 (h.third_approx_memLp n i j k)

/-- The whole-space Sobolev estimate for almost every value of any weak H³
representative. -/
theorem ae_norm_sq_le_weakH3Energy {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) :
    ∀ᵐ x ∂volume, ‖f x‖ ^ 2 ≤ 8 * weakH3Energy f df ddf dddf := by
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp h.tendsto).exists_seq_tendsto_ae
  have ha : ∀ᵐ x ∂volume, ∀ n, (h.approx_memLp (ns n)).toLp (h.approx (ns n)) x =
      h.approx (ns n) x :=
    ae_all_iff.2 (fun n => (h.approx_memLp (ns n)).coeFn_toLp)
  filter_upwards [hae, ha, h.memLp.coeFn_toLp] with x hx hax hfx
  have ht : Tendsto (fun n => h.approx (ns n) x) atTop (𝓝 (f x)) := by
    simpa only [hax, hfx] using hx
  have hen := (approximation_energy_tendsto h).comp hns.tendsto_atTop
  exact le_of_tendsto_of_tendsto (ht.norm.pow 2) (tendsto_const_nhds.mul hen)
    (Filter.Eventually.of_forall (fun n =>
      norm_sq_le_eight_derivativeH3Energy (h.smooth (ns n)) (approximation_finiteH3 h (ns n)) x))

/-- A continuous representative of a weak H³ field satisfies the Sobolev
bound at every point. -/
theorem norm_sq_le_weakH3Energy {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) (hf : Continuous f) (x : Space) :
    ‖f x‖ ^ 2 ≤ 8 * weakH3Energy f df ddf dddf := by
  have hc : IsClosed {x | ‖f x‖ ^ 2 ≤ 8 * weakH3Energy f df ddf dddf} :=
    isClosed_le (hf.norm.pow 2) continuous_const
  have heq := hc.ae_eq_univ_iff_eq.mp (show
      {x | ‖f x‖ ^ 2 ≤ 8 * weakH3Energy f df ddf dddf} =ᵐ[volume] univ from by
    filter_upwards [ae_norm_sq_le_weakH3Energy h] with y hy
    exact propext ⟨fun _ => mem_univ y, fun _ => hy⟩)
  change x ∈ {x | ‖f x‖ ^ 2 ≤ 8 * weakH3Energy f df ddf dddf}
  rw [heq]
  exact mem_univ _

theorem norm_le_weakH3Norm {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) (hf : Continuous f) (x : Space) :
    ‖f x‖ ≤ 3 * weakH3Norm f df ddf dddf := by
  have he := norm_sq_le_weakH3Energy h hf x
  have hn : 0 ≤ weakH3Norm f df ddf dddf := Real.sqrt_nonneg _
  have hs : weakH3Norm f df ddf dddf ^ 2 = weakH3Energy f df ddf dddf :=
    Real.sq_sqrt (weakH3Energy_nonneg f df ddf dddf)
  nlinarith [weakH3Energy_nonneg f df ddf dddf]

end NavierStokesR3.H3Embedding

/-! Merged from `NavierStokes.R3.H3UniformApproximation`. -/
/-! Merged from `NavierStokes.R3.H3Operations`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace NavierStokesR3.H3Comparison

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness (spatial_partial_contDiff)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem spatialPartial_sub_smooth {f g : Space → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : Fin 3) :
    spatialPartial i (f - g) = spatialPartial i f - spatialPartial i g := by
  funext x
  exact congrArg (fun L : Space →L[ℝ] E => L (coordinateVector i))
    (fderiv_sub (hf.differentiable (by simp) x) (hg.differentiable (by simp) x))

theorem spatialPartial_two_sub_smooth {f g : Space → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i j : Fin 3) :
    spatialPartial i (spatialPartial j (f - g)) =
      spatialPartial i (spatialPartial j f) - spatialPartial i (spatialPartial j g) := by
  rw [spatialPartial_sub_smooth hf hg j]
  exact spatialPartial_sub_smooth (spatial_partial_contDiff hf j)
    (spatial_partial_contDiff hg j) i

theorem spatialPartial_three_sub_smooth {f g : Space → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i j k : Fin 3) :
    spatialPartial i (spatialPartial j (spatialPartial k (f - g))) =
      spatialPartial i (spatialPartial j (spatialPartial k f)) -
        spatialPartial i (spatialPartial j (spatialPartial k g)) := by
  rw [spatialPartial_two_sub_smooth hf hg j k]
  exact spatialPartial_sub_smooth
    (spatial_partial_contDiff (spatial_partial_contDiff hf k) j)
    (spatial_partial_contDiff (spatial_partial_contDiff hg k) j) i

def H1Approximation.sub {f g : Space → E} {df dg : Fin 3 → Space → E}
    (hf : H1Approximation f df) (hg : H1Approximation g dg) :
    H1Approximation (f - g) (df - dg) where
  memLp := hf.memLp.sub hg.memLp
  derivative_memLp := fun i => (hf.derivative_memLp i).sub (hg.derivative_memLp i)
  approx := fun n => hf.approx n - hg.approx n
  smooth := fun n => (hf.smooth n).sub (hg.smooth n)
  compact := fun n => (hf.compact n).sub (hg.compact n)
  approx_memLp := fun n => (hf.approx_memLp n).sub (hg.approx_memLp n)
  derivative_approx_memLp := fun n i => by
    rw [spatialPartial_sub_smooth (hf.smooth n) (hg.smooth n)]
    exact (hf.derivative_approx_memLp n i).sub (hg.derivative_approx_memLp n i)
  tendsto := by
    simpa only [MemLp.toLp_sub hf.memLp hg.memLp,
      MemLp.toLp_sub (hf.approx_memLp _) (hg.approx_memLp _)] using hf.tendsto.sub hg.tendsto
  derivative_tendsto := fun i => by
    simpa only [spatialPartial_sub_smooth (hf.smooth _) (hg.smooth _), Pi.sub_apply,
      MemLp.toLp_sub (hf.derivative_memLp i) (hg.derivative_memLp i),
      MemLp.toLp_sub (hf.derivative_approx_memLp _ i) (hg.derivative_approx_memLp _ i)] using
      (hf.derivative_tendsto i).sub (hg.derivative_tendsto i)

def H3Approximation.sub {f g : Space → E} {df dg : Fin 3 → Space → E}
    {ddf ddg : Fin 3 → Fin 3 → Space → E}
    {dddf dddg : Fin 3 → Fin 3 → Fin 3 → Space → E}
    (hf : H3Approximation f df ddf dddf) (hg : H3Approximation g dg ddg dddg) :
    H3Approximation (f - g) (df - dg) (ddf - ddg) (dddf - dddg) where
  toH1Approximation := hf.toH1Approximation.sub hg.toH1Approximation
  second_memLp := fun i j => (hf.second_memLp i j).sub (hg.second_memLp i j)
  third_memLp := fun i j k => (hf.third_memLp i j k).sub (hg.third_memLp i j k)
  second_approx_memLp := fun n i j => by
    change MemLp (spatialPartial i (spatialPartial j (hf.approx n - hg.approx n))) 2 volume
    rw [spatialPartial_two_sub_smooth (hf.smooth n) (hg.smooth n)]
    exact (hf.second_approx_memLp n i j).sub (hg.second_approx_memLp n i j)
  third_approx_memLp := fun n i j k => by
    change MemLp (spatialPartial i (spatialPartial j (spatialPartial k
      (hf.approx n - hg.approx n)))) 2 volume
    rw [spatialPartial_three_sub_smooth (hf.smooth n) (hg.smooth n)]
    exact (hf.third_approx_memLp n i j k).sub (hg.third_approx_memLp n i j k)
  second_tendsto := fun i j => by
    simpa only [H1Approximation.sub, spatialPartial_two_sub_smooth (hf.smooth _) (hg.smooth _),
      Pi.sub_apply, MemLp.toLp_sub (hf.second_memLp i j) (hg.second_memLp i j),
      MemLp.toLp_sub (hf.second_approx_memLp _ i j) (hg.second_approx_memLp _ i j)] using
      (hf.second_tendsto i j).sub (hg.second_tendsto i j)
  third_tendsto := fun i j k => by
    simpa only [H1Approximation.sub, spatialPartial_three_sub_smooth (hf.smooth _) (hg.smooth _),
      Pi.sub_apply, MemLp.toLp_sub (hf.third_memLp i j k) (hg.third_memLp i j k),
      MemLp.toLp_sub (hf.third_approx_memLp _ i j k) (hg.third_approx_memLp _ i j k)] using
      (hf.third_tendsto i j k).sub (hg.third_tendsto i j k)

end NavierStokesR3.H3Comparison


end

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

namespace NavierStokesR3.H3Embedding

open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open H3Comparison

theorem squareEnergy_difference_tendsto {f : ℕ → Space → Space} {g : Space → Space}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (ht : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g))) :
    Tendsto (fun n => squareEnergy (f n - g)) atTop (𝓝 0) := by
  have he : (fun n => squareEnergy (f n - g)) =
      fun n => ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2 := by
    funext n
    rw [squareEnergy_eq_norm_toLp ((hf n).sub hg), MemLp.toLp_sub]
  rw [he]
  have hc : Tendsto (fun _ : ℕ => hg.toLp g) atTop (𝓝 (hg.toLp g)) := tendsto_const_nhds
  simpa only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] using (ht.sub hc).norm.pow 2

def approximationErrorNorm {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) (n : ℕ) : ℝ :=
  weakH3Norm (h.approx n - f) (fun i => spatialPartial i (h.approx n) - df i)
    (fun i j => spatialPartial i (spatialPartial j (h.approx n)) - ddf i j)
    (fun i j k => spatialPartial i (spatialPartial j (spatialPartial k (h.approx n))) - dddf i j k)

theorem approximationErrorNorm_tendsto {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) :
    Tendsto (approximationErrorNorm h) atTop (𝓝 0) := by
  have h0 := squareEnergy_difference_tendsto h.approx_memLp h.memLp h.tendsto
  have h1 (i) := squareEnergy_difference_tendsto (fun n => h.derivative_approx_memLp n i)
    (h.derivative_memLp i) (h.derivative_tendsto i)
  have h2 (i j) := squareEnergy_difference_tendsto (fun n => h.second_approx_memLp n i j)
    (h.second_memLp i j) (h.second_tendsto i j)
  have h3 (i j k) := squareEnergy_difference_tendsto (fun n => h.third_approx_memLp n i j k)
    (h.third_memLp i j k) (h.third_tendsto i j k)
  have hs2 := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ => h2 i j))
  have hs3 := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ =>
      tendsto_finsetSum Finset.univ (fun k _ => h3 i j k)))
  have hm := ((((((h0.add (h1 0)).add (h1 1)).add (h1 2)).add (h2 1 0)).add
    (h2 2 0)).add (h2 2 1))
  have he := (((hm.add (h3 2 1 0)).add hs2).add hs3)
  unfold approximationErrorNorm weakH3Norm weakH3Energy
  simpa only [Finset.sum_const_zero, add_zero, Real.sqrt_zero] using he.sqrt

theorem approximation_norm_sub_le {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) (hf : Continuous f) (n : ℕ) (x : Space) :
    ‖h.approx n x - f x‖ ≤ 3 * approximationErrorNorm h n := by
  have ha := (H3Approximation.of_contDiff_compact (h.smooth n) (h.compact n)).sub h
  exact norm_le_weakH3Norm ha ((h.smooth n).continuous.sub hf) x

theorem approximation_uniform_error {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) (hf : Continuous f) :
    ∃ a : ℕ → ℝ, (∀ n, 0 ≤ a n) ∧ Tendsto a atTop (𝓝 0) ∧
      ∀ n x, ‖h.approx n x - f x‖ ≤ a n := by
  refine ⟨fun n => 3 * approximationErrorNorm h n, ?_, ?_, approximation_norm_sub_le h hf⟩
  · intro n
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · simpa only [mul_zero] using tendsto_const_nhds.mul (approximationErrorNorm_tendsto h)


end NavierStokesR3.H3Embedding

/-! Merged from `NavierStokes.R3.H3Curve` (in a section, so its `open`s cannot leak). -/
section
/-! # Curves in the genuine whole-space H³ topology

The topology is the finite product of the ordinary L² topologies of the
velocity and every weak coordinate derivative through order three. The weak
jets come from one smooth compact approximation at each time.
-/

/-! Merged from `NavierStokes.R3.H3CompactHelpers`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology BigOperators ContDiff

namespace NavierStokesR3.H3Compact

open ProblemStatement
open NavierStokes.ProblemStatement (coordinateVector)
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness (slab spatial_smooth)

/-- Coordinate derivatives are genuine spatial derivatives, including at a
closed time interval's endpoints. -/
def partialField (i : Fin 3) (u : VelocityField) : VelocityField :=
  fun z => spatialPartial i (fun y => u (z.1, y)) z.2




/-- An arbitrary ordered word of ordinary coordinate derivatives. -/
def partialWord : List (Fin 3) → VelocityField → VelocityField
  | [], u => u
  | i :: is, u => partialField i (partialWord is u)





end NavierStokesR3.H3Compact


end


/-! Merged from `NavierStokes.R3.H3Continuity`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Continuity in the whole-space derivative H³ norm

The continuity assertion below uses the H³ norm of the difference of two
spatial fields. Thus it controls convergence of every spatial derivative
through order three in genuine Lebesgue L², rather than merely continuity of
the scalar norm of a field.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace NavierStokesR3.H3Embedding

open ProblemStatement H3Compact
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness (slab spatial_smooth)





@[simp] theorem derivativeH3Norm_zero : derivativeH3Norm (fun _ : Space => (0 : Space)) = 0 := by
  have hz (i : Fin 3) : spatialPartial i (fun _ : Space => (0 : Space)) = fun _ => 0 := by
    funext x
    simp [spatialPartial]
  simp [derivativeH3Norm, derivativeH3Energy, mixedEnergy, squareEnergy, hz]



end NavierStokesR3.H3Embedding


end


noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace NavierStokesR3.H3Comparison

open ProblemStatement H3Embedding

/-- A continuous H³ curve, with its continuous spatial representative and
genuine weak derivative jets. Continuity is in the actual L² spaces. -/
structure H3Curve (u : VelocityField) (s : Set ℝ) where
  first : Fin 3 → VelocityField
  second : Fin 3 → Fin 3 → VelocityField
  third : Fin 3 → Fin 3 → Fin 3 → VelocityField
  spatial_continuous : ∀ t ∈ s, Continuous (fun x => u (t, x))
  approximation : ∀ t ∈ s, H3Approximation (fun x => u (t, x))
    (fun i x => first i (t, x)) (fun i j x => second i j (t, x))
    (fun i j k x => third i j k (t, x))
  velocity_continuous : Continuous (fun t : s =>
    ((approximation t t.property).memLp).toLp (fun x => u (t, x)))
  first_continuous : ∀ i, Continuous (fun t : s =>
    ((approximation t t.property).derivative_memLp i).toLp (fun x => first i (t, x)))
  second_continuous : ∀ i j, Continuous (fun t : s =>
    ((approximation t t.property).second_memLp i j).toLp (fun x => second i j (t, x)))
  third_continuous : ∀ i j k, Continuous (fun t : s =>
    ((approximation t t.property).third_memLp i j k).toLp (fun x => third i j k (t, x)))

namespace H3Curve

variable {u : VelocityField} {s : Set ℝ}

def normAt (h : H3Curve u s) (t : ℝ) : ℝ :=
  weakH3Norm (fun x => u (t, x)) (fun i x => h.first i (t, x))
    (fun i j x => h.second i j (t, x)) (fun i j k x => h.third i j k (t, x))

theorem normAt_nonneg (h : H3Curve u s) (t : ℝ) : 0 ≤ h.normAt t := Real.sqrt_nonneg _

theorem norm_le (h : H3Curve u s) {t : ℝ} (ht : t ∈ s) (x : Space) :
    ‖u (t, x)‖ ≤ 3 * h.normAt t :=
  norm_le_weakH3Norm (h.approximation t ht) (h.spatial_continuous t ht) x




/-- The L² velocity curve, extended by zero off its time set. The extension
is only used at times where the time set contains a neighborhood. -/
def velocityLp (h : H3Curve u s) (t : ℝ) : Lp Space 2 (volume : Measure Space) := by
  classical
  exact if ht : t ∈ s then (h.approximation t ht).memLp.toLp (fun x => u (t, x)) else 0



def restrict (h : H3Curve u s) {r : Set ℝ} (hrs : r ⊆ s) : H3Curve u r where
  first := h.first
  second := h.second
  third := h.third
  spatial_continuous := fun t ht => h.spatial_continuous t (hrs ht)
  approximation := fun t ht => h.approximation t (hrs ht)
  velocity_continuous := h.velocity_continuous.comp
    (continuous_subtype_val.subtype_mk (fun t : r => hrs t.property))
  first_continuous := fun i => (h.first_continuous i).comp
    (continuous_subtype_val.subtype_mk (fun t : r => hrs t.property))
  second_continuous := fun i j => (h.second_continuous i j).comp
    (continuous_subtype_val.subtype_mk (fun t : r => hrs t.property))
  third_continuous := fun i j k => (h.third_continuous i j k).comp
    (continuous_subtype_val.subtype_mk (fun t : r => hrs t.property))


end H3Curve

end NavierStokesR3.H3Comparison
end

/-! Merged from `NavierStokes.R3.L2TimeDerivative`. -/
/-! # L² time differentiation for compact smooth fields

Pointwise time differentiation passes to the actual L² space by dominated
convergence of the squared slope error. A compact uniform derivative bound
supplies the domination through the mean value theorem.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace NavierStokesR3.H3Comparison

open ProblemStatement



end NavierStokesR3.H3Comparison

/-! Merged from `NavierStokes.R3.H3StrongSolution`. -/
/-! # The classical H³ solution class on a finite Euclidean slab

Velocity and its spatial jets belong to the genuine H³ completion. Time
differentiation is in L², and the equation holds almost everywhere in space.
Pressure is an arbitrary C¹ spatial potential;
no normalization, support, or bound on the pressure itself is imposed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

namespace NavierStokesR3.H3Comparison

open ProblemStatement

def weakAdvection (u : Space → Space) (du : Fin 3 → Space → Space) (x : Space) : Space :=
  ∑ i, u x i • du i x

def weakLaplacian (ddu : Fin 3 → Fin 3 → Space → Space) (x : Space) : Space :=
  ∑ i, ddu i i x

def weakDivergence (du : Fin 3 → Space → Space) (x : Space) : ℝ := ∑ i, du i x i

/-- The usual strong formulation on a closed time slab, with H³ spatial
regularity and an actual L² time derivative at interior times. -/
structure StrongSolutionOnIcc (ν : ℝ) (f : VelocityField) (a b : ℝ)
    (u : VelocityField) (p : PressureField) where
  time_lt : a < b
  curve : H3Curve u (Icc a b)
  timeDerivative : VelocityField
  timeDerivative_memLp : ∀ t ∈ Ioo a b, MemLp (fun x => timeDerivative (t, x)) 2 volume
  hasDerivAt_velocity : ∀ t (ht : t ∈ Ioo a b),
    HasDerivAt curve.velocityLp
      ((timeDerivative_memLp t ht).toLp (fun x => timeDerivative (t, x))) t
  pressure_C1 : ∀ t ∈ Ioo a b, ContDiff ℝ 1 (fun x => p (t, x))
  divergence_free : ∀ t ∈ Ioo a b,
    ∀ᵐ x ∂volume, weakDivergence (fun i x => curve.first i (t, x)) x = 0
  navier_stokes : ∀ t ∈ Ioo a b, ∀ᵐ x ∂volume,
    timeDerivative (t, x) + weakAdvection (fun x => u (t, x))
        (fun i x => curve.first i (t, x)) x -
      ν • weakLaplacian (fun i j x => curve.second i j (t, x)) x +
      NavierStokes.ProblemStatement.pressureGradient p t x = f (t, x)

theorem weakAdvection_memLp {u : Space → Space} {du : Fin 3 → Space → Space}
    (hu : Continuous u) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, ‖u x‖ ≤ B)
    (hd : ∀ i, MemLp (du i) 2 volume) : MemLp (weakAdvection u du) 2 volume := by
  apply memLp_finsetSum
  intro i _
  apply ((hd i).const_smul B).mono
  · exact ((EuclideanSpace.proj i).continuous.comp hu).aestronglyMeasurable.smul
      (hd i).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_smul, Pi.smul_apply, norm_smul, Real.norm_of_nonneg hB]
    exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le (u x) i).trans (hb x))
      (norm_nonneg _)

/-- In the ordinary H³ solution class the pressure gradient is square
integrable because the equation expresses it as a sum of L² fields. This is
a conclusion, not an added pressure normalization hypothesis. -/
theorem StrongSolutionOnIcc.pressureGradient_memLp {ν a b : ℝ} {f u : VelocityField}
    {p : PressureField} (h : StrongSolutionOnIcc ν f a b u p)
    {t : ℝ} (ht : t ∈ Ioo a b) (hf : MemLp (fun x => f (t, x)) 2 volume) :
    MemLp (fun x => NavierStokes.ProblemStatement.pressureGradient p t x) 2 volume := by
  have htt : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have hd := h.curve.approximation t htt
  have had := weakAdvection_memLp (h.curve.spatial_continuous t htt)
    (mul_nonneg (by norm_num) (h.curve.normAt_nonneg t)) (h.curve.norm_le htt)
    hd.derivative_memLp
  have hla : MemLp (weakLaplacian (fun i j x => h.curve.second i j (t, x))) 2 volume := by
    apply memLp_finsetSum
    intro i _
    exact hd.second_memLp i i
  apply (hf.sub ((h.timeDerivative_memLp t ht).add had) |>.add (hla.const_smul ν)).ae_eq
  filter_upwards [h.navier_stokes t ht] with x hx
  change f (t, x) - (h.timeDerivative (t, x) + weakAdvection (fun x => u (t, x))
    (fun i x => h.curve.first i (t, x)) x) +
      ν • weakLaplacian (fun i j x => h.curve.second i j (t, x)) x = _
  rw [← hx]
  abel

/-- A classical H³ solution on a half-open lifespan. The same velocity and
pressure solve the equation on every shorter closed slab. -/
structure ClassicalH3Solution (ν : ℝ) (f : VelocityField) (initial : Space → Space)
    (T : ℝ) (u : VelocityField) (p : PressureField) where
  lifespan_pos : 0 < T
  initial_velocity : ∀ x, u (0, x) = initial x
  on_shorter_interval : ∀ S ∈ Ioo (0 : ℝ) T, StrongSolutionOnIcc ν f 0 S u p

end NavierStokesR3.H3Comparison

/-! Merged from `NavierStokes.R3.H3CompactCurve` (in a section, so its `open`s cannot leak). -/
section
noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace NavierStokesR3.H3Comparison

open ProblemStatement H3Embedding H3Compact
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness (slab spatial_smooth)




end NavierStokesR3.H3Comparison
end

/-! Merged from `NavierStokes.R3.H3Transport`. -/
/-! # Divergence-free transport for weak H³ limits

The compact smooth approximants need not themselves be divergence-free.
Their divergence terms converge to the zero weak divergence of the limit.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

namespace NavierStokesR3.H3Comparison

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness

private def transportProduct (i : Fin 3) : Space →L[ℝ] Space →L[ℝ] Space :=
  (ContinuousLinearMap.lsmul ℝ ℝ).comp (EuclideanSpace.proj i)

private theorem transportProduct_apply (i : Fin 3) (v w : Space) :
    transportProduct i v w = (v i) • w := rfl

private def realInnerBilinear : Space →L[ℝ] Space →L[ℝ] ℝ := innerSL ℝ

private theorem realInnerBilinear_apply (v w : Space) :
    realInnerBilinear v w = ⟪v, w⟫_ℝ := rfl

private theorem compact_transport {w v : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hv : ContDiff ℝ ∞ v)
    (hcw : HasCompactSupport w) (hcv : HasCompactSupport v) :
    2 * (∑ i : Fin 3, ∫ x, v x i * ⟪w x, spatialPartial i w x⟫_ℝ) =
      -(∑ i : Fin 3, ∫ x, ‖w x‖ ^ 2 * spatialPartial i v x i) := by
  have hiL (i : Fin 3) : Integrable (fun x => v x i * ⟪w x, spatialPartial i w x⟫_ℝ) :=
    ((component_contDiff hv i).continuous.mul
      (hw.inner ℝ (spatial_partial_contDiff hw i)).continuous).integrable_of_hasCompactSupport
      (CompactEnergy.compact_component hcv i).mul_right
  have hiR (i : Fin 3) : Integrable (fun x => ‖w x‖ ^ 2 * spatialPartial i v x i) :=
    ((hw.continuous.norm.pow 2).mul
      (component_contDiff (spatial_partial_contDiff hv i) i).continuous).integrable_of_hasCompactSupport
      (CompactEnergy.compact_norm_sq hcw).mul_right
  have h := CompactEnergy.integral_fderiv_apply (hw.norm_sq ℝ) hv hcv
  have he (x : Space) : fderiv ℝ (fun y => ‖w y‖ ^ 2) x (v x) =
      2 * ∑ i : Fin 3, v x i * ⟪w x, spatialPartial i w x⟫_ℝ := by
    rw [fderiv_normsq hw]
    have hlin : fderiv ℝ w x (v x) = ∑ i : Fin 3, (v x i) • spatialPartial i w x := by
      calc
        fderiv ℝ w x (v x) = fderiv ℝ w x (∑ i : Fin 3, (v x i) • coordinateVector i) :=
          congrArg (fderiv ℝ w x) (sum_coordinates (v x)).symm
        _ = _ := by simp only [map_sum, map_smul, spatialPartial]
    rw [hlin, inner_sum]
    simp only [inner_smul_right]
  simp_rw [he] at h
  have hright : (fun x => ‖w x‖ ^ 2 * ∑ i : Fin 3, spatialPartial i v x i) =
      (fun x => ∑ i : Fin 3, ‖w x‖ ^ 2 * spatialPartial i v x i) :=
    funext (fun _ => Finset.mul_sum _ _ _)
  rw [hright] at h
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hiL i),
    integral_finsetSum _ (fun i _ => hiR i)] at h
  exact h

/-- All integrals of the weak transport term are genuine integrable products. -/
theorem integrable_transport {w v : Space → Space} {dw : Fin 3 → Space → Space}
    (hw : MemLp w 2 volume) (hv : AEStronglyMeasurable v volume)
    (hdw : ∀ i, MemLp (dw i) 2 volume) {C : ℝ} (hC : ∀ x, ‖v x‖ ≤ C)
    (i : Fin 3) : Integrable (fun x => v x i * ⟪w x, dw i x⟫_ℝ) := by
  have hi := integrable_inner_of_memLp
    (memLp_bilinear_bounded (transportProduct i) hv hw hC) (hdw i)
  simpa only [transportProduct_apply, real_inner_smul_left] using! hi

/-- Transport cancels for weak first derivatives obtained from Sobolev
approximants that converge uniformly in velocity. No pointwise derivative of
the limiting fields, pressure condition, or energy identity is assumed. -/
theorem weak_transport_zero {w v : Space → Space} {dw dv : Fin 3 → Space → Space}
    (hw : H1Approximation w dw) (hv : H1Approximation v dv)
    {aw av : ℕ → ℝ} (haw : Tendsto aw atTop (𝓝 0)) (hav : Tendsto av atTop (𝓝 0))
    (hew : ∀ n x, ‖hw.approx n x - w x‖ ≤ aw n)
    (hev : ∀ n x, ‖hv.approx n x - v x‖ ≤ av n)
    {Cw Cv : ℝ} (hcw : ∀ x, ‖w x‖ ≤ Cw) (hcv : ∀ x, ‖v x‖ ≤ Cv)
    (hdiv : ∀ᵐ x ∂volume, (∑ i : Fin 3, dv i x i) = 0) :
    (∫ x, ∑ i : Fin 3, v x i * ⟪w x, dw i x⟫_ℝ) = 0 := by
  have hlimL (i : Fin 3) : Tendsto
      (fun n => ∫ x, hv.approx n x i * ⟪hw.approx n x, spatialPartial i (hw.approx n) x⟫_ℝ)
      atTop (𝓝 (∫ x, v x i * ⟪w x, dw i x⟫_ℝ)) := by
    obtain ⟨hp, hlim⟩ := tendsto_toLp_bilinear (transportProduct i)
      (fun n => (hv.smooth n).continuous.aestronglyMeasurable) hv.memLp.aestronglyMeasurable
      hw.approx_memLp hw.memLp hav hev hcv hw.tendsto
    have h := tendsto_integral_inner hp (fun n => hw.derivative_approx_memLp n i)
      (memLp_bilinear_bounded (transportProduct i) hv.memLp.aestronglyMeasurable hw.memLp hcv)
      (hw.derivative_memLp i) hlim (hw.derivative_tendsto i)
    simpa only [transportProduct_apply, real_inner_smul_left] using! h
  obtain ⟨hp, hlimp⟩ := tendsto_toLp_bilinear realInnerBilinear
    (fun n => (hw.smooth n).continuous.aestronglyMeasurable) hw.memLp.aestronglyMeasurable
    hw.approx_memLp hw.memLp haw hew hcw hw.tendsto
  have hp₀ := memLp_bilinear_bounded realInnerBilinear hw.memLp.aestronglyMeasurable hw.memLp hcw
  have hlimR (i : Fin 3) : Tendsto
      (fun n => ∫ x, ‖hw.approx n x‖ ^ 2 * spatialPartial i (hv.approx n) x i)
      atTop (𝓝 (∫ x, ‖w x‖ ^ 2 * dv i x i)) := by
    let hvi := hv.map (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
    have h := tendsto_integral_inner hp (fun n => hvi.derivative_approx_memLp n i)
      hp₀ (hvi.derivative_memLp i) hlimp (hvi.derivative_tendsto i)
    have he (n : ℕ) : spatialPartial i (hvi.approx n) =
        fun x => spatialPartial i (hv.approx n) x i := by
      funext x
      exact fderiv_component (hv.smooth n) i x (coordinateVector i)
    simp only [he, realInnerBilinear_apply, real_inner_self_eq_norm_sq] at h
    change Tendsto (fun n => ∫ x, spatialPartial i (hv.approx n) x i * ‖hw.approx n x‖ ^ 2)
      atTop (𝓝 (∫ x, dv i x i * ‖w x‖ ^ 2)) at h
    simpa only [mul_comm] using! h
  have hcompact (n : ℕ) := compact_transport (hw.smooth n) (hv.smooth n) (hw.compact n) (hv.compact n)
  have hL := (tendsto_finsetSum Finset.univ (fun i _ => hlimL i)).const_mul 2
  have hR := (tendsto_finsetSum Finset.univ (fun i _ => hlimR i)).neg
  have hid : 2 * (∑ i : Fin 3, ∫ x, v x i * ⟪w x, dw i x⟫_ℝ) =
      -(∑ i : Fin 3, ∫ x, ‖w x‖ ^ 2 * dv i x i) :=
    tendsto_nhds_unique (hL.congr hcompact) hR
  have hiR (i : Fin 3) : Integrable (fun x => ‖w x‖ ^ 2 * dv i x i) := by
    have hvi := hv.map (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
    simpa only [realInnerBilinear_apply, real_inner_self_eq_norm_sq, Pi.mul_apply, Function.comp_apply] using!
      hp₀.integrable_mul (hvi.derivative_memLp i)
  have hzero : (∑ i : Fin 3, ∫ x, ‖w x‖ ^ 2 * dv i x i) = 0 := by
    rw [← integral_finsetSum _ (fun i _ => hiR i)]
    apply integral_eq_zero_of_ae
    filter_upwards [hdiv] with x hx
    simp only [← Finset.mul_sum, hx, mul_zero, Pi.zero_apply]
  rw [hzero, neg_zero] at hid
  rw [integral_finsetSum _ (fun i _ =>
    integrable_transport hw.memLp hv.memLp.aestronglyMeasurable hw.derivative_memLp hcv i)]
  linarith

/-- Ordinary H³ velocities have the exact transport energy cancellation.
Uniform convergence and boundedness are consequences of H³, not premises. -/
theorem H3Approximation.transport_zero {w v : Space → Space}
    {dw dv : Fin 3 → Space → Space}
    {ddw ddv : Fin 3 → Fin 3 → Space → Space}
    {dddw dddv : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (hw : H3Approximation w dw ddw dddw) (hv : H3Approximation v dv ddv dddv)
    (hcw : Continuous w) (hcv : Continuous v)
    (hdiv : ∀ᵐ x ∂volume, (∑ i : Fin 3, dv i x i) = 0) :
    (∫ x, ∑ i : Fin 3, v x i * ⟪w x, dw i x⟫_ℝ) = 0 := by
  obtain ⟨aw, _, haw, hew⟩ := H3Embedding.approximation_uniform_error hw hcw
  obtain ⟨av, _, hav, hev⟩ := H3Embedding.approximation_uniform_error hv hcv
  exact weak_transport_zero hw.toH1Approximation hv.toH1Approximation haw hav hew hev
    (H3Embedding.norm_le_weakH3Norm hw hcw) (H3Embedding.norm_le_weakH3Norm hv hcv) hdiv

end NavierStokesR3.H3Comparison

/-! Merged from `NavierStokes.R3.H3CandidateStrong` (in a section, so its `open`s cannot leak). -/
section
noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

namespace NavierStokesR3.H3Comparison

open ProblemStatement
open NavierStokes.ProblemStatement (temporalDerivative advection spatialDerivative spatialDivergence)
open NavierStokes.PeriodicUniqueness (slab spatial_smooth time_differentiable_at_interior)









end NavierStokesR3.H3Comparison
end

/-! Merged from `NavierStokes.R3.H3PressureDistribution` (in a section, so its `open`s cannot leak). -/
section
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
end


/-! Merged from `NavierStokes.R3.H3PressureOrthogonality`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Pressure cancellation for ordinary first-order Sobolev fields

The pressure is an arbitrary C¹ scalar function. Only its gradient must be
square integrable; no decay or growth condition is imposed on the pressure.
-/

/-! Merged from `NavierStokes.R3.H3DivCurlFourier`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Orthogonality of square integrable divergence-free and curl-free fields -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators FourierTransform

namespace NavierStokesR3.H3DivCurlFourier

open ProblemStatement
open NavierStokes.ProblemStatement (coordinateVector)

abbrev ComplexL2 := Lp ℂ 2 (volume : Measure Space)
abbrev ComplexDistribution := TemperedDistribution Space ℂ

def coordinate (i : Fin 3) (ξ : Space) : ℂ := ξ i




def multiplier (i : Fin 3) (f : ComplexL2) : ComplexDistribution :=
  TemperedDistribution.smulLeftCLM ℂ (coordinate i) (Lp.toTemperedDistribution f)















end NavierStokesR3.H3DivCurlFourier


end


noncomputable section

open Set Filter MeasureTheory LineDeriv
open scoped ContDiff Topology BigOperators LineDeriv

namespace NavierStokesR3.H3PressureOrthogonality

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open H3Comparison H3PressureDistribution

def complexComponent (i : Fin 3) : Space →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj i)

@[simp] theorem complexComponent_apply (i : Fin 3) (x : Space) :
    complexComponent i x = (x i : ℂ) := rfl






end NavierStokesR3.H3PressureOrthogonality


end


/-! Merged from `NavierStokes.R3.H3Energy`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Difference energy for ordinary H³ fields

The time derivative is a derivative in the L² Hilbert space. Spatial
integration by parts uses the actual weak derivative approximations.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

namespace NavierStokesR3.H3Comparison

open NavierStokes.ProblemStatement






end NavierStokesR3.H3Comparison


end


/-! Merged from `NavierStokes.R3.H3Blowup`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Whole-space H³ blowup and the exclusion of H³ continuation

The obstruction is the actual Sobolev norm and its continuous topology. It
applies to weak H³ spatial fields, rather than a class requiring C∞ velocity.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace NavierStokesR3.H3Embedding

open ProblemStatement H3Comparison
open NavierStokes.PeriodicUniqueness (slab spatial_smooth)





end NavierStokesR3.H3Embedding


end


/-! Merged from `NavierStokes.R3.H3CandidateUniqueness`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section


/-! Merged from `NavierStokes.R3.H3WeakStrong`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Weak–strong comparison in the ordinary H³ class -/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

namespace NavierStokesR3.H3Comparison

open ProblemStatement
open NavierStokes.ProblemStatement (pressureGradient)



end NavierStokesR3.H3Comparison


end

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

namespace NavierStokesR3.H3Comparison

open ProblemStatement
open NavierStokes.ProblemStatement (pressureGradient spatialDerivative coordinateVector)
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness (slab spatial_smooth)





end NavierStokesR3.H3Comparison


end


noncomputable section

open Set

namespace NavierStokesR3.H3Comparison

open ProblemStatement H3Embedding

def ClassicalH3Solution.restrict {ν T S : ℝ} {f u : VelocityField} {p : PressureField}
    {initial : Space → Space} (h : ClassicalH3Solution ν f initial T u p)
    (hS : 0 < S) (hST : S ≤ T) : ClassicalH3Solution ν f initial S u p where
  lifespan_pos := hS
  initial_velocity := h.initial_velocity
  on_shorter_interval := fun R hR => h.on_shorter_interval R ⟨hR.1, hR.2.trans_le hST⟩

def VelocityAgreesOn (T : ℝ) (u v : VelocityField) : Prop :=
  ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, u (t, x) = v (t, x)











end NavierStokesR3.H3Comparison

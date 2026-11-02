import NavierStokes.R3.H3WeakEmbedding
import NavierStokes.R3.H3Approximation


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

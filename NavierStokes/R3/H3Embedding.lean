import NavierStokes.R3.H3Definitions
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Group.Integral

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

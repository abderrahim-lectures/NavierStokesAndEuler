import NavierStokes.SmoothPathFamily
import NavierStokes.JointODE
import NavierStokes.CommonCoverSolve
import NavierStokes.CommonCoverClass
import NavierStokes.ParticularWaveBounds
import NavierStokes.GenericEndpointExtension

/-! # The slow-time-zero clause of the common-torus particular inverse

Uniform interior jets determine genuine closed-side smoothness. The actual
common-torus velocity and pressure inherit these one-sided jets, uniformly
on compact parameter sets. No analytic regularity or open extension of an
arbitrary source is required.
-/
/-! Merged from `NavierStokes.WithinPathFamily` (in a section, so its `open`s cannot leak). -/
section
/-! # Smooth parameter families on a convex closed domain

The parameter set need not be open. In particular, all mixed one-sided jets
at a slow-time endpoint pass to the actual continuous-path Banach space.
-/

noncomputable section

namespace NavierStokes.WithinPathFamily

open Set Filter Function Metric Asymptotics
open scoped Topology ContDiff
open SmoothPathFamily

universe u

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {a b : ℝ}

/-- Uniform differentiability of continuous paths using only derivatives
within the convex parameter domain. -/
theorem hasFDerivWithinAt_pathFamily {U : Set P} (hU : Convex ℝ U)
    (F : P × ℝ → E) (G : P × ℝ → P →L[ℝ] E)
    (hF : ContinuousOn F (U ×ˢ Icc a b))
    (hG : ContinuousOn G (U ×ˢ Icc a b))
    (hderiv : ∀ p ∈ U, ∀ t : Icc a b,
      HasFDerivWithinAt (fun q => F (q, t)) (G (p, t)) U p)
    {p : P} (hp : p ∈ U) :
    HasFDerivWithinAt (pathFamily (a := a) (b := b) F)
      (flipPath (P := P) (E := E) (pathFamily (a := a) (b := b) G p)) U p := by
  rw [hasFDerivWithinAt_iff_isLittleO]
  apply isLittleO_iff.mpr
  intro ε hε
  have hgc := continuousOn_pathFamily hG p hp
  have hsmall : ∀ᶠ q in 𝓝[U] p,
      ‖pathFamily (a := a) (b := b) G q - pathFamily G p‖ < ε := by
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp hgc ε hε
  obtain ⟨δ, hδ, hδmem⟩ := Metric.mem_nhdsWithin_iff.mp hsmall
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds p hδ),
    self_mem_nhdsWithin] with q hq hqU
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg (q - p)))).mpr
  intro t
  simp only [ContinuousMap.sub_apply, flipPath_apply,
    pathFamily_apply F q (slice_continuous hF hqU),
    pathFamily_apply F p (slice_continuous hF hp),
    pathFamily_apply G p (slice_continuous hG hp)]
  have hd : ∀ r ∈ ball p δ ∩ U,
      HasFDerivWithinAt (fun r => F (r, t) - G (p, t) r)
        (G (r, t) - G (p, t)) (ball p δ ∩ U) r := by
    intro r hr
    exact ((hderiv r hr.2 t).sub (G (p, t)).hasFDerivAt.hasFDerivWithinAt).mono
      inter_subset_right
  have hb : ∀ r ∈ ball p δ ∩ U, ‖G (r, t) - G (p, t)‖ ≤ ε := by
    intro r hr
    calc
      _ = ‖(pathFamily G r - pathFamily G p : C(Icc a b, P →L[ℝ] E)) t‖ := by
        simp only [ContinuousMap.sub_apply,
          pathFamily_apply G r (slice_continuous hG hr.2),
          pathFamily_apply G p (slice_continuous hG hp)]
      _ ≤ ‖pathFamily (a := a) (b := b) G r - pathFamily G p‖ :=
        ContinuousMap.norm_coe_le_norm _ t
      _ ≤ ε := (hδmem hr).le
  have hh := ((convex_ball p δ).inter hU).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hd hb ⟨mem_ball_self hδ, hp⟩ ⟨hq, hqU⟩
  have he : F (q, t) - F (p, t) - G (p, t) (q - p) =
      (F (q, t) - G (p, t) q) - (F (p, t) - G (p, t) p) := by
    rw [map_sub]
    abel
  rw [he]
  exact hh

noncomputable def parameterDerivativeWithin (U : Set P) (V : Set ℝ)
    (F : P × ℝ → E) (z : P × ℝ) : P →L[ℝ] E :=
  (fderivWithin ℝ F (U ×ˢ V) z).comp (ContinuousLinearMap.inl ℝ P ℝ)

/-- Every finite order of genuine joint within regularity passes to the
path space. No extension across the parameter boundary is an assumption. -/
theorem contDiffOn_pathFamily_nat (U : Set P) (V : Set ℝ)
    (hU : Convex ℝ U) (hu : UniqueDiffOn ℝ U) (hv : UniqueDiffOn ℝ V)
    (hI : Icc a b ⊆ V) (n : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : P × ℝ → W),
      ContDiffOn ℝ n F (U ×ˢ V) →
      ContDiffOn ℝ n (pathFamily (a := a) (b := b) F) U := by
  induction n with
  | zero =>
    intro W _ _ F hF
    exact contDiffOn_zero.mpr (continuousOn_pathFamily
      (hF.continuousOn.mono (prod_mono Subset.rfl hI)))
  | succ n ih =>
    intro W _ _ F hF
    have hFs : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) F (U ×ˢ V) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hF
    have hdata := (contDiffOn_succ_iff_fderivWithin (hu.prod hv)).mp hFs
    have hD : ContDiffOn ℝ n (parameterDerivativeWithin U V F) (U ×ˢ V) :=
      hdata.2.2.clm_comp contDiffOn_const
    have hd : ∀ p ∈ U, HasFDerivWithinAt (pathFamily (a := a) (b := b) F)
        (flipPath (P := P) (E := W)
          (pathFamily (a := a) (b := b) (parameterDerivativeWithin U V F) p)) U p := by
      intro p hp
      apply hasFDerivWithinAt_pathFamily hU F (parameterDerivativeWithin U V F)
        (hF.continuousOn.mono (prod_mono Subset.rfl hI))
        (hD.continuousOn.mono (prod_mono Subset.rfl hI)) _ hp
      intro q hq t
      change HasFDerivWithinAt (fun r => F (r, (t : ℝ)))
        ((fderivWithin ℝ F (U ×ˢ V) (q, t)).comp
          (ContinuousLinearMap.inl ℝ P ℝ)) U q
      exact (hdata.1 (q, (t : ℝ)) ⟨hq, hI t.2⟩).hasFDerivWithinAt.comp q
        ((hasFDerivAt_prodMk_left q (t : ℝ)).hasFDerivWithinAt (s := U))
        (show MapsTo (fun r : P => (r, (t : ℝ))) U (U ×ˢ V) from
          fun r hr => ⟨hr, hI t.2⟩)
    have hpathD := ih (parameterDerivativeWithin U V F) hD
    let L : C(Icc a b, P →L[ℝ] W) →L[ℝ] P →L[ℝ] C(Icc a b, W) :=
      flipPath (P := P) (E := W) (a := a) (b := b)
    have hL : ContDiff ℝ (n : WithTop ℕ∞) L :=
      ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
        (E := C(Icc a b, P →L[ℝ] W)) (F := P →L[ℝ] C(Icc a b, W)) L
    have hflip : ContDiffOn ℝ n
        (fun p => flipPath (P := P) (E := W) (a := a) (b := b)
          (pathFamily (a := a) (b := b) (parameterDerivativeWithin U V F) p)) U :=
      hL.comp_contDiffOn hpathD
    have hh : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1)
        (pathFamily (a := a) (b := b) F) U := by
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hu).mpr
      refine ⟨?_, _, hflip, hd⟩
      intro hω
      exact (WithTop.coe_ne_top hω).elim
    simpa only [Nat.cast_add, Nat.cast_one] using hh


end NavierStokes.WithinPathFamily
end


/-! Merged from `NavierStokes.WithinJointODE`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Joint ODE jets on closed parameter and pulse domains -/

noncomputable section

namespace NavierStokes.WithinJointODE

open Set Filter Function
open scoped Topology ContDiff

universe u

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {a b : ℝ}




end NavierStokes.WithinJointODE

namespace NavierStokes.WithinJetClosure

open Set Filter
open scoped Topology ContDiff

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]



end NavierStokes.WithinJetClosure


end


/-! Merged from `NavierStokes.CommonCoverWithin`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Common-torus inverse at a one-sided slow endpoint

All inputs have genuine joint within regularity on the slow domain. The
actual copy and common-torus solves inherit it; an open continuation of the
source is not required.
-/

noncomputable section

namespace NavierStokes.CommonCoverSolve.LinearData

open Set Filter Function
open scoped Topology ContDiff
open TorusInverse

variable {P V E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ} (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)
  {U : Set P} (hU : Convex ℝ U) (hu : UniqueDiffOn ℝ U)
  (hA : ContDiffOn ℝ ∞ d.coefficient (U ×ˢ univ))
  (hB : ContDiffOn ℝ ∞ d.forcingMap (U ×ˢ univ))
  (hf : ContDiffOn ℝ ∞ d.source (U ×ˢ univ))

include hU hu hA hB hf










end NavierStokes.CommonCoverSolve.LinearData


end


/-! Merged from `NavierStokes.ParticularWithinPressure`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # One-sided jets of the actual particular velocity and pressure -/

noncomputable section

namespace NavierStokes.ParticularWaveBounds

open Set Filter Function
open scoped ContDiff Topology InnerProductSpace
open CommonCoverSolve TorusInverse

section Real

variable {P H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]



end Real

section Complex

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]


variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]



end Complex

end NavierStokes.ParticularWaveBounds


end


/-! Merged from `NavierStokes.ParticularWithinBounds`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # The particular inverse estimate at closed slow and pulse endpoints -/

noncomputable section

namespace NavierStokes.ParticularWaveBounds

open Set Function Filter
open scoped ContDiff Topology InnerProductSpace
open PrimaryPulseBounds

variable {Q H : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]


end NavierStokes.ParticularWaveBounds


end


noncomputable section

namespace NavierStokes.ParticularOneSided

open Set Filter
open scoped ContDiff Topology
open CommonCoverSolve TorusInverse ParticularWaveBounds

section InputTraces

variable {Y E : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


end InputTraces

section UniformJets

variable {Y E : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]



end UniformJets

section CommonTorus

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

def slowDomain (W : Set X) : Set (ℝ × X) := Ici (0 : ℝ) ×ˢ W
def positiveDomain (W : Set X) : Set (ℝ × X) := Ioi (0 : ℝ) ×ˢ W








end CommonTorus

end NavierStokes.ParticularOneSided

import NavierStokes.ParticularWithinPressure
import NavierStokes.ParticularWithinBounds
import NavierStokes.GenericEndpointExtension

/-! # The slow-time-zero clause of the common-torus particular inverse

Uniform interior jets determine genuine closed-side smoothness. The actual
common-torus velocity and pressure inherit these one-sided jets, uniformly
on compact parameter sets. No analytic regularity or open extension of an
arbitrary source is required.
-/

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


omit [NormedSpace ℝ Y] [NormedSpace ℝ E] in
theorem tendstoUniformlyOn_of_joint_continuous {s : Set ℝ} {K : Set Y}
    {F : ℝ → Y → E} (hK : IsCompact K)
    (hF : ContinuousOn F.uncurry (s ×ˢ K)) {t : ℝ} (ht : t ∈ s) :
    TendstoUniformlyOn F (F t) (𝓝[s] t) K := by
  intro u hu
  obtain ⟨v, hv, hnear⟩ := hK.mem_uniformity_of_prod hF ht (symmetrize_mem_uniformity hu)
  filter_upwards [hv] with r hr y hy
  exact (hnear r hr y hy).2

end UniformJets

section CommonTorus

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

def slowDomain (W : Set X) : Set (ℝ × X) := Ici (0 : ℝ) ×ˢ W
def positiveDomain (W : Set X) : Set (ℝ × X) := Ioi (0 : ℝ) ×ˢ W

theorem slowDomain_convex {W : Set X} (hW : Convex ℝ W) :
    Convex ℝ (slowDomain W) := (convex_Ici 0).prod hW

theorem slowDomain_uniqueDiff {W : Set X} (hW : IsOpen W) :
    UniqueDiffOn ℝ (slowDomain W) := (uniqueDiffOn_Ici 0).prod hW.uniqueDiffOn

/-- The same construction is local in slow time; no values for τ≥T need
be smooth. This is the form used on compact sets with q>0. -/
theorem commonCoefficients_local_oneSided (t : TangentData (ℝ × X) ProblemStatement.Space)
    (f : (ℝ × X) × Plane → HarmonicCalculus.ComplexVector) (g : Geometry)
    {a b T : ℝ} (hab : a ≤ b) {W : Set X} (hW : IsOpen W) (hcW : Convex ℝ W)
    (hN : ContDiffOn ℝ ∞ t.normal ((Ico 0 T ×ˢ W) ×ˢ univ))
    (hNd : ContDiffOn ℝ ∞ t.normalDot ((Ico 0 T ×ˢ W) ×ˢ univ))
    (hK : ContDiffOn ℝ ∞ t.action ((Ico 0 T ×ˢ W) ×ˢ univ))
    (hδ : ContDiffOn ℝ ∞ t.damping ((Ico 0 T ×ˢ W) ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ f ((Ico 0 T ×ˢ W) ×ˢ univ))
    (hn : ∀ x ∈ (Ico 0 T ×ˢ W) ×ˢ univ, t.normal x ≠ 0)
    {κ : Plane → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hsupp : tsupport κ ⊆ univ ×ˢ Ioo a b) (frequency : ℝ) :
    ContDiffOn ℝ ∞ (commonVelocity t f g hab κ) ((Ico 0 T ×ˢ W) ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (commonPressure t f g hab κ frequency) ((Ico 0 T ×ˢ W) ×ˢ univ) :=
  commonCoefficients_contDiffOn_within t f g hab ((convex_Ico 0 T).prod hcW)
    ((uniqueDiffOn_Ico 0 T).prod hW.uniqueDiffOn) hN hNd hK hδ hf hn hκ hcκ hsupp frequency

/-- Uniform convergence of the actual interior mixed jets to the genuine
one-sided boundary jets on any compact transverse parameter set. -/
theorem uniform_endpoint_jets {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} (hT : 0 < T) {W : Set X} (hW : IsOpen W)
    {F : (ℝ × X) × Plane → E}
    (hF : ContDiffOn ℝ ∞ F ((Ico 0 T ×ˢ W) ×ˢ univ))
    {K : Set (X × Plane)} (hK : IsCompact K) (hKW : K ⊆ W ×ˢ univ) (n : ℕ) :
    TendstoUniformlyOn (fun τ z => iteratedFDeriv ℝ n F ((τ, z.1), z.2))
      (fun z => iteratedFDerivWithin ℝ n F ((Ico 0 T ×ˢ W) ×ˢ univ) ((0, z.1), z.2))
      (𝓝[>] (0 : ℝ)) K := by
  let S : Set ((ℝ × X) × Plane) := (Ico 0 T ×ˢ W) ×ˢ univ
  let J := iteratedFDerivWithin ℝ n F S
  have hS : UniqueDiffOn ℝ S := ((uniqueDiffOn_Ico 0 T).prod hW.uniqueDiffOn).prod uniqueDiffOn_univ
  have hJ : ContinuousOn J S := hF.continuousOn_iteratedFDerivWithin
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) hS
  have hjoint : ContinuousOn (fun z : ℝ × (X × Plane) => J ((z.1, z.2.1), z.2.2))
      (Ico 0 T ×ˢ K) :=
    hJ.comp ((continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd).continuousOn
      (fun _ hz => ⟨⟨hz.1, (hKW hz.2).1⟩, mem_univ _⟩)
  have hlim := tendstoUniformlyOn_of_joint_continuous
    (F := fun (τ : ℝ) (z : X × Plane) => J ((τ, z.1), z.2)) (s := Ico 0 T) hK hjoint
    (show (0 : ℝ) ∈ Ico 0 T from ⟨le_rfl, hT⟩)
  have hlim' : TendstoUniformlyOn (fun τ z => J ((τ, z.1), z.2))
      (fun z => J ((0, z.1), z.2)) (𝓝[Ioo 0 T] (0 : ℝ)) K :=
    fun u hu => (hlim u hu).filter_mono (nhdsWithin_mono _ Ioo_subset_Ico_self)
  rw [← nhdsWithin_Ioo_eq_nhdsGT hT]
  apply hlim'.congr
  filter_upwards [self_mem_nhdsWithin] with τ hτ z hz
  have hpoint : ((τ, z.1), z.2) ∈ (Ioo 0 T ×ˢ W) ×ˢ (univ : Set Plane) :=
    ⟨⟨hτ, (hKW hz).1⟩, mem_univ _⟩
  have hsub : (Ioo 0 T ×ˢ W) ×ˢ (univ : Set Plane) ⊆ S :=
    Set.prod_mono (Set.prod_mono Ioo_subset_Ico_self Subset.rfl) Subset.rfl
  exact iteratedFDerivWithin_eq_iteratedFDeriv hS
    (((hF.mono hsub).contDiffAt (((isOpen_Ioo.prod hW).prod isOpen_univ).mem_nhds hpoint)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)) (hsub hpoint)


/-- The paper's actual complex common-torus inverse, for arbitrary source
coefficients with one-sided slow regularity at τ=0. Primitive geometry and
source are the only smoothness inputs. -/
theorem commonCoefficients_oneSided (t : TangentData (ℝ × X) ProblemStatement.Space)
    (f : (ℝ × X) × Plane → HarmonicCalculus.ComplexVector) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) {W : Set X} (hW : IsOpen W) (hcW : Convex ℝ W)
    (hN : ContDiffOn ℝ ∞ t.normal (slowDomain W ×ˢ univ))
    (hNd : ContDiffOn ℝ ∞ t.normalDot (slowDomain W ×ˢ univ))
    (hK : ContDiffOn ℝ ∞ t.action (slowDomain W ×ˢ univ))
    (hδ : ContDiffOn ℝ ∞ t.damping (slowDomain W ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ f (slowDomain W ×ˢ univ))
    (hn : ∀ x ∈ slowDomain W ×ˢ univ, t.normal x ≠ 0)
    {κ : Plane → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hsupp : tsupport κ ⊆ univ ×ˢ Ioo a b) (frequency : ℝ) :
    ContDiffOn ℝ ∞ (commonVelocity t f g hab κ) (slowDomain W ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (commonPressure t f g hab κ frequency) (slowDomain W ×ˢ univ) :=
  commonCoefficients_contDiffOn_within t f g hab (slowDomain_convex hcW)
    (slowDomain_uniqueDiff hW) hN hNd hK hδ hf hn hκ hcκ hsupp frequency


end CommonTorus

end NavierStokes.ParticularOneSided

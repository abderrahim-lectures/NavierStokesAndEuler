import NavierStokes.GenericSolenoidalRealization
import NavierStokes.GenericSupportedPolynomial

/-! Merged from `NavierStokes.GenericFactorSupport` (in a section, so its `open`s cannot leak). -/
/-! Merged from `NavierStokes.GenericVelocityRates` (in a section, so its `open`s cannot leak). -/
section
noncomputable section

namespace NavierStokes.GenericDifferentialPolynomial

open Set Filter DiagonalResidual
open scoped Topology ContDiff

variable {D V W : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem rate_linear {l : Filter D} {q : D → ℝ} {U : Set D} {f : D → V}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (L : V →L[ℝ] W) {m : ℕ} {r : ℝ} (hr : JetRate l q f m r) :
    JetRate l q (fun x => L (f x)) m r := by
  obtain ⟨C, hC, hb⟩ := hr
  refine ⟨‖L‖ * C, mul_nonneg (norm_nonneg L) hC, ?_⟩
  filter_upwards [hlU, hb] with x hx hbx
  exact (ResidualStability.norm_jet_linear_map L hU hf hx m).trans
    ((mul_le_mul_of_nonneg_left hbx (norm_nonneg L)).trans_eq (mul_assoc _ _ _).symm)

end NavierStokes.GenericDifferentialPolynomial

namespace NavierStokes.GenericSolenoidalRealization

open Set Filter ProblemStatement DiagonalResidual GenericRealizationBounds GenericDifferentialPolynomial
open scoped Topology ContDiff BigOperators

def positiveStage (u0 : VelocityField) (A B : ℕ → VelocityField) (J : ℕ) : VelocityField :=
  fun w => u0 w + MixedDiagonalResidual.uncutVelocity
    (CutStageEstimates.positiveStages A) (CutStageEstimates.positiveStages B) J w

theorem positiveStage_smooth {u0 : VelocityField} {A B : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hu0 : ContDiffOn ℝ ∞ u0 U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U) (J : ℕ) :
    ContDiffOn ℝ ∞ (positiveStage u0 A B J) U :=
  hu0.add (MixedDiagonalResidual.uncutVelocity_smooth hU
    (CutStageEstimates.positiveStages_smooth hA) (CutStageEstimates.positiveStages_smooth hB) J)

/-- The scalar components of the literal solenoidal velocity have the
approximation data needed by every finite differential polynomial. The curl
costs one derivative; the power loss is independent of the truncation. -/
def velocity_component_approximation {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {u0 : VelocityField} {A B : ℕ → VelocityField} {U : Set SpaceTime}
    {l : Filter SpaceTime} (hU : IsOpen U) (hlU : ∀ᶠ w in l, w ∈ U)
    (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ w ∈ U, 0 < q w)
    (hlq : ∀ᶠ w in l, 0 < q w ∧ q w ≤ 1) (hqzero : Tendsto q l (𝓝 0))
    (hu0 : ContDiffOn ℝ ∞ u0 U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (g gain LA LB LAc LBc K0 : ℕ → ℝ)
    (CA PA CB PB : ℕ → ℕ → ℝ)
    (hrawA : CutStageEstimates.RawStageBounds q A g LA CA PA U)
    (hrawB : CutStageEstimates.RawStageBounds q B g LB CB PB U)
    (hg : ∀ j, 1 ≤ j → 0 ≤ g j) (hgain : Monotone gain)
    (hbase : ∀ m, JetRate l q u0 m (-K0 m))
    (hcutA : DiagonalJetBounds.CutStageBounds a q A gain LAc U)
    (hcutB : DiagonalJetBounds.CutStageBounds a q B gain LBc U) (i : Fin 3) :
    ApproximationRates l q (fun J => gain (J + 1))
      (fun w => positiveVelocity a q u0 A B w i)
      (fun J w => positiveStage u0 A B J w i) := by
  let loss : ℕ → ℝ := fun m => max (max (LA (m + 1) + 1) 0) (max (LB m + 1) (K0 m))
  have hprefixA : ∀ J, ContDiffOn ℝ ∞
      (DiagonalJetBounds.uncutPrefix (CutStageEstimates.positiveStages A) (J + 1)) U :=
    fun J => ContDiffOn.sum (fun j _ => CutStageEstimates.positiveStages_smooth hA j)
  have hprefixB : ∀ J, ContDiffOn ℝ ∞
      (DiagonalJetBounds.uncutPrefix (CutStageEstimates.positiveStages B) (J + 1)) U :=
    fun J => ContDiffOn.sum (fun j _ => CutStageEstimates.positiveStages_smooth hB j)
  have hstage := positiveStage_smooth hU hu0 hA hB
  have hvel : ContDiffOn ℝ ∞ (positiveVelocity a q u0 A B) U :=
    velocity_smooth ha hU hq hpos hu0 (CutStageEstimates.positiveStages_smooth hA)
      (CutStageEstimates.positiveStages_smooth hB)
  have hgrowth : ∀ J m, JetRate l q (positiveStage u0 A B J) m (-loss m) := by
    intro J m
    have hz : ∀ k, JetRate l q (fun _ : SpaceTime => (0 : Space)) k (-(0 : ℝ)) := by
      intro k
      exact ⟨0, le_rfl, Eventually.of_forall (fun _ => by simp)⟩
    have hAr := stage_growth hU hlU hlq hqzero contDiffOn_const hA hrawA hg hz J (m + 1)
    have hAr' : JetRate l q
        (DiagonalJetBounds.uncutPrefix (CutStageEstimates.positiveStages A) (J + 1)) (m + 1)
          (-max (LA (m + 1) + 1) 0) := by
      have heq : GenericRealizationBounds.stage (fun _ : SpaceTime => (0 : Space)) A J =
          DiagonalJetBounds.uncutPrefix (CutStageEstimates.positiveStages A) (J + 1) := by
        funext x
        simp only [GenericRealizationBounds.stage, zero_add]
      rw [heq] at hAr
      exact hAr
    have hCr := (hAr'.spatialCurl hU hlU (hprefixA J)).weaken hlq
      (neg_le_neg (le_max_left (max (LA (m + 1) + 1) 0) (max (LB m + 1) (K0 m))))
    have hBr := (stage_growth hU hlU hlq hqzero hu0 hB hrawB hg hbase J m).weaken hlq
      (neg_le_neg (le_max_right (max (LA (m + 1) + 1) 0) (max (LB m + 1) (K0 m))))
    have hCs : ContDiffOn ℝ ∞
        (SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix
          (CutStageEstimates.positiveStages A) (J + 1))) U :=
      fun x hx => (SpatialCurl.contDiffAt_spatialCurl
        ((hprefixA J).contDiffAt (hU.mem_nhds hx)) (by simp)).contDiffWithinAt
    exact (hCr.add hBr hU hlU hCs (hu0.add (hprefixB J))).congr_on hU hlU
      (fun x _ => by dsimp [positiveStage, MixedDiagonalResidual.uncutVelocity, stage]; abel)
  refine ⟨loss, MixedDiagonalResidual.velocityLoss LAc LBc, id, ?_, ?_⟩
  · intro J m
    exact rate_linear hU hlU (hstage J) (EuclideanSpace.proj i) (hgrowth J m)
  · intro m J hJ
    change m ≤ J at hJ
    have ht := MixedDiagonalResidual.velocity_tail_jetRate ha hU hpos hq
      (CutStageEstimates.positiveStages_smooth hA) (CutStageEstimates.positiveStages_smooth hB)
      hgain (CutStageEstimates.positiveStages_cut_bounds hcutA)
      (CutStageEstimates.positiveStages_cut_bounds hcutB) hlU hlq hqzero J m (by omega)
    have ht' : JetRate l q (fun w => positiveVelocity a q u0 A B w - positiveStage u0 A B J w) m
        (gain (J + 1) - MixedDiagonalResidual.velocityLoss LAc LBc m) :=
      ht.congr_on hU hlU (fun x _ => by
        dsimp [positiveVelocity, velocity, positiveStage, MixedDiagonalResidual.velocity]
        abel)
    exact (rate_linear hU hlU (hvel.sub (hstage J)) (EuclideanSpace.proj i) ht').congr_on hU hlU
      (fun x _ => by simp only [map_sub]; rfl)

/-- Exact geometric velocity tail. The fixed curl norm is absorbed by one
additional power of the small scale, uniformly in the truncation index. -/
theorem positiveVelocity_tail_bound {a : ℕ → ℝ} (hatop : Tendsto a atTop atTop)
    (hamono : Monotone a) (hapos : ∀ j, 0 < a j)
    {q : SpaceTime → ℝ} {u0 : VelocityField} {A B : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ w ∈ U, 0 < q w)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    {gain LA LB : ℕ → ℝ} (hg : Monotone gain)
    (hcutA : DiagonalJetBounds.CutStageBounds a q A gain LA U)
    (hcutB : DiagonalJetBounds.CutStageBounds a q B gain LB U)
    (hfirst : ‖SpatialCurl.curlLinear.comp (ResidualStability.spaceRestriction Space)‖ + 1 ≤ 2 * a 0)
    {x : SpaceTime} (hx : x ∈ U) (hqx1 : q x ≤ 1)
    (J m : ℕ) (hm : m ≤ J + 2) (hsmall : q x < 1 / (2 * a J)) :
    ‖iteratedFDeriv ℝ m (fun y => positiveVelocity a q u0 A B y - positiveStage u0 A B J y) x‖ ≤
      (1 / 2 : ℝ) ^ J * q x ^ (gain (J + 1) - (max (LA (m + 1)) (LB m) + 1)) := by
  let As := CutStageEstimates.positiveStages A
  let Bs := CutStageEstimates.positiveStages B
  let tailA := fun y => SolenoidalDiagonal.potentialSum a q As y - DiagonalJetBounds.uncutPrefix As (J + 1) y
  let tailB := fun y => SolenoidalDiagonal.potentialSum a q Bs y - DiagonalJetBounds.uncutPrefix Bs (J + 1) y
  have hAs := CutStageEstimates.positiveStages_smooth hA
  have hBs := CutStageEstimates.positiveStages_smooth hB
  have hsumA := SolenoidalDiagonal.potentialSum_contDiffOn hatop hU hpos hq hAs
  have hsumB := SolenoidalDiagonal.potentialSum_contDiffOn hatop hU hpos hq hBs
  have hpA : ContDiffOn ℝ ∞ (DiagonalJetBounds.uncutPrefix As (J + 1)) U :=
    ContDiffOn.sum (fun j _ => hAs j)
  have hpB : ContDiffOn ℝ ∞ (DiagonalJetBounds.uncutPrefix Bs (J + 1)) U :=
    ContDiffOn.sum (fun j _ => hBs j)
  have htA : ContDiffOn ℝ ∞ tailA U := hsumA.sub hpA
  have htB : ContDiffOn ℝ ∞ tailB U := hsumB.sub hpB
  have htAc : ContDiffOn ℝ ∞ (SpatialCurl.spatialCurl tailA) U :=
    fun y hy => (SpatialCurl.contDiffAt_spatialCurl (htA.contDiffAt (hU.mem_nhds hy)) (by simp)).contDiffWithinAt
  have heq : EqOn (fun y => SpatialCurl.spatialCurl tailA y + tailB y)
      (fun y => positiveVelocity a q u0 A B y - positiveStage u0 A B J y) U := by
    intro y hy
    change SpatialCurl.spatialCurl (fun z => SolenoidalDiagonal.potentialSum a q As z -
      DiagonalJetBounds.uncutPrefix As (J + 1) z) y + tailB y = _
    rw [spatialCurl_sub_on hU hsumA hpA hy]
    dsimp [tailB, positiveVelocity, velocity, positiveStage, MixedDiagonalResidual.uncutVelocity,
      SolenoidalDiagonal.velocitySum]
    dsimp only [As, Bs]
    abel
  have hAt := realized_tail_bound (base := fun _ : SpaceTime => (0 : Space)) hatop hamono hapos
    hU hq hA hg hcutA hx (hpos x hx) hqx1 J (m + 1) (by omega) hsmall
  have hBt := realized_tail_bound (base := fun _ : SpaceTime => (0 : Space)) hatop hamono hapos
    hU hq hB hg hcutB hx (hpos x hx) hqx1 J m (by omega) hsmall
  have hAt' : ‖iteratedFDeriv ℝ (m + 1) tailA x‖ ≤
      (1 / 2 : ℝ) ^ J * q x ^ (gain (J + 1) - LA (m + 1)) := by
    have he : (fun y => realized a q (fun _ : SpaceTime => (0 : Space)) A y -
        stage (fun _ : SpaceTime => (0 : Space)) A J y) = tailA := by
      funext y
      simp only [realized, stage, tailA, As, zero_add]
    rw [he] at hAt
    exact hAt
  have hBt' : ‖iteratedFDeriv ℝ m tailB x‖ ≤
      (1 / 2 : ℝ) ^ J * q x ^ (gain (J + 1) - LB m) := by
    have he : (fun y => realized a q (fun _ : SpaceTime => (0 : Space)) B y -
        stage (fun _ : SpaceTime => (0 : Space)) B J y) = tailB := by
      funext y
      simp only [realized, stage, tailB, Bs, zero_add]
    rw [he] at hBt
    exact hBt
  let K : ℝ := ‖SpatialCurl.curlLinear.comp (ResidualStability.spaceRestriction Space)‖
  let r : ℝ := gain (J + 1) - max (LA (m + 1)) (LB m)
  have hK : 0 ≤ K := norm_nonneg
    (SpatialCurl.curlLinear.comp (ResidualStability.spaceRestriction Space))
  have hpa : q x ^ (gain (J + 1) - LA (m + 1)) ≤ q x ^ r :=
    Real.rpow_le_rpow_of_exponent_ge (hpos x hx) hqx1
      (sub_le_sub_left (le_max_left _ _) _)
  have hpb : q x ^ (gain (J + 1) - LB m) ≤ q x ^ r :=
    Real.rpow_le_rpow_of_exponent_ge (hpos x hx) hqx1
      (sub_le_sub_left (le_max_right _ _) _)
  have hKq : (K + 1) * q x ≤ 1 := by
    have hqmul := (lt_div_iff₀ (mul_pos (by norm_num) (hapos J))).mp hsmall
    have hle : K + 1 ≤ 2 * a J := hfirst.trans (mul_le_mul_of_nonneg_left (hamono (Nat.zero_le J)) (by norm_num))
    have := mul_le_mul_of_nonneg_right hle (hpos x hx).le
    nlinarith
  have hpowEq : q x ^ r = q x * q x ^ (r - 1) := by
    calc
      _ = q x ^ (1 + (r - 1)) := by congr 1; ring
      _ = q x ^ (1 : ℝ) * q x ^ (r - 1) := Real.rpow_add (hpos x hx) _ _
      _ = _ := by rw [Real.rpow_one]
  have hpower : (K + 1) * q x ^ r ≤ q x ^ (r - 1) := by
    calc
      _ = ((K + 1) * q x) * q x ^ (r - 1) := by rw [hpowEq]; ring
      _ ≤ 1 * q x ^ (r - 1) := mul_le_mul_of_nonneg_right hKq (Real.rpow_nonneg (hpos x hx).le _)
      _ = _ := one_mul _
  rw [← ResidualStability.iteratedFDeriv_eqOn hU heq m hx]
  calc
    _ ≤ ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl tailA) x‖ + ‖iteratedFDeriv ℝ m tailB x‖ :=
      ResidualStability.norm_jet_add_le hU htAc htB hx m
    _ ≤ K * ((1 / 2 : ℝ) ^ J * q x ^ r) + (1 / 2 : ℝ) ^ J * q x ^ r := by
      apply add_le_add
      · exact (ResidualStability.norm_iteratedFDeriv_spatialCurl_le hU htA hx m).trans
          (mul_le_mul_of_nonneg_left (hAt'.trans (mul_le_mul_of_nonneg_left hpa (by positivity))) hK)
      · exact hBt'.trans (mul_le_mul_of_nonneg_left hpb (by positivity))
    _ = (1 / 2 : ℝ) ^ J * ((K + 1) * q x ^ r) := by ring
    _ ≤ (1 / 2 : ℝ) ^ J * q x ^ (r - 1) := mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = _ := by dsimp only [r]; congr 2; ring

end NavierStokes.GenericSolenoidalRealization
end

/-! Merged from `NavierStokes.GenericTupleRealization` (in a section, so its `open`s cannot leak). -/
section
noncomputable section

namespace NavierStokes.GenericTupleRealization

open Set Filter ProblemStatement DiagonalResidual GenericRealizationBounds GenericDifferentialPolynomial
open GenericSolenoidalRealization GenericRealization
open scoped Topology ContDiff BigOperators

abbrev Entry (κ : Type*) := Bool ⊕ κ

def Value {κ : Type*} : Entry κ → Type
  | .inl _ => Space
  | .inr _ => ℝ

instance {κ : Type*} (e : Entry κ) : NormedAddCommGroup (Value e) :=
  match e with
  | .inl _ => inferInstanceAs (NormedAddCommGroup Space)
  | .inr _ => inferInstanceAs (NormedAddCommGroup ℝ)

instance {κ : Type*} (e : Entry κ) : NormedSpace ℝ (Value e) :=
  match e with
  | .inl _ => inferInstanceAs (NormedSpace ℝ Space)
  | .inr _ => inferInstanceAs (NormedSpace ℝ ℝ)

def representatives {κ : Type*} (A B : ℕ → VelocityField) (R : κ → ℕ → PressureField) :
    ∀ e : Entry κ, ℕ → SpaceTime → Value e
  | .inl false => A
  | .inl true => B
  | .inr k => R k

/-- The optional scalar entries comprise pressure and any finite stress
components. Taking a singleton retains pressure alone. -/
def components {κ : Type*} (a : ℕ → ℝ) (q : SpaceTime → ℝ)
    (u0 : VelocityField) (s0 : κ → PressureField)
    (A B : ℕ → VelocityField) (R : κ → ℕ → PressureField) :
    Fin 3 ⊕ κ → PressureField
  | .inl i => fun w => positiveVelocity a q u0 A B w i
  | .inr k => realized a q (s0 k) (R k)

def stageComponents {κ : Type*} (u0 : VelocityField) (s0 : κ → PressureField)
    (A B : ℕ → VelocityField) (R : κ → ℕ → PressureField) (J : ℕ) :
    Fin 3 ⊕ κ → PressureField
  | .inl i => fun w => positiveStage u0 A B J w i
  | .inr k => stage (s0 k) (R k) J

structure Result {κ : Type*} (U : Set SpaceTime) (q : SpaceTime → ℝ)
    (u0 : VelocityField) (s0 : κ → PressureField)
    (A B : ℕ → VelocityField) (R : κ → ℕ → PressureField)
    (g L : ℕ → ℝ) (a : ℕ → ℕ) : Prop where
  positive : ∀ j, 0 < a j
  doubling : ∀ j, 2 * a j ≤ a (j + 1)
  monotone : StrictMono a
  tends : Tendsto (fun j => (a j : ℝ)) atTop atTop
  locallyFinite_representatives : ∀ e, LocallyFinite (fun j => Function.support
    (fun w : U => SolenoidalDiagonal.cutStage (fun j => (a j : ℝ)) q
      (CutStageEstimates.positiveStages (representatives A B R e)) j w))
  smooth_velocity : ContDiffOn ℝ ∞ (positiveVelocity (fun j => (a j : ℝ)) q u0 A B) U
  smooth_scalars : ∀ k, ContDiffOn ℝ ∞ (realized (fun j => (a j : ℝ)) q (s0 k) (R k)) U
  divergence : ∀ w ∈ U, spatialDivergence (positiveVelocity (fun j => (a j : ℝ)) q u0 A B) w.1 w.2 = 0
  approximation : ∀ i, Nonempty (ApproximationRates (scaleApproach U q) q (fun J => g (J + 1) / 2)
    (components (fun j => (a j : ℝ)) q u0 s0 A B R i) (fun J => stageComponents u0 s0 A B R J i))
  tail_velocity : ∀ w ∈ U, ∀ J m, m ≤ J + 2 → q w < 1 / (2 * (a J : ℝ)) →
    ‖iteratedFDeriv ℝ m (fun y => positiveVelocity (fun j => (a j : ℝ)) q u0 A B y -
      positiveStage u0 A B J y) w‖ ≤ (1 / 2 : ℝ) ^ J * q w ^
        (g (J + 1) / 2 - (max (CutStageEstimates.cutLoss L (m + 1)) (CutStageEstimates.cutLoss L m) + 1))
  tail_scalars : ∀ k w, w ∈ U → ∀ J m, m ≤ J + 3 → q w < 1 / (2 * (a J : ℝ)) →
    ‖iteratedFDeriv ℝ m (fun y => realized (fun j => (a j : ℝ)) q (s0 k) (R k) y -
      stage (s0 k) (R k) J y) w‖ ≤
      (1 / 2 : ℝ) ^ J * q w ^ (g (J + 1) / 2 - CutStageEstimates.cutLoss L m)
  outer_velocity : ∀ w, ContinuousAt q w → 1 / (a 0 : ℝ) < q w →
    positiveVelocity (fun j => (a j : ℝ)) q u0 A B =ᶠ[𝓝 w] u0
  outer_scalars : ∀ k w, ContinuousAt q w → 1 / (a 0 : ℝ) < q w →
    realized (fun j => (a j : ℝ)) q (s0 k) (R k) =ᶠ[𝓝 w] s0 k

/-- Simultaneous realization of the literal solenoidal velocity, pressure,
and arbitrary additional finite stress entries. All polynomial tests use
this same schedule and these same scalar components. -/
theorem exists_realization {κ : Type*} [Fintype κ] {U : Set SpaceTime}
    (hU : IsOpen U) {q : SpaceTime → ℝ} (hq : ContDiffOn ℝ ∞ q U)
    (hpos : ∀ w ∈ U, 0 < q w ∧ q w ≤ 1)
    (Bq : ℕ → ℝ) (hBq : ∀ k w, w ∈ U → q w ≤ 1 →
      ‖iteratedFDeriv ℝ k q w‖ ≤ Bq k * q w ^ (1 - (k : ℝ)))
    {u0 : VelocityField} {s0 : κ → PressureField}
    (hu0 : ContDiffOn ℝ ∞ u0 U) (hs0 : ∀ k, ContDiffOn ℝ ∞ (s0 k) U)
    (K0 : ℕ → ℝ) (Ks : κ → ℕ → ℝ)
    (hbaseU : ∀ m, JetRate (scaleApproach U q) q u0 m (-K0 m))
    (hbaseS : ∀ k m, JetRate (scaleApproach U q) q (s0 k) m (-Ks k m))
    {A B : ℕ → VelocityField} {R : κ → ℕ → PressureField}
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (hR : ∀ k j, 1 ≤ j → ContDiffOn ℝ ∞ (R k j) U)
    (g L : ℕ → ℝ) (C P : Entry κ → ℕ → ℕ → ℝ)
    (hraw : ∀ e, CutStageEstimates.RawStageBounds q (representatives A B R e) g L (C e) (P e) U)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (hgmono : Monotone g)
    (hdiv0 : ∀ w ∈ U, spatialDivergence u0 w.1 w.2 = 0)
    (hdivB : ∀ j, 1 ≤ j → ∀ w ∈ U, spatialDivergence (B j) w.1 w.2 = 0)
    (htan : ∀ j, 1 ≤ j → ∀ w ∈ U, ∑ i : Fin 3,
      fderiv ℝ (fun x : Space => q (w.1, x)) w.2 (coordinateVector i) * B j w i = 0)
    {τ : Type*} (tests : ℕ → Finset τ) (Bt Pt γ : ℕ → τ → ℝ)
    (hγ : ∀ j k, k ∈ tests j → 0 < γ j k) {q0 : ℝ} (hq0 : 0 < q0) :
    ∃ a : ℕ → ℕ, (∀ j, 1 / (a j : ℝ) < q0) ∧ Result U q u0 s0 A B R g L a ∧
      ∀ j k, k ∈ tests j → ∀ r : ℝ, 0 < r → r ≤ 1 / (a j : ℝ) →
        |DiagonalScale.logPowerWeight (Bt j k) (Pt j k) (γ j k) r| ≤ (1 / 2 : ℝ) ^ j := by
  obtain ⟨lower, hlower⟩ := exists_nat_ge
    ((‖SpatialCurl.curlLinear.comp (ResidualStability.spaceRestriction Space)‖ + 1) / 2)
  have hs : ∀ e j, 1 ≤ j → ContDiffOn ℝ ∞ (representatives A B R e j) U := by
    intro e j hj
    cases e with
    | inl b => cases b; exact hA j hj; exact hB j hj
    | inr k => exact hR k j hj
  obtain ⟨a, hlo, hap, had, ham, hat, hao, hab, hatest⟩ :=
    GenericDiagonalSchedule.exists_finite_diagonal_cut_bounds_with_tests hU Subset.rfl hq
      (fun w hw => (hpos w hw).1) Bq hBq hs g L C P hraw hg lower tests Bt Pt γ hγ hq0
  have haReal : Monotone (fun j => (a j : ℝ)) := fun i j hij => by
    change (a i : ℝ) ≤ (a j : ℝ)
    exact_mod_cast ham.monotone hij
  have hapReal : ∀ j, 0 < (a j : ℝ) := fun j => by exact_mod_cast hap j
  have hfirst : ‖SpatialCurl.curlLinear.comp (ResidualStability.spaceRestriction Space)‖ + 1 ≤ 2 * (a 0 : ℝ) := by
    have hloR : (lower : ℝ) ≤ (a 0 : ℝ) := by exact_mod_cast hlo
    linarith
  have hlU := eventually_domain U q
  have hlq := hlU.mono fun w hw => hpos w hw
  have hzero := scale_tendsto U q
  have hgHalf : Monotone (fun j => g j / 2) := fun i j hij => div_le_div_of_nonneg_right (hgmono hij) (by norm_num)
  have hcutA : DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ)) q A (fun j => g j / 2) (CutStageEstimates.cutLoss L) U := hab (.inl false)
  have hcutB : DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ)) q B (fun j => g j / 2) (CutStageEstimates.cutLoss L) U := hab (.inl true)
  have hcutR : ∀ k, DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ)) q (R k) (fun j => g j / 2) (CutStageEstimates.cutLoss L) U := fun k => hab (.inr k)
  have hu := velocity_smooth hat hU hq (fun w hw => (hpos w hw).1) hu0
    (CutStageEstimates.positiveStages_smooth hA) (CutStageEstimates.positiveStages_smooth hB)
  have hr := fun k => realized_smooth hU hq (fun w hw => (hpos w hw).1) hat (hs0 k) (hR k)
  refine ⟨a, hao, ?_, hatest⟩
  refine ⟨hap, had, ham, hat, ?_, hu, hr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    exact SolenoidalDiagonal.locallyFinite_cutStage_support_on hat hq.continuousOn
      (fun w hw => (hpos w hw).1) _
  · intro w hw
    exact positiveVelocity_divergence hat hU hq (fun w hw => (hpos w hw).1) hu0 hA hB hdiv0 hdivB htan hw
  · intro i
    cases i with
    | inl i =>
        exact ⟨velocity_component_approximation hat hU hlU hq (fun w hw => (hpos w hw).1)
          hlq hzero hu0 hA hB g (fun j => g j / 2) L L (CutStageEstimates.cutLoss L)
          (CutStageEstimates.cutLoss L) K0 (C (.inl false)) (P (.inl false)) (C (.inl true)) (P (.inl true))
          (hraw (.inl false)) (hraw (.inl true)) (fun j hj => (hg j hj).le) hgHalf hbaseU hcutA hcutB i⟩
    | inr k =>
        refine ⟨⟨fun m => max (L m + 1) (Ks k m), CutStageEstimates.cutLoss L, id, ?_, ?_⟩⟩
        · intro J m
          exact stage_growth hU hlU hlq hzero (hs0 k) (hR k) (hraw (.inr k))
            (fun j hj => (hg j hj).le) (hbaseS k) J m
        · intro m J hJ
          change m ≤ J at hJ
          exact realized_tail_jetRate hat hU hq (hR k) hgHalf (hcutR k) hlU hlq hzero J m (by omega)
  · intro w hw J m hm hsmall
    exact positiveVelocity_tail_bound hat haReal hapReal hU hq (fun w hw => (hpos w hw).1)
      hA hB hgHalf hcutA hcutB hfirst hw (hpos w hw).2 J m hm hsmall
  · intro k w hw J m hm hsmall
    exact realized_tail_bound hat haReal hapReal hU hq (hR k) hgHalf (hcutR k)
      hw (hpos w hw).1 (hpos w hw).2 J m hm hsmall
  · intro w hqw houter
    exact positiveVelocity_outer_germ haReal hapReal hqw houter u0 A B
  · intro k w hqw houter
    have hz := correction_eventually_zero haReal hapReal hqw houter (CutStageEstimates.positiveStages (R k))
    filter_upwards [hz] with y hy
    simp only [realized, hy, add_zero]

/-- Every finite differential polynomial of the realized physical tuple has
flat residual under the manuscript's finite-stage residual hypothesis.
The coefficient estimates are needed only on each term's common support. -/
theorem Result.flat_residual {κ : Type*} {U : Set SpaceTime} {q : SpaceTime → ℝ}
    {u0 : VelocityField} {s0 : κ → PressureField} {A B : ℕ → VelocityField}
    {R : κ → ℕ → PressureField} {g L : ℕ → ℝ} {a : ℕ → ℕ}
    (H : Result U q u0 s0 A B R g L a) (hU : IsOpen U)
    (hq : ∀ w ∈ U, 0 < q w ∧ q w ≤ 1)
    (hu0 : ContDiffOn ℝ ∞ u0 U) (hs0 : ∀ k, ContDiffOn ℝ ∞ (s0 k) U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (hR : ∀ k j, 1 ≤ j → ContDiffOn ℝ ∞ (R k j) U)
    (hgtop : Tendsto g atTop atTop) (P : SupportedPolynomial SpaceTime (Fin 3 ⊕ κ))
    (hconst : ContDiffOn ℝ ∞ P.constant U)
    (hc : ∀ t ∈ P.terms, ContDiffOn ℝ ∞ t.1 U)
    (region : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → Set SpaceTime)
    (Lc : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → ℕ → ℝ)
    (hcg : ∀ t ∈ P.terms, ∀ m, JetRate (scaleApproach U q ⊓ 𝓟 (region t)) q t.1 m (-Lc t m))
    (hzero : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      t.2.eval (fun k => Empty.elim k) (components (fun j => (a j : ℝ)) q u0 s0 A B R)
        =ᶠ[𝓝 x] (fun _ => 0))
    (hszero : ∀ t ∈ P.terms, ∀ J x, x ∈ U → x ∉ region t →
      t.2.eval (fun k => Empty.elim k) (stageComponents u0 s0 A B R J)
        =ᶠ[𝓝 x] (fun _ => 0))
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop atTop) (Lres : ℕ → ℝ)
    (hres : ∀ J m, JetRate (scaleApproach U q) q
      (P.eval (stageComponents u0 s0 A B R J)) m (rho J - Lres m)) (m : ℕ) (N : ℝ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ x ∈ U, 0 < q x → q x < δ →
      ‖iteratedFDeriv ℝ m (P.eval (components (fun j => (a j : ℝ)) q u0 s0 A B R)) x‖ ≤ C * q x ^ N := by
  have hlU := eventually_domain U q
  have hlq := hlU.mono fun w hw => hq w hw
  have hu : ∀ i, ContDiffOn ℝ ∞ (components (fun j => (a j : ℝ)) q u0 s0 A B R i) U := by
    intro i
    cases i with
    | inl i => exact (EuclideanSpace.proj i).contDiff.comp_contDiffOn H.smooth_velocity
    | inr k => exact H.smooth_scalars k
  have hus : ∀ J i, ContDiffOn ℝ ∞ (stageComponents u0 s0 A B R J i) U := by
    intro J i
    cases i with
    | inl i => exact (EuclideanSpace.proj i).contDiff.comp_contDiffOn (positiveStage_smooth hU hu0 hA hB J)
    | inr k => exact stage_smooth (hs0 k) (hR k) J
  have hgain : Tendsto (fun J => g (J + 1) / 2) atTop atTop :=
    (hgtop.comp (tendsto_add_atTop_nat 1)).atTop_div_const (by norm_num)
  exact uniform_bound_of_rate (P.flat_of_local_coefficients hU hlU hlq hu hus hgain hrho
    (fun i => (H.approximation i).some) hconst hc region Lc hcg hzero hszero Lres hres m N)

end NavierStokes.GenericTupleRealization
end

section
noncomputable section

namespace NavierStokes.GenericDifferentialPolynomial

open Set Filter
open scoped Topology ContDiff BigOperators

variable {D ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- A single Cartesian field factor. Coordinate vectors give the usual
multi-index derivatives; arbitrary fixed directions are also permitted. -/
inductive FieldFactor (D ι : Type*) where
  | input : ι → FieldFactor D ι
  | directional : D → FieldFactor D ι → FieldFactor D ι

def FieldFactor.expression : FieldFactor D ι → Expression D ι Empty
  | .input i => .input i
  | .directional v f => .directional v f.expression

def FieldFactor.eval (f : FieldFactor D ι) (u : ι → D → ℝ) : D → ℝ :=
  f.expression.eval (fun k => Empty.elim k) u

theorem FieldFactor.smooth_eval (f : FieldFactor D ι) {U : Set D}
    (hU : IsOpen U) {u : ι → D → ℝ} (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U) :
    ContDiffOn ℝ ∞ (f.eval u) U :=
  f.expression.smooth_eval hU (fun k => Empty.elim k) hu

theorem FieldFactor.congr_germ (f : FieldFactor D ι) {u v : ι → D → ℝ} {x : D}
    (h : ∀ i, u i =ᶠ[𝓝 x] v i) : f.eval u =ᶠ[𝓝 x] f.eval v := by
  induction f with
  | input i => exact h i
  | directional w f ih =>
      exact (ih.fderiv (𝕜 := ℝ)).mono (fun y hy => congrArg (fun L => L w) hy)

theorem FieldFactor.add_on (f : FieldFactor D ι) {U : Set D}
    (hU : IsOpen U) {u v : ι → D → ℝ}
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U) (hv : ∀ i, ContDiffOn ℝ ∞ (v i) U) :
    EqOn (f.eval (fun i x => u i x + v i x)) (fun x => f.eval u x + f.eval v x) U := by
  induction f with
  | input i => exact fun _ _ => rfl
  | directional w f ih =>
      intro x hx
      have he : f.eval (fun i x => u i x + v i x) =ᶠ[𝓝 x]
          (fun x => f.eval u x + f.eval v x) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact ih hy
      change fderiv ℝ (f.eval (fun i x => u i x + v i x)) x w =
        fderiv ℝ (f.eval u) x w + fderiv ℝ (f.eval v) x w
      rw [he.fderiv_eq, fderiv_fun_add
        (((f.smooth_eval hU hu).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
        (((f.smooth_eval hU hv).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
      rfl

theorem FieldFactor.zero (f : FieldFactor D ι) : f.eval (fun _ _ => 0) = (fun _ => 0) := by
  induction f with
  | input i => rfl
  | directional w f ih =>
      change (fun x => fderiv ℝ (f.eval (fun _ _ => 0)) x w) = _
      rw [ih]
      simp

theorem FieldFactor.sum_on (f : FieldFactor D ι) {U : Set D}
    (hU : IsOpen U) {σ : Type*} (s : Finset σ) {v : σ → ι → D → ℝ}
    (hv : ∀ j i, ContDiffOn ℝ ∞ (v j i) U) :
    EqOn (f.eval (fun i x => ∑ j ∈ s, v j i x)) (fun x => ∑ j ∈ s, f.eval (v j) x) U := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro x _
      simpa only [Finset.sum_empty] using congrFun f.zero x
  | @insert j s hj ih =>
      intro x hx
      have hadd := f.add_on hU (hv j) (fun i => ContDiffOn.sum (s := s) (fun k _ => hv k i)) hx
      simpa only [Finset.sum_insert hj, ih hx] using hadd

/-- Linearity propagates each field factor's support through the actual
locally finite sum. The neighborhoods for individual increments may differ. -/
theorem FieldFactor.zero_germ_of_local_sum (f : FieldFactor D ι)
    {U : Set D} (hU : IsOpen U) {x : D} (hx : x ∈ U)
    {u base : ι → D → ℝ} {inc : ℕ → ι → D → ℝ}
    (hb : ∀ i, ContDiffOn ℝ ∞ (base i) U)
    (hi : ∀ j i, ContDiffOn ℝ ∞ (inc j i) U)
    (hlocal : ∃ N, ∀ i, u i =ᶠ[𝓝 x] (fun y => base i y + ∑ j ∈ Finset.range N, inc j i y))
    (hbase : f.eval base =ᶠ[𝓝 x] (fun _ => 0))
    (hinc : ∀ j, f.eval (inc j) =ᶠ[𝓝 x] (fun _ => 0)) :
    f.eval u =ᶠ[𝓝 x] (fun _ => 0) := by
  obtain ⟨N, hN⟩ := hlocal
  have he := f.congr_germ hN
  have hs : ∀ᶠ y in 𝓝 x, ∀ j ∈ Finset.range N, f.eval (inc j) y = 0 :=
    (Filter.eventually_all_finset (Finset.range N)).mpr (fun j _ => hinc j)
  filter_upwards [he, hbase, hs, hU.mem_nhds hx] with y hy hyb hys hyU
  rw [hy]
  change f.eval (fun i z => base i z + ∑ j ∈ Finset.range N, inc j i z) y = 0
  have ha := f.add_on hU hb (fun i => ContDiffOn.sum (s := Finset.range N) (fun j _ => hi j i)) hyU
  calc
    _ = f.eval base y + f.eval (fun i z => ∑ j ∈ Finset.range N, inc j i z) y := ha
    _ = f.eval base y + ∑ j ∈ Finset.range N, f.eval (inc j) y :=
      congrArg (fun z => f.eval base y + z) (f.sum_on hU (Finset.range N) hi hyU)
    _ = 0 := by rw [hyb, Finset.sum_eq_zero hys, add_zero]

/-- Each leaf records the support of one differentiated field factor in the
base and every increment. Multiplication constructs arbitrary positive-degree
monomials without requiring undifferentiated components to share the support. -/
inductive FactorSupportAt (base : ι → D → ℝ) (inc : ℕ → ι → D → ℝ) (x : D) :
    Expression D ι Empty → Prop where
  | factor (f : FieldFactor D ι)
      (base_zero : f.eval base =ᶠ[𝓝 x] (fun _ => 0))
      (increment_zero : ∀ j, f.eval (inc j) =ᶠ[𝓝 x] (fun _ => 0)) :
      FactorSupportAt base inc x f.expression
  | mul {e f : Expression D ι Empty} :
      FactorSupportAt base inc x e → FactorSupportAt base inc x f →
      FactorSupportAt base inc x (.mul e f)

theorem FactorSupportAt.factor_of_tsupport {base : ι → D → ℝ} {inc : ℕ → ι → D → ℝ}
    (f : FieldFactor D ι) {S U : Set D} {x : D} (hx : x ∈ U) (hxs : x ∉ S)
    (hb : tsupport (f.eval base) ∩ U ⊆ S)
    (hi : ∀ j, tsupport (f.eval (inc j)) ∩ U ⊆ S) :
    FactorSupportAt base inc x f.expression := by
  apply FactorSupportAt.factor f
  · exact notMem_tsupport_iff_eventuallyEq.mp (fun h => hxs (hb ⟨h, hx⟩))
  · intro j
    exact notMem_tsupport_iff_eventuallyEq.mp (fun h => hxs (hi j ⟨h, hx⟩))

theorem FactorSupportAt.zero_germ {U : Set D} (hU : IsOpen U) {x : D} (hx : x ∈ U)
    {u base : ι → D → ℝ} {inc : ℕ → ι → D → ℝ} {e : Expression D ι Empty}
    (h : FactorSupportAt base inc x e)
    (hb : ∀ i, ContDiffOn ℝ ∞ (base i) U)
    (hi : ∀ j i, ContDiffOn ℝ ∞ (inc j i) U)
    (hlocal : ∃ N, ∀ i, u i =ᶠ[𝓝 x] (fun y => base i y + ∑ j ∈ Finset.range N, inc j i y)) :
    e.eval (fun k => Empty.elim k) u =ᶠ[𝓝 x] (fun _ => 0) := by
  induction h with
  | factor f hbase hinc => exact f.zero_germ_of_local_sum hU hx hb hi hlocal hbase hinc
  | mul he hf ihe ihf =>
      filter_upwards [ihe, ihf] with y hy hz
      simp only [Expression.eval, hy, hz, mul_zero]

end NavierStokes.GenericDifferentialPolynomial
end

noncomputable section

namespace NavierStokes.GenericTupleRealization

open Set Filter ProblemStatement GenericSolenoidalRealization GenericDifferentialPolynomial
open GenericRealizationBounds GenericRealization SolenoidalDiagonal
open scoped Topology ContDiff BigOperators

def baseComponents {κ : Type*} (u0 : VelocityField) (s0 : κ → PressureField) :
    Fin 3 ⊕ κ → PressureField
  | .inl i => fun w => u0 w i
  | .inr k => s0 k

def incrementComponents {κ : Type*} (A B : ℕ → VelocityField)
    (R : κ → ℕ → PressureField) (j : ℕ) : Fin 3 ⊕ κ → PressureField
  | .inl i => fun w => (SpatialCurl.spatialCurl (CutStageEstimates.positiveStages A j) w +
      CutStageEstimates.positiveStages B j w) i
  | .inr k => CutStageEstimates.positiveStages (R k) j

def cutIncrementComponents {κ : Type*} (a : ℕ → ℝ) (q : SpaceTime → ℝ)
    (A B : ℕ → VelocityField) (R : κ → ℕ → PressureField) (j : ℕ) : Fin 3 ⊕ κ → PressureField
  | .inl i => fun w => (SpatialCurl.spatialCurl (cutStage a q (CutStageEstimates.positiveStages A) j) w +
      cutStage a q (CutStageEstimates.positiveStages B) j w) i
  | .inr k => cutStage a q (CutStageEstimates.positiveStages (R k)) j

theorem smooth_baseComponents {κ : Type*} {U : Set SpaceTime}
    {u0 : VelocityField} {s0 : κ → PressureField}
    (hu0 : ContDiffOn ℝ ∞ u0 U) (hs0 : ∀ k, ContDiffOn ℝ ∞ (s0 k) U) :
    ∀ i, ContDiffOn ℝ ∞ (baseComponents u0 s0 i) U := by
  intro i
  cases i with
  | inl i => exact (EuclideanSpace.proj i).contDiff.comp_contDiffOn hu0
  | inr k => exact hs0 k

theorem smooth_incrementComponents {κ : Type*} {U : Set SpaceTime} (hU : IsOpen U)
    {A B : ℕ → VelocityField} {R : κ → ℕ → PressureField}
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (hR : ∀ k j, 1 ≤ j → ContDiffOn ℝ ∞ (R k j) U) :
    ∀ j i, ContDiffOn ℝ ∞ (incrementComponents A B R j i) U := by
  intro j i
  have ha := CutStageEstimates.positiveStages_smooth hA j
  have hb := CutStageEstimates.positiveStages_smooth hB j
  cases i with
  | inl i =>
      have hcurl : ContDiffOn ℝ ∞ (SpatialCurl.spatialCurl (CutStageEstimates.positiveStages A j)) U :=
        fun w hw => (SpatialCurl.contDiffAt_spatialCurl (ha.contDiffAt (hU.mem_nhds hw)) (by simp)).contDiffWithinAt
      exact (EuclideanSpace.proj i).contDiff.comp_contDiffOn (hcurl.add hb)
  | inr k => exact CutStageEstimates.positiveStages_smooth (hR k) j

theorem smooth_cutIncrementComponents {κ : Type*} {U : Set SpaceTime} (hU : IsOpen U)
    {a : ℕ → ℝ} {q : SpaceTime → ℝ} (hq : ContDiffOn ℝ ∞ q U)
    {A B : ℕ → VelocityField} {R : κ → ℕ → PressureField}
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (hR : ∀ k j, 1 ≤ j → ContDiffOn ℝ ∞ (R k j) U) :
    ∀ j i, ContDiffOn ℝ ∞ (cutIncrementComponents a q A B R j i) U := by
  have hs {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
      {F : ℕ → SpaceTime → W} (hF : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (F j) U) (j : ℕ) :
      ContDiffOn ℝ ∞ (cutStage a q (CutStageEstimates.positiveStages F) j) U := by
    intro w hw
    exact (cutStage_contDiffAt (hq.contDiffAt (hU.mem_nhds hw))
      (fun k => (CutStageEstimates.positiveStages_smooth hF k).contDiffAt (hU.mem_nhds hw)) j).contDiffWithinAt
  intro j i
  cases i with
  | inl i =>
      have hcurl : ContDiffOn ℝ ∞ (SpatialCurl.spatialCurl (cutStage a q (CutStageEstimates.positiveStages A) j)) U :=
        fun w hw => (SpatialCurl.contDiffAt_spatialCurl ((hs hA j).contDiffAt (hU.mem_nhds hw)) (by simp)).contDiffWithinAt
      exact (EuclideanSpace.proj i).contDiff.comp_contDiffOn (hcurl.add (hs hB j))
  | inr k => exact hs (hR k) j

private theorem spatialCurl_sum_on {U : Set SpaceTime} (hU : IsOpen U)
    {A : ℕ → VelocityField} (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U)
    (N : ℕ) {w : SpaceTime} (hw : w ∈ U) :
    SpatialCurl.spatialCurl (fun y => ∑ j ∈ Finset.range N, A j y) w =
      ∑ j ∈ Finset.range N, SpatialCurl.spatialCurl (A j) w := by
  have hd : ∀ j ∈ Finset.range N, DifferentiableAt ℝ (fun x : Space => A j (w.1, x)) w.2 := by
    intro j _
    exact (((hA j).contDiffAt (hU.mem_nhds hw)).comp w.2
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  simpa only [SpatialCurl.spatialCurl, SpatialCurl.curl, map_sum] using
    congrArg SpatialCurl.curlLinear (fderiv_fun_sum hd)

/-- The finite stages are the base plus precisely the uncut physical
increments, including the curl of each potential. -/
theorem stageComponents_local_sum {κ : Type*} {U : Set SpaceTime} (hU : IsOpen U)
    {u0 : VelocityField} {s0 : κ → PressureField} {A B : ℕ → VelocityField}
    {R : κ → ℕ → PressureField} (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (J : ℕ) {x : SpaceTime} (hx : x ∈ U) :
    ∃ N, ∀ i, stageComponents u0 s0 A B R J i =ᶠ[𝓝 x]
      (fun y => baseComponents u0 s0 i y + ∑ j ∈ Finset.range N, incrementComponents A B R j i y) := by
  refine ⟨J + 1, ?_⟩
  intro i
  filter_upwards [hU.mem_nhds hx] with y hy
  cases i with
  | inl i =>
      have hc := spatialCurl_sum_on hU (CutStageEstimates.positiveStages_smooth hA) (J + 1) hy
      have hv : positiveStage u0 A B J y = u0 y + ∑ j ∈ Finset.range (J + 1),
          (SpatialCurl.spatialCurl (CutStageEstimates.positiveStages A j) y + CutStageEstimates.positiveStages B j y) := by
        dsimp only [positiveStage, MixedDiagonalResidual.uncutVelocity, DiagonalJetBounds.uncutPrefix]
        change u0 y + (SpatialCurl.spatialCurl (fun z => ∑ j ∈ Finset.range (J + 1),
          CutStageEstimates.positiveStages A j z) y + _) = _
        rw [hc, Finset.sum_add_distrib]
      simpa only [stageComponents, baseComponents, incrementComponents, map_add, map_sum,
        EuclideanSpace.proj, PiLp.proj_apply, PiLp.add_apply] using
        congrArg (EuclideanSpace.proj i) hv
  | inr k => rfl

/-- A single local prefix works simultaneously for all physical components.
It is chosen from the scale alone, before taking any derivatives. -/
theorem components_local_sum {κ : Type*} {U : Set SpaceTime} (hU : IsOpen U)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {q : SpaceTime → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ w ∈ U, 0 < q w)
    {u0 : VelocityField} {s0 : κ → PressureField} {A B : ℕ → VelocityField}
    {R : κ → ℕ → PressureField} (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    {x : SpaceTime} (hx : x ∈ U) :
    ∃ N, ∀ i, components a q u0 s0 A B R i =ᶠ[𝓝 x]
      (fun y => baseComponents u0 s0 i y + ∑ j ∈ Finset.range N, cutIncrementComponents a q A B R j i y) := by
  obtain ⟨N, hN⟩ := SmoothCutoffs.scaledCutoffs_zero_on_common_neighborhood a ha (hpos x hx)
  have hz : ∀ᶠ y in 𝓝 x, ∀ j, N ≤ j → SmoothCutoffs.scaledCutoff (a j) (q y) = 0 := by
    filter_upwards [(hq.contDiffAt (hU.mem_nhds hx)).continuousAt
      (lt_mem_nhds (half_lt_self (hpos x hx)))] with y hy
    exact fun j hj => hN j hj (q y) hy
  have hp {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : ℕ → SpaceTime → W) :
      potentialSum a q F =ᶠ[𝓝 x] partialPotential a q F N := by
    filter_upwards [hz] with y hy
    apply tsum_eq_sum
    intro j hj
    simp only [cutStage, hy j (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj)), zero_smul]
  have hc := spatialCurl_eventuallyEq (hp (CutStageEstimates.positiveStages A))
  refine ⟨N, ?_⟩
  intro i
  cases i with
  | inl i =>
      filter_upwards [hc, hp (CutStageEstimates.positiveStages B), hU.mem_nhds hx] with y hcy hby hy
      have hv : positiveVelocity a q u0 A B y = u0 y + ∑ j ∈ Finset.range N,
          (SpatialCurl.spatialCurl (cutStage a q (CutStageEstimates.positiveStages A) j) y +
            cutStage a q (CutStageEstimates.positiveStages B) j y) := by
        dsimp only [positiveVelocity, velocity, velocitySum]
        rw [hcy, spatialCurl_partialPotential (hq.contDiffAt (hU.mem_nhds hy))
          (fun j => (CutStageEstimates.positiveStages_smooth hA j).contDiffAt (hU.mem_nhds hy)), hby]
        simp only [partialPotential, Finset.sum_add_distrib]
        abel
      simpa only [components, baseComponents, cutIncrementComponents, map_add, map_sum,
        EuclideanSpace.proj, PiLp.proj_apply, PiLp.add_apply] using
        congrArg (EuclideanSpace.proj i) hv
  | inr k =>
      filter_upwards [hp (CutStageEstimates.positiveStages (R k))] with y hy
      exact congrArg (fun z => s0 k y + z) hy

/-- The paper's primitive common-support assumptions suffice: each
differentiated factor is supported there in the base and in each raw and cut
increment. Support of the final sum is proved, not assumed. -/
theorem Result.flat_residual_of_factor_support {κ : Type*} {U : Set SpaceTime} {q : SpaceTime → ℝ}
    {u0 : VelocityField} {s0 : κ → PressureField} {A B : ℕ → VelocityField}
    {R : κ → ℕ → PressureField} {g L : ℕ → ℝ} {a : ℕ → ℕ}
    (H : Result U q u0 s0 A B R g L a) (hU : IsOpen U)
    (hqs : ContDiffOn ℝ ∞ q U) (hq : ∀ w ∈ U, 0 < q w ∧ q w ≤ 1)
    (hu0 : ContDiffOn ℝ ∞ u0 U) (hs0 : ∀ k, ContDiffOn ℝ ∞ (s0 k) U)
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) U)
    (hR : ∀ k j, 1 ≤ j → ContDiffOn ℝ ∞ (R k j) U)
    (hgtop : Tendsto g atTop atTop) (P : SupportedPolynomial SpaceTime (Fin 3 ⊕ κ))
    (hconst : ContDiffOn ℝ ∞ P.constant U) (hc : ∀ t ∈ P.terms, ContDiffOn ℝ ∞ t.1 U)
    (region : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → Set SpaceTime)
    (Lc : ((SpaceTime → ℝ) × Expression SpaceTime (Fin 3 ⊕ κ) Empty) → ℕ → ℝ)
    (hcg : ∀ t ∈ P.terms, ∀ m, DiagonalResidual.JetRate (scaleApproach U q ⊓ 𝓟 (region t)) q t.1 m (-Lc t m))
    (hrawsupport : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      FactorSupportAt (baseComponents u0 s0) (incrementComponents A B R) x t.2)
    (hcutsupport : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      FactorSupportAt (baseComponents u0 s0) (cutIncrementComponents (fun j => (a j : ℝ)) q A B R) x t.2)
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop atTop) (Lres : ℕ → ℝ)
    (hres : ∀ J m, DiagonalResidual.JetRate (scaleApproach U q) q
      (P.eval (stageComponents u0 s0 A B R J)) m (rho J - Lres m)) (m : ℕ) (N : ℝ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ x ∈ U, 0 < q x → q x < δ →
      ‖iteratedFDeriv ℝ m (P.eval (components (fun j => (a j : ℝ)) q u0 s0 A B R)) x‖ ≤ C * q x ^ N := by
  apply H.flat_residual hU hq hu0 hs0 hA hB hR hgtop P hconst hc region Lc hcg
    _ _ rho hrho Lres hres m N
  · intro t ht x hx hxs
    exact (hcutsupport t ht x hx hxs).zero_germ hU hx (smooth_baseComponents hu0 hs0)
      (smooth_cutIncrementComponents hU hqs hA hB hR)
      (components_local_sum hU H.tends hqs (fun w hw => (hq w hw).1) hA hx)
  · intro t ht J x hx hxs
    exact (hrawsupport t ht x hx hxs).zero_germ hU hx (smooth_baseComponents hu0 hs0)
      (smooth_incrementComponents hU hA hB hR) (stageComponents_local_sum hU hA J hx)

end NavierStokes.GenericTupleRealization

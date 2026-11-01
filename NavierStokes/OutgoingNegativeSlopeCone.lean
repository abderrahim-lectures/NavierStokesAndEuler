import NavierStokes.OutgoingCone

/-! # The admissible cone starts during the negative-slope transition

The literal schedule has negative logarithmic slope immediately after
`dropLength + 1`. Its actual radial cone coefficient is then greater than
two. Combining this identity with the already constructed relaxed cone
gives the missing transition interval, with the same profile and radius.
-/

noncomputable section

open Set
open scoped Topology

namespace NavierStokes.OutgoingNegativeSlopeCone

open OutgoingSchedule OutgoingTail OutgoingCone
open UniformAngularReset (ResetWitness)
open OutgoingEntranceCone (coneA)

theorem sigma_pos {x : ℝ} (hx : 0 < x) : 0 < sigma x :=
  div_pos (FlatCutoff.edge_pos 1 hx) (sigma_denom_pos x)

/-- This is the sign of the prescribed smooth schedule itself, not an
assumed inequality for a free slope function. -/
theorem slope_neg_iff (c : Parameters) (y : ℝ) :
    slope c.dropLength c.lam y < 0 ↔ c.dropLength + 1 < y := by
  constructor
  · intro hneg
    by_contra hy
    have hy' : y ≤ c.dropLength + 1 := le_of_not_gt hy
    have hstep : sigma (y - (c.dropLength + 1)) = 0 := sigma_zero (by linarith)
    have hnonneg : 0 ≤ (3 / 5 : ℝ) * (1 - sigma y) :=
      mul_nonneg (by norm_num) (sub_nonneg.mpr (sigma_le_one y))
    simp only [OutgoingSchedule.slope, hstep, mul_zero, sub_zero] at hneg
    exact (not_lt_of_ge hnonneg) hneg
  · intro hy
    have hy1 : 1 ≤ y := by linarith [c.dropLength_pos]
    have hstep : 0 < sigma (y - (c.dropLength + 1)) := sigma_pos (by linarith)
    simp only [OutgoingSchedule.slope, sigma_one hy1, sub_self, mul_zero, zero_sub]
    exact neg_neg_of_pos (mul_pos c.lam_pos hstep)


theorem coneA_gt_two_of_negative_slope {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y : ℝ} (hy : y < d.core.endpoint) (eta : ℝ)
    (hneg : slope d.core.dropLength d.core.lam y < 0) : 2 < coneA w (y, eta) := by
  rw [OutgoingEntranceCone.coneA_before w hy]
  dsimp only [OutgoingEntranceCone.radialA]
  linarith

/-- No shear estimate is added: the existing normalized radial identity
already dominates the radial coefficient for every actual shear value. -/
theorem true_of_relaxed_negative_slope {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (Amp : ℝ → ℝ) {XR y eta : ℝ}
    (hrelaxed : RelaxedAt w Amp XR (y, eta)) (hy : y < d.core.endpoint)
    (hneg : slope d.core.dropLength d.core.lam y < 0) :
    TrueAt w Amp XR (y, eta) :=
  ⟨hrelaxed, normalV_gt_two_of_radial w Amp (y, eta)
    (coneA_gt_two_of_negative_slope w hy eta hneg)⟩

def trueWindowFromTransition (d : TailData) : Set (ℝ × ℝ) :=
  Ioc (d.core.dropLength + 1) (cleanEnd d) ×ˢ Icc (-1) 1

/-- Every constructed clean cone already satisfies the full paper clause:
the admissible cone begins as soon as the incoming transition slope is
negative, one unit before the constant-slope interval begins. -/
theorem true_from_transition {d : TailData} {K XR left : ℝ}
    {w : ResetWitness d K} (h : CleanOutgoingCone w XR left) (hleft : left ≤ 0) :
    ∀ p ∈ trueWindowFromTransition d,
      TrueAt w (CorrectedPulseAmplitude.amplitude d w.coefficients) XR p := by
  rintro ⟨y, eta⟩ hp
  by_cases hy : d.core.holdStart ≤ y
  · exact h.true_from_hold (y, eta) ⟨⟨hy, hp.1.2⟩, hp.2⟩
  · have hneg : slope d.core.dropLength d.core.lam y < 0 :=
      (slope_neg_iff d.core y).mpr hp.1.1
    have hy0 : 0 < y := by linarith [d.core.dropLength_pos, hp.1.1]
    have hyend : y < d.core.endpoint := by
      have hh := d.core.pulseStart_ge_hold
      have hpulse := d.core.pulseLength_pos
      dsimp only [Parameters.endpoint]
      linarith
    exact true_of_relaxed_negative_slope w _
      (h.relaxed (y, eta) ⟨⟨hleft.trans hy0.le, hp.1.2⟩, hp.2⟩) hyend hneg


structure FullCleanOutgoingCone {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (XR left : ℝ) : Prop extends CleanOutgoingCone w XR left where
  true_from_transition : ∀ p ∈ trueWindowFromTransition d,
    TrueAt w (CorrectedPulseAmplitude.amplitude d w.coefficients) XR p

theorem full_of_clean {d : TailData} {K XR left : ℝ} {w : ResetWitness d K}
    (h : CleanOutgoingCone w XR left) (hleft : left ≤ 0) : FullCleanOutgoingCone w XR left :=
  ⟨h, true_from_transition h hleft⟩



end NavierStokes.OutgoingNegativeSlopeCone

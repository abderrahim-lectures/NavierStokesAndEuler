import NavierStokes.ModulatedProfileAssembly
import NavierStokes.PrimaryRepresentatives
import NavierStokes.LeadingStress
import NavierStokes.BaseChartJets
import NavierStokes.EntranceAlignedBase

/-!
# The spectral cone of the actual aligned modulated base

This module binds the generic profile and physical-shear identities to the
same finite modulation, aligned coefficient family, and covariance target.
-/
/-! Merged from `NavierStokes.ProfileSpectralCone`. -/
/-!
# From the actual profile cone to the primary spectral cone

The signed axial shear in the profile cone is `c = -2 X U_X / E`.
Consequently the physical shear vector is `F * (-a,-c)`, while the
leading stress is a positive multiple of `(p₁-a,p₂-c)`.  The results
below derive the primary spectral and target cones from these identities.
-/

noncomputable section

namespace NavierStokes.ProfileSpectralCone

open Set Function Filter
open scoped ContDiff Topology InnerProductSpace


abbrev Plane := MovingFrameODE.Plane
abbrev Slow := PhaseCalculus.Slow

private theorem shear_size_mul {a c : ℝ} (ha : a ≠ 0) :
    a * (a * (1 + (c / a) ^ 2)) = a ^ 2 + c ^ 2 := by
  field_simp

theorem referenceCone_of_trueCone {F p₁ p₂ a c : ℝ} (hF : 0 < F)
    (h : TrueConeLoop.InTrueCone p₁ p₂ a c) :
    PrimaryRepresentatives.ReferenceCone F (F • !₂[-a, -c]) := by
  apply PrimaryRepresentatives.referenceCone_of_shear_coordinates hF h.1
  have he := shear_size_mul (c := c) h.1.ne'
  have hm := mul_lt_mul_of_pos_left h.2.1 h.1
  nlinarith

/-- The square of the actual unstable eigenvector slope. -/
theorem c0_sq_signedShear {F a c : ℝ} (hF : 0 < F) (ha : 0 < a)
    (hv : 2 < a * (1 + (c / a) ^ 2)) :
    PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) ^ 2 = (a * (1 + (c / a) ^ 2) - 2) / 2 := by
  have ho : 2 * a < a ^ 2 + (-c) ^ 2 := by
    have he := shear_size_mul (c := c) ha.ne'
    have hm := mul_lt_mul_of_pos_left hv ha
    nlinarith
  have hr := PrimaryRepresentatives.referenceCone_of_shear_coordinates hF ha ho
  have hn0 : ‖F • !₂[-a, -c]‖ ≠ 0 := norm_ne_zero_iff.mpr hr.shear_ne_zero
  have hn : ‖F • !₂[-a, -c]‖ ^ 2 = F ^ 2 * (a ^ 2 + c ^ 2) := by
    have hh := ViscousPropagator.plane_norm_sq (F • !₂[-a, -c])
    change ‖F • !₂[-a, -c]‖ ^ 2 = (F * -a) ^ 2 + (F * -c) ^ 2 at hh
    rw [hh]
    ring
  have he : PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) ^ 2 =
      -(PrimaryRepresentatives.coupling F (F • !₂[-a, -c]) + ‖F • !₂[-a, -c]‖) /
        PrimaryRepresentatives.coupling F (F • !₂[-a, -c]) := by
    rw [PrimaryRepresentatives.c0, div_pow, hr.lambda0_sq]
    field_simp [hr.coupling_neg.ne]
  rw [he, PrimaryRepresentatives.coupling_eq]
  change -((2 * F * (F * -a)) / ‖F • !₂[-a, -c]‖ + ‖F • !₂[-a, -c]‖) /
      ((2 * F * (F * -a)) / ‖F • !₂[-a, -c]‖) = _
  field_simp [hF.ne', ha.ne', hn0]
  nlinarith [hn]

/-- Projection of the actual stress coordinates onto the normal. -/
theorem stress_inner_normal (F τ p₁ p₂ a c : ℝ) (ha : a ≠ 0) :
    ⟪τ • !₂[p₁ - a, p₂ - c], PrimaryRepresentatives.normalDirection (F • !₂[-a, -c])⟫_ℝ =
      -(τ * F * a / ‖F • !₂[-a, -c]‖) *
        (p₁ + p₂ * (c / a) - a * (1 + (c / a) ^ 2)) := by
  have he : a * (p₁ + p₂ * (c / a) - a * (1 + (c / a) ^ 2)) =
      a * p₁ + c * p₂ - a ^ 2 - c ^ 2 := by
    field_simp ; ring
  calc
    _ = -(τ * F / ‖F • !₂[-a, -c]‖) *
        (a * p₁ + c * p₂ - a ^ 2 - c ^ 2) := by
      simp [PrimaryRepresentatives.normalDirection, PiLp.inner_apply, Fin.sum_univ_two]
      ring
    _ = _ := by rw [← he]; ring

/-- Projection onto the fixed transverse orientation `-quarterTurn N`. -/
theorem stress_inner_transverse (F τ p₁ p₂ a c : ℝ) (ha : a ≠ 0) :
    ⟪τ • !₂[p₁ - a, p₂ - c], PrimaryRepresentatives.transverseDirection (F • !₂[-a, -c])⟫_ℝ =
      (τ * F * a / ‖F • !₂[-a, -c]‖) * (p₂ - p₁ * (c / a)) := by
  have he : a * (p₂ - p₁ * (c / a)) = a * p₂ - c * p₁ := by
    field_simp
  calc
    _ = (τ * F / ‖F • !₂[-a, -c]‖) * (a * p₂ - c * p₁) := by
      simp [PrimaryRepresentatives.transverseDirection, PrimaryRepresentatives.normalDirection,
        MovingFrameODE.quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
      ring
    _ = _ := by rw [← he]; ring

private theorem cancel_signed_scale (q k j d : ℝ) (hk : k ≠ 0) :
    q * (k * j) / (-k * d) = -(q * j / d) := by
  rw [neg_mul, div_neg]
  congr 1
  calc
    q * (k * j) / (k * d) = k * (q * j) / (k * d) := by ring
    _ = _ := mul_div_mul_left _ _ hk

/-- The true profile cone implies both primary cones, without assuming
an eigenvector or target-cone inequality. -/
theorem spectral_cones_of_trueCone {F τ p₁ p₂ a c : ℝ} (hF : 0 < F) (hτ : 0 < τ)
    (h : TrueConeLoop.InTrueCone p₁ p₂ a c) :
    PrimaryRepresentatives.ReferenceCone F (F • !₂[-a, -c]) ∧
      PrimaryRepresentatives.TargetCone F (F • !₂[-a, -c]) (τ • !₂[p₁ - a, p₂ - c]) := by
  have hr := referenceCone_of_trueCone hF h
  have hq := (ConeAlgebra.true_cone_iff h.2.1).mp h.2.2
  have hn := norm_pos_iff.mpr hr.shear_ne_zero
  have hk : 0 < τ * F * a / ‖F • !₂[-a, -c]‖ :=
    div_pos (mul_pos (mul_pos hτ hF) h.1) hn
  have hd : 0 < p₁ + p₂ * (c / a) - a * (1 + (c / a) ^ 2) := sub_pos.mpr hq.1
  have hc := c0_sq_signedShear hF h.1 h.2.1
  have hsq : (PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (p₂ - p₁ * (c / a))) ^ 2 <
      (p₁ + p₂ * (c / a) - a * (1 + (c / a) ^ 2)) ^ 2 := by
    rw [mul_pow, hc]
    nlinarith [hq.2]
  have habs : |PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (p₂ - p₁ * (c / a))| <
      p₁ + p₂ * (c / a) - a * (1 + (c / a) ^ 2) := by
    nlinarith [sq_abs (PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (p₂ - p₁ * (c / a))),
      abs_nonneg (PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (p₂ - p₁ * (c / a)))]
  refine ⟨hr, ⟨?_, ?_⟩⟩
  · rw [stress_inner_normal F τ p₁ p₂ a c h.1.ne']
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hk) hd
  · rw [PrimaryRepresentatives.targetRatio, stress_inner_normal F τ p₁ p₂ a c h.1.ne',
      stress_inner_transverse F τ p₁ p₂ a c h.1.ne']
    rw [cancel_signed_scale _ _ _ _ hk.ne', abs_neg, abs_div, abs_of_pos hd]
    exact (div_lt_one hd).mpr habs


/-- A scalar criterion for any direction, including a nonzero smooth
edge factor when the actual stress itself vanishes. -/
theorem targetCone_of_signedShear {F a c : ℝ} (hF : 0 < F) (ha : 0 < a)
    (hv : 2 < a * (1 + (c / a) ^ 2)) (T : Plane)
    (hin : 0 < a * T 0 + c * T 1)
    (hquad : (a * (1 + (c / a) ^ 2) - 2) * (a * T 1 - c * T 0) ^ 2 <
      2 * (a * T 0 + c * T 1) ^ 2) :
    PrimaryRepresentatives.TargetCone F (F • !₂[-a, -c]) T := by
  have ho : 2 * a < a ^ 2 + (-c) ^ 2 := by
    have he := shear_size_mul (c := c) ha.ne'
    have hm := mul_lt_mul_of_pos_left hv ha
    nlinarith
  have hr := PrimaryRepresentatives.referenceCone_of_shear_coordinates hF ha ho
  have hk : 0 < F / ‖F • !₂[-a, -c]‖ :=
    div_pos hF (norm_pos_iff.mpr hr.shear_ne_zero)
  have hN : ⟪T, PrimaryRepresentatives.normalDirection (F • !₂[-a, -c])⟫_ℝ =
      -(F / ‖F • !₂[-a, -c]‖) * (a * T 0 + c * T 1) := by
    simp [PrimaryRepresentatives.normalDirection, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hK : ⟪T, PrimaryRepresentatives.transverseDirection (F • !₂[-a, -c])⟫_ℝ =
      (F / ‖F • !₂[-a, -c]‖) * (a * T 1 - c * T 0) := by
    simp [PrimaryRepresentatives.transverseDirection, PrimaryRepresentatives.normalDirection,
      MovingFrameODE.quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hsq : (PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (a * T 1 - c * T 0)) ^ 2 <
      (a * T 0 + c * T 1) ^ 2 := by
    rw [mul_pow, c0_sq_signedShear hF ha hv]
    nlinarith only [hquad]
  have habs : |PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (a * T 1 - c * T 0)| <
      a * T 0 + c * T 1 := by
    nlinarith [sq_abs (PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (a * T 1 - c * T 0)),
      abs_nonneg (PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (a * T 1 - c * T 0))]
  constructor
  · rw [hN]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hk) hin
  · rw [PrimaryRepresentatives.targetRatio, hN, hK,
      cancel_signed_scale _ _ _ _ hk.ne', abs_neg, abs_div, abs_of_pos hin]
    exact (div_lt_one hin).mpr habs

/-- The edge-collar convention uses the target tilt `T₁ / T₀` and the
signed shear tilt `c / a`. Its two strict scalar margins imply the
primary target cone. -/
theorem targetCone_of_tilt {F a c : ℝ} (hF : 0 < F) (ha : 0 < a)
    (hv : 2 < a * (1 + (c / a) ^ 2)) (T : Plane) (hT : 0 < T 0)
    (hin : 0 < 1 + (c / a) * (T 1 / T 0))
    (hgap : 0 < 2 * (1 + (c / a) * (T 1 / T 0)) ^ 2 -
      (a * (1 + (c / a) ^ 2) - 2) * (T 1 / T 0 - c / a) ^ 2) :
    PrimaryRepresentatives.TargetCone F (F • !₂[-a, -c]) T := by
  have hi : a * T 0 + c * T 1 = a * T 0 * (1 + (c / a) * (T 1 / T 0)) := by
    field_simp [ha.ne', hT.ne']
  have ht : a * T 1 - c * T 0 = a * T 0 * (T 1 / T 0 - c / a) := by
    field_simp [ha.ne', hT.ne']
  apply targetCone_of_signedShear hF ha hv T
  · rw [hi]
    exact mul_pos (mul_pos ha hT) hin
  · rw [hi, ht]
    have hm := mul_pos (sq_pos_of_pos (mul_pos ha hT)) hgap
    nlinarith only [hm]

/-! ## The actual profile histories and stresses -/

open ProfileHistories

/-- The two actual leading stress coefficients, in the Euclidean plane
used by the primary ODE. -/
noncomputable def stressVector {D : RadialDomain} (P : Profiles D) (h : ℝ)
    (p : Point) : Plane := !₂[LeadingStress.theta P h p, LeadingStress.axial P h p]

/-- Both entries use the actual integral-history stocks; the axial sign
agrees with the modulation convention. -/
theorem stressVector_eq_stocks {D : RadialDomain} (P : Profiles D) (h : ℝ) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : P.f p ≠ 0) :
    stressVector P h p = P.f p •
      !₂[ActivationStocks.profileStockOne P h p - ModulatedCone.angularShear P.E p,
        ActivationStocks.profileStockTwo P h p - ModulatedCone.signedAxialShear P.E P.U p] := by
  have hs := NominalConeAssembly.modulated_shears_eq P hp hX hf
  ext i
  fin_cases i
  · change LeadingStress.theta P h p = P.f p * _
    rw [LeadingStress.theta_eq_lag_minus_slope P h hf, hs.1]
    rfl
  · change LeadingStress.axial P h p = P.f p * _
    rw [LeadingStress.axial_eq_lag_plus_slope P h hX hf, hs.2]
    unfold ActivationStocks.profileStockTwo LeadingStress.slopeB ActivationContinuation.shearB
    change P.f p * (p.1 * P.axialLag h p / (CoordinateAlgebra.L h p.2 * P.E p) +
      2 * p.1 * radialPartial P.U p / P.E p) =
      P.f p * (p.1 * P.axialLag h p / (CoordinateAlgebra.L h p.2 * P.E p) -
        -2 * p.1 * radialPartial P.U p / P.E p)
    ring

/-- The actual leading stress belongs to the primary target cone whenever
the actual five-history profile has the true cone. -/
theorem profile_spectral_cones {D : RadialDomain} (P : Profiles D) (h : ℝ) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : 0 < P.f p) {F : ℝ} (hF : 0 < F)
    (hc : TrueConeLoop.InTrueCone (ActivationStocks.profileStockOne P h p)
      (ActivationStocks.profileStockTwo P h p) (ModulatedCone.angularShear P.E p)
      (ModulatedCone.signedAxialShear P.E P.U p)) :
    PrimaryRepresentatives.ReferenceCone F
        (F • !₂[-ModulatedCone.angularShear P.E p, -ModulatedCone.signedAxialShear P.E P.U p]) ∧
      PrimaryRepresentatives.TargetCone F
        (F • !₂[-ModulatedCone.angularShear P.E p, -ModulatedCone.signedAxialShear P.E P.U p])
        (stressVector P h p) := by
  rw [stressVector_eq_stocks P h hp hX hf.ne']
  exact spectral_cones_of_trueCone hF hf hc


/-! ## Genuine radial derivatives of the normalized leading fields -/

theorem normalizedCoordinates_radial (h : ℝ) (p : Slow) (R : ℝ) :
    BaseChartJets.normalizedCoordinates h (R, p.2) =
      ((BaseChartJets.normalizedCoordinates h p).1,
        ((R ^ 2 / 2) / (BaseChartJets.normalizedCoordinates h p).1,
          (BaseChartJets.normalizedCoordinates h p).2.2)) := by
  simp only [BaseChartJets.normalizedCoordinates_eq, SimilarityHomogeneity.chartQ,
    SimilarityHomogeneity.chartX, SimilarityHomogeneity.chartEta,
    SimilarityCoordinates.coordinateX]

private theorem slowR_hasDerivAt {f : Slow → ℝ} {p : Slow}
    (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (fun R => f (R, p.2)) (PhaseCalculus.slowR f p) p.1 :=
  hf.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))

private theorem radial_composition_hasDerivAt {f : Point → ℝ} {rho eta R : ℝ}
    (hf : DifferentiableAt ℝ f ((R ^ 2 / 2) / rho, eta)) :
    HasDerivAt (fun r => f ((r ^ 2 / 2) / rho, eta))
      (R / rho * SimilarityProfile.partialX f ((R ^ 2 / 2) / rho, eta)) R := by
  have hx : HasDerivAt (fun r : ℝ => (r ^ 2 / 2) / rho) (R / rho) R := by
    convert! (((hasDerivAt_id R).pow 2).div_const 2).div_const rho using 1
    simp
  convert! (LeadingStress.partialX_hasDerivAt hf).comp R hx using 1
  ring

theorem leadingFrequency_germ {h C : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    BaseChartJets.leadingFrequency h C d =ᶠ[𝓝 p]
      (fun q => (BaseChartJets.normalizedCoordinates h q).1 ^ (-CoordinateAlgebra.A h - 1 / 2) / C *
        d.phi 0 (BaseChartJets.normalizedCoordinates h q).2) := by
  filter_upwards [continuous_fst.continuousAt.eventually (Ioi_mem_nhds hR),
    continuous_snd.snd.continuousAt.eventually (Ioi_mem_nhds hT)] with q hqR hqT
  exact BaseChartJets.leadingFrequency_eq hh hh1 hqT hqR

theorem leadingFrequency_smoothAt {h C : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    ContDiffAt ℝ ∞ (BaseChartJets.leadingFrequency h C d) p := by
  have hs := BaseChartJets.normalizedCoordinates_smoothAt hh hh1 hT
  have hn := BaseChartJets.normalizedCoordinates_q_pos hh hh1 hT
  exact (((hs.fst.rpow_const_of_ne hn.ne').div_const C).mul
    ((hd.phi 0).contDiffAt.comp p hs.snd)).congr_of_eventuallyEq
      (leadingFrequency_germ hh hh1 hT hR)

theorem leadingAxial_smoothAt {h : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) :
    ContDiffAt ℝ ∞ (BaseChartJets.leadingAxial h d) p := by
  have hs := BaseChartJets.normalizedCoordinates_smoothAt hh hh1 hT
  have hn := BaseChartJets.normalizedCoordinates_q_pos hh hh1 hT
  exact (hs.fst.rpow_const_of_ne hn.ne').mul ((hd.axial 0).contDiffAt.comp p hs.snd)

/-- This is the Fréchet radial derivative of the actual leading angular
frequency, with all chart scale factors retained. -/
theorem leadingFrequency_slowR {h C : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    PhaseCalculus.slowR (BaseChartJets.leadingFrequency h C d) p =
      (BaseChartJets.normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h - 1 / 2) / C *
        (p.1 / (BaseChartJets.normalizedCoordinates h p).1 *
          SimilarityProfile.partialX (d.phi 0) (BaseChartJets.normalizedCoordinates h p).2) := by
  have hp := congrArg Prod.snd (normalizedCoordinates_radial h p p.1)
  change (BaseChartJets.normalizedCoordinates h p).2 =
    ((p.1 ^ 2 / 2) / (BaseChartJets.normalizedCoordinates h p).1,
      (BaseChartJets.normalizedCoordinates h p).2.2) at hp
  have hf := (hd.phi 0).differentiable (by simp) (BaseChartJets.normalizedCoordinates h p).2
  rw [hp] at hf
  have hr := (radial_composition_hasDerivAt hf).const_mul
    ((BaseChartJets.normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h - 1 / 2) / C)
  have he : (fun R => BaseChartJets.leadingFrequency h C d (R, p.2)) =ᶠ[𝓝 p.1]
      (fun R => (BaseChartJets.normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h - 1 / 2) / C *
        d.phi 0 ((R ^ 2 / 2) / (BaseChartJets.normalizedCoordinates h p).1,
          (BaseChartJets.normalizedCoordinates h p).2.2)) := by
    filter_upwards [Ioi_mem_nhds hR] with R hRp
    rw [BaseChartJets.leadingFrequency_eq (p := (R, p.2)) hh hh1 hT hRp,
      normalizedCoordinates_radial]
  rw [← hp] at hr
  exact (slowR_hasDerivAt ((leadingFrequency_smoothAt hh hh1 hd hT hR).differentiableAt
    (by simp))).unique (hr.congr_of_eventuallyEq he)

theorem leadingAxial_slowR {h : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) :
    PhaseCalculus.slowR (BaseChartJets.leadingAxial h d) p =
      (BaseChartJets.normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h) *
        (p.1 / (BaseChartJets.normalizedCoordinates h p).1 *
          SimilarityProfile.partialX (d.axial 0) (BaseChartJets.normalizedCoordinates h p).2) := by
  have hp := congrArg Prod.snd (normalizedCoordinates_radial h p p.1)
  change (BaseChartJets.normalizedCoordinates h p).2 =
    ((p.1 ^ 2 / 2) / (BaseChartJets.normalizedCoordinates h p).1,
      (BaseChartJets.normalizedCoordinates h p).2.2) at hp
  have hf := (hd.axial 0).differentiable (by simp) (BaseChartJets.normalizedCoordinates h p).2
  rw [hp] at hf
  have hr := (radial_composition_hasDerivAt hf).const_mul
    ((BaseChartJets.normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h))
  have he : (fun R => BaseChartJets.leadingAxial h d (R, p.2)) =
      (fun R => (BaseChartJets.normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h) *
        d.axial 0 ((R ^ 2 / 2) / (BaseChartJets.normalizedCoordinates h p).1,
          (BaseChartJets.normalizedCoordinates h p).2.2)) := by
    funext R
    simp only [BaseChartJets.leadingAxial, BaseChartJets.axialFactor, normalizedCoordinates_radial]
  rw [← hp] at hr
  rw [← he] at hr
  exact (slowR_hasDerivAt ((leadingAxial_smoothAt hh hh1 hd hT).differentiableAt
    (by simp))).unique hr

theorem normalized_X_eq (h : ℝ) (p : Slow) :
    (BaseChartJets.normalizedCoordinates h p).2.1 =
      p.1 ^ 2 / (2 * (BaseChartJets.normalizedCoordinates h p).1) := by
  rw [BaseChartJets.normalizedCoordinates_eq]
  unfold SimilarityHomogeneity.chartX SimilarityCoordinates.coordinateX
    SimilarityHomogeneity.chartQ
  ring

theorem normalized_X_pos {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    0 < (BaseChartJets.normalizedCoordinates h p).2.1 := by
  rw [normalized_X_eq]
  exact div_pos (sq_pos_of_pos hR)
    (mul_pos (by norm_num) (BaseChartJets.normalizedCoordinates_q_pos hh hh1 hT))

/-- Value and radial-germ agreement with a profile suffice to identify the
genuine shear vector of the coefficient-defined leading fields. -/
theorem leading_shear_eq_profile {D : RadialDomain} (P : Profiles D)
    {h C : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hC : C ≠ 0) (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1)
    (hp : (BaseChartJets.normalizedCoordinates h p).2 ∈ D.carrier)
    (hf : P.f (BaseChartJets.normalizedCoordinates h p).2 ≠ 0)
    (hphi : (fun X => d.phi 0 (X, (BaseChartJets.normalizedCoordinates h p).2.2)) =ᶠ[
      𝓝 (BaseChartJets.normalizedCoordinates h p).2.1]
      (fun X => C * P.f (X, (BaseChartJets.normalizedCoordinates h p).2.2)))
    (hU : (fun X => d.axial 0 (X, (BaseChartJets.normalizedCoordinates h p).2.2)) =ᶠ[
      𝓝 (BaseChartJets.normalizedCoordinates h p).2.1]
      (fun X => P.U (X, (BaseChartJets.normalizedCoordinates h p).2.2))) :
    PhaseEstimates.shearVector (BaseChartJets.leadingFrequency h C d) (BaseChartJets.leadingAxial h d) p =
      BaseChartJets.leadingFrequency h C d p •
        !₂[-ModulatedCone.angularShear P.E (BaseChartJets.normalizedCoordinates h p).2,
          -ModulatedCone.signedAxialShear P.E P.U (BaseChartJets.normalizedCoordinates h p).2] := by
  let w := (BaseChartJets.normalizedCoordinates h p).2
  let rho := (BaseChartJets.normalizedCoordinates h p).1
  have hrho : 0 < rho := BaseChartJets.normalizedCoordinates_q_pos hh hh1 hT
  have hX : 0 < w.1 := normalized_X_pos hh hh1 hT hR
  have hphi0 : d.phi 0 w = C * P.f w := hphi.eq_of_nhds
  have hfx := LeadingStress.partialX_hasDerivAt
    ((P.f_smooth.contDiffAt (D.isOpen.mem_nhds hp)).differentiableAt (by simp))
  have hux := LeadingStress.partialX_hasDerivAt
    ((P.U_smooth.contDiffAt (D.isOpen.mem_nhds hp)).differentiableAt (by simp))
  have hphiX : SimilarityProfile.partialX (d.phi 0) w = C * SimilarityProfile.partialX P.f w :=
    (LeadingStress.partialX_hasDerivAt ((hd.phi 0).differentiable (by simp) w)).unique
      ((hfx.const_mul C).congr_of_eventuallyEq hphi)
  have hUX : SimilarityProfile.partialX (d.axial 0) w = SimilarityProfile.partialX P.U w :=
    (LeadingStress.partialX_hasDerivAt ((hd.axial 0).differentiable (by simp) w)).unique
      (hux.congr_of_eventuallyEq hU)
  have hF : BaseChartJets.leadingFrequency h C d p =
      rho ^ (-CoordinateAlgebra.A h - 1 / 2) * P.f w := by
    rw [BaseChartJets.leadingFrequency_eq hh hh1 hT hR, hphi0]
    dsimp only [rho]
    field_simp
  have hFX : PhaseCalculus.slowR (BaseChartJets.leadingFrequency h C d) p =
      rho ^ (-CoordinateAlgebra.A h - 1 / 2) * (p.1 / rho * SimilarityProfile.partialX P.f w) := by
    rw [leadingFrequency_slowR hh hh1 hd hT hR, hphiX]
    dsimp only [rho]
    field_simp
  have hGX : PhaseCalculus.slowR (BaseChartJets.leadingAxial h d) p =
      rho ^ (-CoordinateAlgebra.A h) * (p.1 / rho * SimilarityProfile.partialX P.U w) := by
    rw [leadingAxial_slowR hh hh1 hd hT, hUX]
  have hw : w.1 = p.1 ^ 2 / (2 * rho) := normalized_X_eq h p
  have hsqrt : Real.sqrt (2 * w.1) = p.1 / Real.sqrt rho := by
    have he : 2 * w.1 = p.1 ^ 2 / rho := by rw [hw]; ring
    rw [he, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hR.le]
  have hpow : rho ^ (-CoordinateAlgebra.A h - 1 / 2) =
      rho ^ (-CoordinateAlgebra.A h) / Real.sqrt rho := by
    rw [Real.rpow_sub hrho, Real.sqrt_eq_rpow]
  have hs := NominalConeAssembly.modulated_shears_eq P hp hX hf
  rw [hs.1, hs.2]
  ext i
  fin_cases i
  · change p.1 * PhaseCalculus.slowR (BaseChartJets.leadingFrequency h C d) p =
      BaseChartJets.leadingFrequency h C d p * (-ActivationContinuation.shearA P w)
    rw [hFX, hF]
    unfold ActivationContinuation.shearA
    change p.1 * (rho ^ (-CoordinateAlgebra.A h - 1 / 2) * (p.1 / rho * radialPartial P.f w)) =
      rho ^ (-CoordinateAlgebra.A h - 1 / 2) * P.f w * (-(-2 * w.1 * radialPartial P.f w / P.f w))
    rw [hw]
    field_simp [show P.f w ≠ 0 from hf, hrho.ne']
  · change PhaseCalculus.slowR (BaseChartJets.leadingAxial h d) p =
      BaseChartJets.leadingFrequency h C d p * (-ActivationContinuation.shearB P w)
    rw [hGX, hF]
    unfold ActivationContinuation.shearB Profiles.E
    change rho ^ (-CoordinateAlgebra.A h) * (p.1 / rho * radialPartial P.U w) =
      rho ^ (-CoordinateAlgebra.A h - 1 / 2) * P.f w *
        (-(-2 * w.1 * radialPartial P.U w / (Real.sqrt (2 * w.1) * P.f w)))
    rw [hpow, hsqrt, hw]
    field_simp [show P.f w ≠ 0 from hf, hrho.ne', hR.ne', (Real.sqrt_pos.mpr hrho).ne']

/-! ## Uniform choices on a compact reference set -/

theorem signedShear_continuousOn {K : Set Slow} {F a c : Slow → ℝ}
    (hF : ContinuousOn F K) (ha : ContinuousOn a K) (hc : ContinuousOn c K) :
    ContinuousOn (fun p => F p • !₂[-a p, -c p]) K := by
  apply hF.smul
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  change ContinuousOn (fun p => (![-a p, -c p] : Fin 2 → ℝ)) K
  apply continuousOn_pi.mpr
  intro i
  fin_cases i
  · exact ha.neg
  · exact hc.neg



end NavierStokes.ProfileSpectralCone


noncomputable section

namespace NavierStokes.AlignedProfileSpectralCone

open Set Function Filter ProfileHistories ProfileSpectralCone
open scoped ContDiff Topology InnerProductSpace

/-! ## The same finite modulated profile and aligned slow coefficients -/

section Modulated

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {d : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness d)

theorem modulated_fields_radial_germ {p : Point} (hX : 0 < p.1) (heta : |p.2| ≤ 1) :
    ((fun X => (EntranceAlignedBase.modulatedCoefficients H v).phi 0 (X, p.2)) =ᶠ[𝓝 p.1]
      (fun X => W.axis.normalization * v.profiles.f (X, p.2))) ∧
    ((fun X => (EntranceAlignedBase.modulatedCoefficients H v).axial 0 (X, p.2)) =ᶠ[𝓝 p.1]
      (fun X => v.profiles.U (X, p.2))) := by
  constructor
  · filter_upwards [Ioi_mem_nhds hX] with X hXp
    exact (EntranceAlignedBase.modulated_zero_fields H v (p := (X, p.2)) hXp.le heta).1
  · filter_upwards [Ioi_mem_nhds hX] with X hXp
    exact (EntranceAlignedBase.modulated_zero_fields H v (p := (X, p.2)) hXp.le heta).2.1

theorem modulated_frequency_eq {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    BaseChartJets.leadingFrequency F.data.h W.axis.normalization
        (EntranceAlignedBase.modulatedCoefficients H v) p =
      (BaseChartJets.normalizedCoordinates F.data.h p).1 ^ (-CoordinateAlgebra.A F.data.h - 1 / 2) *
        v.profiles.f (BaseChartJets.normalizedCoordinates F.data.h p).2 := by
  have hh := ConstructedSlowBase.height_pos W
  have hh1 := ConstructedSlowBase.height_lt_half W
  have hX := normalized_X_pos hh hh1 hT hR
  have heta := BaseChartJets.normalizedCoordinates_eta hh hh1 hT
  rw [BaseChartJets.leadingFrequency_eq hh hh1 hT hR,
    (EntranceAlignedBase.modulated_zero_fields H v hX.le heta.le).1]
  field_simp [W.axis.normalization_pos.ne']


theorem modulated_shear_eq {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    PhaseEstimates.shearVector
        (BaseChartJets.leadingFrequency F.data.h W.axis.normalization
          (EntranceAlignedBase.modulatedCoefficients H v))
        (BaseChartJets.leadingAxial F.data.h (EntranceAlignedBase.modulatedCoefficients H v)) p =
      BaseChartJets.leadingFrequency F.data.h W.axis.normalization
        (EntranceAlignedBase.modulatedCoefficients H v) p •
          !₂[-ModulatedCone.angularShear v.profiles.E (BaseChartJets.normalizedCoordinates F.data.h p).2,
            -ModulatedCone.signedAxialShear v.profiles.E v.profiles.U
              (BaseChartJets.normalizedCoordinates F.data.h p).2] := by
  have hh := ConstructedSlowBase.height_pos W
  have hh1 := ConstructedSlowBase.height_lt_half W
  have hX := normalized_X_pos hh hh1 hT hR
  have heta := (BaseChartJets.normalizedCoordinates_eta hh hh1 hT).le
  have hg := modulated_fields_radial_germ H v hX heta
  exact leading_shear_eq_profile v.profiles hh hh1 W.axis.normalization_pos.ne'
    (EntranceAlignedBase.modulated_smooth H v) hT hR
    (d.domain_nonnegative hX.le (d.parameters_contains (abs_le.mp heta)))
    (v.positive_f hX (abs_le.mp heta)).ne' hg.1 hg.2





end Modulated

/-! ## A single Euclidean direction through both zero-amplitude edges -/

noncomputable def planeOfPair : (ℝ × ℝ) →L[ℝ] Plane :=
  LinearMap.toContinuousLinearMap {
    toFun := fun p => !₂[p.1, p.2]
    map_add' := by intro p q; ext i; fin_cases i <;> simp
    map_smul' := by intro c p; ext i; fin_cases i <;> simp }

theorem planeOfPair_injective : Injective planeOfPair := by
  intro p q h
  apply Prod.ext
  · exact congrArg (fun z : Plane => z 0) h
  · exact congrArg (fun z : Plane => z 1) h

noncomputable def planeEdgeFactor {J : Set ℝ} {c : ℝ} {S : (ℝ × ℝ) → ℝ × ℝ}
    (F : ActiveAnnulusWeight.EdgeFactor J c S) :
    ActiveAnnulusWeight.EdgeFactor J c (fun p => planeOfPair (S p)) where
  coefficient := fun p => planeOfPair (F.coefficient p)
  order := F.order
  width := F.width
  width_pos := F.width_pos
  domain := F.domain
  domain_open := F.domain_open
  boundary_mem := F.boundary_mem
  smooth := planeOfPair.contDiff.comp_contDiffOn F.smooth
  boundary_ne_zero := by
    intro eta heta hz
    apply F.boundary_ne_zero eta heta
    apply planeOfPair_injective
    simpa only [map_zero] using hz
  identity := by
    intro eta heta x hx hxw
    rw [F.identity eta heta x hx hxw, map_smul]

theorem normalDirection_pos_smul (T : Plane) {c : ℝ} (hc : 0 < c) :
    PrimaryRepresentatives.normalDirection (c • T) = PrimaryRepresentatives.normalDirection T := by
  simp only [PrimaryRepresentatives.normalDirection, norm_smul,
    Real.norm_of_nonneg hc.le, mul_inv_rev, smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

private theorem normalDirection_continuousAt {S : (ℝ × ℝ) → Plane} {p : ℝ × ℝ}
    (hS : ContinuousAt S p) (hne : S p ≠ 0) :
    ContinuousAt (fun q => PrimaryRepresentatives.normalDirection (S q)) p :=
  (hS.norm.inv₀ (norm_ne_zero_iff.mpr hne)).smul hS

/-- In the interior this is the actual stress normalized in the Euclidean
norm. At the two endpoints it uses the corresponding genuine flat factor. -/
noncomputable def gluedDirection (a b : ℝ) (S BL BR : (ℝ × ℝ) → Plane)
    (p : ℝ × ℝ) : Plane :=
  if p.2 ≤ a then PrimaryRepresentatives.normalDirection (BL (p.1, p.2 - a))
  else if b ≤ p.2 then PrimaryRepresentatives.normalDirection (BR (p.1, b - p.2))
  else PrimaryRepresentatives.normalDirection (S p)

theorem gluedDirection_interior {a b : ℝ} (S BL BR : (ℝ × ℝ) → Plane) {p : ℝ × ℝ}
    (hp : p.2 ∈ Ioo a b) : gluedDirection a b S BL BR p = PrimaryRepresentatives.normalDirection (S p) := by
  simp [gluedDirection, not_le.mpr hp.1, not_le.mpr hp.2]

private theorem gluedDirection_left_germ {J : Set ℝ} {a b cL cR : ℝ}
    {S : (ℝ × ℝ) → Plane} (hab : a < b)
    (FL : ActiveAnnulusWeight.EdgeFactor J cL (ActiveAnnulusWeight.leftChart a S))
    (FR : ActiveAnnulusWeight.EdgeFactor J cR (ActiveAnnulusWeight.rightChart b S))
    {eta : ℝ} (_heta : eta ∈ J) :
    gluedDirection a b S FL.coefficient FR.coefficient =ᶠ[𝓝[J ×ˢ Icc a b] (eta, a)]
      (fun q => PrimaryRepresentatives.normalDirection (FL.coefficient (q.1, q.2 - a))) := by
  have hw : ∀ᶠ q : ℝ × ℝ in 𝓝 (eta, a), q.2 < a + FL.width :=
    continuous_snd.continuousAt.eventually (Iio_mem_nhds (by linarith [FL.width_pos]))
  have hb : ∀ᶠ q : ℝ × ℝ in 𝓝 (eta, a), q.2 < b :=
    continuous_snd.continuousAt.eventually (Iio_mem_nhds hab)
  filter_upwards [self_mem_nhdsWithin, hw.filter_mono nhdsWithin_le_nhds,
    hb.filter_mono nhdsWithin_le_nhds] with q hq hqw hqb
  by_cases hqa : q.2 ≤ a
  · simp only [gluedDirection, ite_eq_left hqa]
  · simp only [gluedDirection, ite_eq_right hqa, ite_eq_right (not_le.mpr hqb)]
    have hx : 0 < q.2 - a := sub_pos.mpr (lt_of_not_ge hqa)
    have he := FL.identity q.1 hq.1 (q.2 - a) hx (by linarith)
    simp only [ActiveAnnulusWeight.leftChart] at he
    rw [show a + (q.2 - a) = q.2 by ring] at he
    change S q = _ at he
    rw [he, normalDirection_pos_smul _ (div_pos (FlatCutoff.edge_pos _ hx) (pow_pos hx _))]

private theorem gluedDirection_right_germ {J : Set ℝ} {a b cL cR : ℝ}
    {S : (ℝ × ℝ) → Plane} (hab : a < b)
    (FL : ActiveAnnulusWeight.EdgeFactor J cL (ActiveAnnulusWeight.leftChart a S))
    (FR : ActiveAnnulusWeight.EdgeFactor J cR (ActiveAnnulusWeight.rightChart b S))
    {eta : ℝ} (_heta : eta ∈ J) :
    gluedDirection a b S FL.coefficient FR.coefficient =ᶠ[𝓝[J ×ˢ Icc a b] (eta, b)]
      (fun q => PrimaryRepresentatives.normalDirection (FR.coefficient (q.1, b - q.2))) := by
  have hw : ∀ᶠ q : ℝ × ℝ in 𝓝 (eta, b), b - FR.width < q.2 :=
    continuous_snd.continuousAt.eventually (Ioi_mem_nhds (by linarith [FR.width_pos]))
  have ha : ∀ᶠ q : ℝ × ℝ in 𝓝 (eta, b), a < q.2 :=
    continuous_snd.continuousAt.eventually (Ioi_mem_nhds hab)
  filter_upwards [self_mem_nhdsWithin, hw.filter_mono nhdsWithin_le_nhds,
    ha.filter_mono nhdsWithin_le_nhds] with q hq hqw hqa
  simp only [gluedDirection, ite_eq_right (not_le.mpr hqa)]
  by_cases hqb : b ≤ q.2
  · simp only [ite_eq_left hqb]
  · simp only [ite_eq_right hqb]
    have hx : 0 < b - q.2 := sub_pos.mpr (lt_of_not_ge hqb)
    have he := FR.identity q.1 hq.1 (b - q.2) hx (by linarith)
    simp only [ActiveAnnulusWeight.rightChart] at he
    rw [show b - (b - q.2) = q.2 by ring] at he
    change S q = _ at he
    rw [he, normalDirection_pos_smul _ (div_pos (FlatCutoff.edge_pos _ hx) (pow_pos hx _))]

theorem gluedDirection_continuousOn {J : Set ℝ} {a b cL cR : ℝ}
    {S : (ℝ × ℝ) → Plane} (hab : a < b)
    (FL : ActiveAnnulusWeight.EdgeFactor J cL (ActiveAnnulusWeight.leftChart a S))
    (FR : ActiveAnnulusWeight.EdgeFactor J cR (ActiveAnnulusWeight.rightChart b S))
    (hS : ∀ p ∈ J ×ˢ Ioo a b, ContinuousAt S p)
    (hne : ∀ p ∈ J ×ˢ Ioo a b, S p ≠ 0) :
    ContinuousOn (gluedDirection a b S FL.coefficient FR.coefficient) (J ×ˢ Icc a b) := by
  rintro ⟨eta, y⟩ ⟨heta, hy⟩
  by_cases hl : y = a
  · subst y
    have hB : ContinuousAt FL.coefficient (eta, 0) := FL.smooth.continuousOn.continuousAt
      (FL.domain_open.mem_nhds (FL.boundary_mem ⟨heta, rfl⟩))
    have hn := normalDirection_continuousAt hB (FL.boundary_ne_zero eta heta)
    have hm : ContinuousAt (fun q : ℝ × ℝ => (q.1, q.2 - a)) (eta, a) :=
      continuous_fst.continuousAt.prodMk (continuous_snd.continuousAt.sub continuousAt_const)
    have hc := hn.comp_of_eq hm (by simp)
    exact hc.continuousWithinAt.congr_of_eventuallyEq_of_mem
      (gluedDirection_left_germ hab FL FR heta) ⟨heta, hy⟩
  by_cases hr : y = b
  · subst y
    have hB : ContinuousAt FR.coefficient (eta, 0) := FR.smooth.continuousOn.continuousAt
      (FR.domain_open.mem_nhds (FR.boundary_mem ⟨heta, rfl⟩))
    have hn := normalDirection_continuousAt hB (FR.boundary_ne_zero eta heta)
    have hm : ContinuousAt (fun q : ℝ × ℝ => (q.1, b - q.2)) (eta, b) :=
      continuous_fst.continuousAt.prodMk (continuousAt_const.sub continuous_snd.continuousAt)
    have hc := hn.comp_of_eq hm (by simp)
    exact hc.continuousWithinAt.congr_of_eventuallyEq_of_mem
      (gluedDirection_right_germ hab FL FR heta) ⟨heta, hy⟩
  have hmid : y ∈ Ioo a b := ⟨lt_of_le_of_ne hy.1 (Ne.symm hl), lt_of_le_of_ne hy.2 hr⟩
  have hn := normalDirection_continuousAt (hS (eta, y) ⟨heta, hmid⟩) (hne (eta, y) ⟨heta, hmid⟩)
  apply (hn.continuousWithinAt (s := J ×ˢ Icc a b)).congr_of_eventuallyEq_of_mem _ ⟨heta, hy⟩
  have hm : ∀ᶠ q : ℝ × ℝ in 𝓝 (eta, y), q.2 ∈ Ioo a b :=
    continuous_snd.continuousAt.eventually (isOpen_Ioo.mem_nhds hmid)
  filter_upwards [hm.filter_mono nhdsWithin_le_nhds] with q hq
  exact gluedDirection_interior S FL.coefficient FR.coefficient hq

theorem gluedDirection_norm {J : Set ℝ} {a b cL cR : ℝ}
    {S : (ℝ × ℝ) → Plane} (_hab : a < b)
    (FL : ActiveAnnulusWeight.EdgeFactor J cL (ActiveAnnulusWeight.leftChart a S))
    (FR : ActiveAnnulusWeight.EdgeFactor J cR (ActiveAnnulusWeight.rightChart b S))
    (hne : ∀ p ∈ J ×ˢ Ioo a b, S p ≠ 0) {p : ℝ × ℝ} (hp : p ∈ J ×ˢ Icc a b) :
    ‖gluedDirection a b S FL.coefficient FR.coefficient p‖ = 1 := by
  by_cases hl : p.2 ≤ a
  · have he : p.2 = a := le_antisymm hl hp.2.1
    rw [gluedDirection, ite_eq_left hl, he, sub_self]
    exact PrimaryRepresentatives.normalDirection_unit (FL.boundary_ne_zero p.1 hp.1)
  by_cases hr : b ≤ p.2
  · have he : p.2 = b := le_antisymm hp.2.2 hr
    rw [gluedDirection, ite_eq_right hl, ite_eq_left hr, he, sub_self]
    exact PrimaryRepresentatives.normalDirection_unit (FR.boundary_ne_zero p.1 hp.1)
  rw [gluedDirection_interior S FL.coefficient FR.coefficient ⟨lt_of_not_ge hl, lt_of_not_ge hr⟩]
  exact PrimaryRepresentatives.normalDirection_unit (hne p ⟨hp.1, lt_of_not_ge hl, lt_of_not_ge hr⟩)


private theorem referenceCone_of_speed {F a c : ℝ} (hF : 0 < F) (ha : 0 < a)
    (hv : 2 < a * (1 + (c / a) ^ 2)) :
    PrimaryRepresentatives.ReferenceCone F (F • !₂[-a, -c]) := by
  apply PrimaryRepresentatives.referenceCone_of_shear_coordinates hF ha
  have he : a * (a * (1 + (c / a) ^ 2)) = a ^ 2 + c ^ 2 := by
    field_simp
  have hm := mul_lt_mul_of_pos_left hv ha
  nlinarith

private theorem normalized_target_of_tilt {F a c : ℝ} (hF : 0 < F) (ha : 0 < a)
    (hv : 2 < a * (1 + (c / a) ^ 2)) (B : ℝ × ℝ) (hB : 0 < B.1)
    (hin : 0 < 1 + (c / a) * (B.2 / B.1))
    (hgap : 0 < 2 * (1 + (c / a) * (B.2 / B.1)) ^ 2 -
      (a * (1 + (c / a) ^ 2) - 2) * (B.2 / B.1 - c / a) ^ 2) :
    PrimaryRepresentatives.TargetCone F (F • !₂[-a, -c])
      (PrimaryRepresentatives.normalDirection (planeOfPair B)) := by
  have hne : planeOfPair B ≠ 0 := by
    intro hz
    have hb := congrArg (fun z : Plane => z 0) hz
    change B.1 = 0 at hb
    exact hB.ne' hb
  exact (targetCone_of_tilt hF ha hv (planeOfPair B) hB hin hgap).pos_smul
    (inv_pos.mpr (norm_pos_iff.mpr hne))

section ClosedDirection

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {d : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness d)

noncomputable def logShear (omega : ℝ) (p : ℝ × ℝ) : Plane :=
  omega • !₂[-LeadingStressWeights.logShearA v.profiles p,
    -LeadingStressWeights.logShearB v.profiles p]

/-- A single actual unit direction, continuous through both flat edges,
with the strict spectral target cone on the entire closed annulus. -/
theorem exists_closed_direction (hcone : LeadingStressWeights.FullTrueCone v) :
    ∃ D : (ℝ × ℝ) → Plane,
      ContinuousOn D (Icc (-1 : ℝ) 1 ×ˢ Icc (LeadingStressWeights.leftEdge W) (LeadingStressWeights.rightEdge W)) ∧
      (∀ p ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (LeadingStressWeights.leftEdge W) (LeadingStressWeights.rightEdge W), ‖D p‖ = 1) ∧
      (∀ p ∈ Icc (-1 : ℝ) 1 ×ˢ Ioo (LeadingStressWeights.leftEdge W) (LeadingStressWeights.rightEdge W),
        D p = PrimaryRepresentatives.normalDirection
          (planeOfPair (LeadingStressWeights.logStress v.profiles F.data.h p))) ∧
      ∀ p ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (LeadingStressWeights.leftEdge W) (LeadingStressWeights.rightEdge W),
        ∀ omega : ℝ, 0 < omega → PrimaryRepresentatives.ReferenceCone omega (logShear v omega p) ∧
          PrimaryRepresentatives.TargetCone omega (logShear v omega p) (D p) := by
  obtain ⟨FL, hFL, hDL⟩ := LeadingStressWeights.inner_direction_positive v hcone
  obtain ⟨FR, hFR, hDR⟩ := LeadingStressWeights.outer_direction_positive v
  let S : (ℝ × ℝ) → Plane := fun p => planeOfPair (LeadingStressWeights.logStress v.profiles F.data.h p)
  let L : ActiveAnnulusWeight.EdgeFactor (Icc (-1 : ℝ) 1) (W.controls.activationTime ^ 2)
      (ActiveAnnulusWeight.leftChart (LeadingStressWeights.leftEdge W) S) := planeEdgeFactor FL
  let R : ActiveAnnulusWeight.EdgeFactor (Icc (-1 : ℝ) 1) 4
      (ActiveAnnulusWeight.rightChart (LeadingStressWeights.rightEdge W) S) := planeEdgeFactor FR
  let D : (ℝ × ℝ) → Plane := gluedDirection (LeadingStressWeights.leftEdge W) (LeadingStressWeights.rightEdge W)
    S L.coefficient R.coefficient
  have hab := LeadingStressWeights.edges_ordered W
  have hS (p : ℝ × ℝ) (hp : p ∈ Icc (-1 : ℝ) 1 ×ˢ
      Ioo (LeadingStressWeights.leftEdge W) (LeadingStressWeights.rightEdge W)) : ContinuousAt S p := by
    have hm := LeadingStressWeights.logStress_mem v (p := p) hp.1
    exact planeOfPair.continuous.continuousAt.comp_of_eq
      ((LeadingStressWeights.logStress_smooth v.profiles F.data.h).continuousOn.continuousAt
        ((LeadingStressWeights.logStressDomain_open v.profiles F.data.h).mem_nhds hm)) rfl
  have hne (p : ℝ × ℝ) (hp : p ∈ Icc (-1 : ℝ) 1 ×ˢ
      Ioo (LeadingStressWeights.leftEdge W) (LeadingStressWeights.rightEdge W)) : S p ≠ 0 := by
    intro hz
    apply LeadingStressWeights.logStress_ne_zero v hcone hp.1 hp.2
    apply planeOfPair_injective
    simpa only [map_zero] using hz
  refine ⟨D, gluedDirection_continuousOn hab L R hS hne,
    (fun p hp => gluedDirection_norm hab L R hne hp),
    (fun p hp => gluedDirection_interior S L.coefficient R.coefficient hp.2), ?_⟩
  rintro ⟨eta, y⟩ ⟨heta, hy⟩ omega homega
  have hspeed := LeadingStressWeights.closed_shear_positive v hcone heta hy
  have href : PrimaryRepresentatives.ReferenceCone omega (logShear v omega (eta, y)) :=
    referenceCone_of_speed homega hspeed.1 hspeed.2
  refine ⟨href, ?_⟩
  by_cases hl : y = LeadingStressWeights.leftEdge W
  · subst y
    obtain ⟨dl, el, O, hdl, _, hel, _, _, _, hmargin, _⟩ := hDL.1
    have hm := hmargin eta heta 0 ⟨le_rfl, hdl.le⟩
    have hin := hel.trans_le hm.1
    have hgap := hel.trans_le hm.2
    simp only [ActiveAnnulusWeight.leftChart, add_zero,
      ActiveAnnulusWeight.directionProjection, ActiveAnnulusWeight.directionGap,
      ActiveAnnulusWeight.tilt, LeadingStressWeights.logSlope,
      LeadingStressWeights.logSpeed, ActivationContinuation.shearSize] at hin hgap
    have ht := normalized_target_of_tilt homega hspeed.1 hspeed.2
      (FL.coefficient (eta, 0)) (hFL eta heta) hin hgap
    simpa only [D, gluedDirection, ite_eq_left le_rfl, sub_self, L, planeEdgeFactor,
      logShear] using ht
  by_cases hr : y = LeadingStressWeights.rightEdge W
  · subst y
    obtain ⟨dr, er, O, hdr, _, her, _, _, _, hmargin, _⟩ := hDR.1
    have hm := hmargin eta heta 0 ⟨le_rfl, hdr.le⟩
    have hin := her.trans_le hm.1
    have hgap := her.trans_le hm.2
    simp only [ActiveAnnulusWeight.rightChart, sub_zero,
      ActiveAnnulusWeight.directionProjection, ActiveAnnulusWeight.directionGap,
      ActiveAnnulusWeight.tilt, LeadingStressWeights.logSlope,
      LeadingStressWeights.logSpeed, ActivationContinuation.shearSize] at hin hgap
    have ht := normalized_target_of_tilt homega hspeed.1 hspeed.2
      (FR.coefficient (eta, 0)) (hFR eta heta) hin hgap
    simpa only [D, gluedDirection, ite_eq_right (not_le.mpr hab), ite_eq_left le_rfl,
      sub_self, R, planeEdgeFactor, logShear] using ht
  have hmid : y ∈ Ioo (LeadingStressWeights.leftEdge W) (LeadingStressWeights.rightEdge W) :=
    ⟨lt_of_le_of_ne hy.1 (Ne.symm hl), lt_of_le_of_ne hy.2 hr⟩
  have hx : 0 < Real.exp y := Real.exp_pos _
  have hleft : NominalConeAssembly.activeLeft W < Real.exp y :=
    (Real.log_lt_iff_lt_exp (NominalConeAssembly.activeLeft_pos W)).mp hmid.1
  have hright : Real.exp y < NominalConeAssembly.activeRight W :=
    (Real.lt_log_iff_exp_lt (LeadingStressWeights.activeRight_pos W)).mp hmid.2
  have hdom := d.domain_nonnegative (p := (Real.exp y, eta)) hx.le (d.parameters_contains heta)
  have hf := v.positive_f (p := (Real.exp y, eta)) hx heta
  have hs := NominalConeAssembly.modulated_shears_eq v.profiles hdom hx hf.ne'
  have ht := (profile_spectral_cones v.profiles F.data.h hdom hx hf homega
    (hcone (Real.exp y, eta) hleft hright heta)).2
  rw [hs.1, hs.2] at ht
  have he : S (eta, y) = stressVector v.profiles F.data.h (Real.exp y, eta) := rfl
  have ht' := ht.pos_smul (inv_pos.mpr (norm_pos_iff.mpr (hne (eta, y) ⟨heta, hmid⟩)))
  change PrimaryRepresentatives.TargetCone omega _ (D (eta, y))
  rw [show D (eta, y) = PrimaryRepresentatives.normalDirection (S (eta, y)) from
    gluedDirection_interior S L.coefficient R.coefficient hmid]
  simpa only [logShear, LeadingStressWeights.logShearA, LeadingStressWeights.logShearB,
    LeadingStressWeights.logPoint, PrimaryRepresentatives.normalDirection, he] using ht'

end ClosedDirection

noncomputable def referenceSet {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) : Set Slow :=
  PrimaryRepresentatives.referenceCompact F.data.h (NominalConeAssembly.activeLeft W)
    (NominalConeAssembly.activeRight W)

noncomputable def referenceLogPoint {F : OutgoingProfile.Profile} (_W : NominalProfile.Witness F)
    (p : Slow) : ℝ × ℝ :=
  ((PositiveRepresentatives.stableInner F.data.h p).2,
    Real.log (PositiveRepresentatives.stableInner F.data.h p).1)

structure ReferencePointData {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (p : Slow) : Prop where
  stable : p ∈ PositiveRepresentatives.stableDomain F.data.h
  radius : 0 < p.1
  scalar : 0 < PositiveRepresentatives.stableQ F.data.h p
  inner_pos : 0 < (PositiveRepresentatives.stableInner F.data.h p).1
  parameter : (PositiveRepresentatives.stableInner F.data.h p).2 ∈ Icc (-1 : ℝ) 1
  log_mem : referenceLogPoint W p ∈ Icc (-1 : ℝ) 1 ×ˢ
    Icc (LeadingStressWeights.leftEdge W) (LeadingStressWeights.rightEdge W)

private theorem active_order {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    NominalConeAssembly.activeLeft W < NominalConeAssembly.activeRight W := by
  have he := Real.exp_lt_exp.mpr (LeadingStressWeights.edges_ordered W)
  simpa only [LeadingStressWeights.leftEdge, LeadingStressWeights.rightEdge,
    Real.exp_log (NominalConeAssembly.activeLeft_pos W),
    Real.exp_log (LeadingStressWeights.activeRight_pos W)] using he

theorem referenceSet_compact {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    IsCompact (referenceSet W) :=
  PrimaryRepresentatives.referenceCompact_isCompact (ConstructedSlowBase.height_pos W).le
    (ConstructedSlowBase.height_lt_half W) (NominalConeAssembly.activeLeft_pos W) (active_order W).le

theorem reference_point {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {p : Slow} (hp : p ∈ referenceSet W) : ReferencePointData W p := by
  have hh := (ConstructedSlowBase.height_pos W).le
  have hh1 := ConstructedSlowBase.height_lt_half W
  have ha := NominalConeAssembly.activeLeft_pos W
  have hab := (active_order W).le
  have hs := PositiveRepresentatives.referenceCompact_subset_stableDomain hh hh1 ha hab hp
  have hX := (PositiveRepresentatives.stableQ_bounds_reference hh hh1 ha hab hp).2
  have he := PositiveRepresentatives.stableEta_mem_reference hh hh1 ha hab hp
  have hx : 0 < (PositiveRepresentatives.stableInner F.data.h p).1 := ha.trans_le hX.1
  refine ⟨hs, hs.1, (PositiveRepresentatives.stableQ_spec hs).1, hx, he, he, ?_, ?_⟩
  · exact Real.log_le_log ha hX.1
  · exact Real.log_le_log hx hX.2

section ReferenceFunctions

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {d : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness d)

noncomputable def referenceFrequency : Slow → ℝ :=
  PositiveRepresentatives.stablePullback F.data.h (-CoordinateAlgebra.A F.data.h - 1 / 2) v.profiles.f

noncomputable def referenceShear (p : Slow) : Plane :=
  referenceFrequency v p • !₂[-ActivationContinuation.shearA v.profiles (PositiveRepresentatives.stableInner F.data.h p),
    -ActivationContinuation.shearB v.profiles (PositiveRepresentatives.stableInner F.data.h p)]

theorem referenceFrequency_pos {p : Slow} (hp : p ∈ referenceSet W) : 0 < referenceFrequency v p := by
  have h := reference_point W hp
  exact mul_pos (Real.rpow_pos_of_pos h.scalar _) (v.positive_f h.inner_pos h.parameter)

theorem reference_continuous : ContinuousOn (referenceFrequency v) (referenceSet W) ∧
    ContinuousOn (referenceShear v) (referenceSet W) ∧ ContinuousOn (referenceLogPoint W) (referenceSet W) := by
  have hh := (ConstructedSlowBase.height_pos W).le
  have hh1 := (ConstructedSlowBase.height_lt_half W).le
  have hF : ContinuousOn (referenceFrequency v) (referenceSet W) := by
    intro p hp
    have h := reference_point W hp
    exact (PositiveRepresentatives.stablePullback_smoothAt hh hh1 _ h.stable
      (v.profiles.f_smooth.contDiffAt (d.domain.isOpen.mem_nhds
        (d.domain_nonnegative h.inner_pos.le (d.parameters_contains h.parameter))))).continuousAt.continuousWithinAt
  have hA : ContinuousOn (fun p => ActivationContinuation.shearA v.profiles
      (PositiveRepresentatives.stableInner F.data.h p)) (referenceSet W) := by
    intro p hp
    have h := reference_point W hp
    have hs := NominalConeAssembly.shears_smoothAt v.profiles
      (d.domain_nonnegative h.inner_pos.le (d.parameters_contains h.parameter)) h.inner_pos
      (v.positive_f h.inner_pos h.parameter).ne'
    exact (hs.1.comp p (PositiveRepresentatives.stableInner_smoothAt hh hh1 h.stable)).continuousAt.continuousWithinAt
  have hC : ContinuousOn (fun p => ActivationContinuation.shearB v.profiles
      (PositiveRepresentatives.stableInner F.data.h p)) (referenceSet W) := by
    intro p hp
    have h := reference_point W hp
    have hs := NominalConeAssembly.shears_smoothAt v.profiles
      (d.domain_nonnegative h.inner_pos.le (d.parameters_contains h.parameter)) h.inner_pos
      (v.positive_f h.inner_pos h.parameter).ne'
    exact (hs.2.comp p (PositiveRepresentatives.stableInner_smoothAt hh hh1 h.stable)).continuousAt.continuousWithinAt
  refine ⟨hF, signedShear_continuousOn hF hA hC, ?_⟩
  intro p hp
  have h := reference_point W hp
  have hs := (PositiveRepresentatives.stableInner_smoothAt hh hh1 h.stable).continuousAt
  exact (hs.snd.prodMk (hs.fst.log h.inner_pos.ne')).continuousWithinAt

theorem stableInner_eq_normalized (W : NominalProfile.Witness F) {p : Slow} (hT : 0 < p.2.2) :
    PositiveRepresentatives.stableInner F.data.h p = (BaseChartJets.normalizedCoordinates F.data.h p).2 := by
  rw [PositiveRepresentatives.stableInner_eq_chartInner (ConstructedSlowBase.height_pos W)
    (ConstructedSlowBase.height_lt_half W) hT, BaseChartJets.normalizedCoordinates_eq]
  rfl

theorem referenceFrequency_eq_actual (H : NominalConeAssembly.Certificate W)
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    referenceFrequency v p = BaseChartJets.leadingFrequency F.data.h W.axis.normalization
      (EntranceAlignedBase.modulatedCoefficients H v) p := by
  rw [modulated_frequency_eq H v hT hR]
  unfold referenceFrequency PositiveRepresentatives.stablePullback
  rw [stableInner_eq_normalized W hT, PositiveRepresentatives.stableQ_eq_chartQ
    (ConstructedSlowBase.height_pos W) (ConstructedSlowBase.height_lt_half W) hT,
    BaseChartJets.normalizedCoordinates_eq]

theorem referenceShear_eq_actual (H : NominalConeAssembly.Certificate W)
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) : referenceShear v p =
      PhaseEstimates.shearVector (BaseChartJets.leadingFrequency F.data.h W.axis.normalization
        (EntranceAlignedBase.modulatedCoefficients H v))
        (BaseChartJets.leadingAxial F.data.h (EntranceAlignedBase.modulatedCoefficients H v)) p := by
  have hh := ConstructedSlowBase.height_pos W
  have hh1 := ConstructedSlowBase.height_lt_half W
  have hx := normalized_X_pos hh hh1 hT hR
  have he := abs_le.mp (BaseChartJets.normalizedCoordinates_eta hh hh1 hT).le
  have hs := NominalConeAssembly.modulated_shears_eq v.profiles
    (d.domain_nonnegative hx.le (d.parameters_contains he)) hx (v.positive_f hx he).ne'
  rw [referenceShear, referenceFrequency_eq_actual v H hT hR, stableInner_eq_normalized W hT,
    modulated_shear_eq H v hT hR, hs.1, hs.2]

theorem referenceLogPoint_profile {p : Slow} (hp : p ∈ referenceSet W) :
    LeadingStressWeights.logPoint (referenceLogPoint W p) = PositiveRepresentatives.stableInner F.data.h p := by
  have h := reference_point W hp
  apply Prod.ext
  · exact Real.exp_log h.inner_pos
  · rfl

theorem reference_cone (hcone : LeadingStressWeights.FullTrueCone v)
    {p : Slow} (hp : p ∈ referenceSet W) :
    PrimaryRepresentatives.ReferenceCone (referenceFrequency v p) (referenceShear v p) := by
  have h := reference_point W hp
  obtain ⟨ha, hv⟩ := LeadingStressWeights.closed_shear_positive v hcone h.parameter h.log_mem.2
  change 0 < LeadingStressWeights.logShearA v.profiles (referenceLogPoint W p) at ha
  change 2 < LeadingStressWeights.logSpeed v.profiles (referenceLogPoint W p) at hv
  simp only [LeadingStressWeights.logShearA, LeadingStressWeights.logShearB,
    LeadingStressWeights.logSpeed, referenceLogPoint_profile hp] at ha hv
  exact referenceCone_of_speed (referenceFrequency_pos v hp) ha hv

theorem modulated_positive_reference_cone (H : NominalConeAssembly.Certificate W)
    (hcone : LeadingStressWeights.FullTrueCone v) {p : Slow}
    (hp : p ∈ PositiveRepresentatives.positivePart (referenceSet W)) :
    PrimaryRepresentatives.ReferenceCone
      (BaseChartJets.leadingFrequency F.data.h W.axis.normalization
        (EntranceAlignedBase.modulatedCoefficients H v) p)
      (PhaseEstimates.shearVector (BaseChartJets.leadingFrequency F.data.h W.axis.normalization
        (EntranceAlignedBase.modulatedCoefficients H v))
        (BaseChartJets.leadingAxial F.data.h (EntranceAlignedBase.modulatedCoefficients H v)) p) := by
  have h := reference_cone v hcone hp.1
  rwa [referenceFrequency_eq_actual v H hp.2 (reference_point W hp.1).radius,
    referenceShear_eq_actual v H hp.2 (reference_point W hp.1).radius] at h

/-- The global normalized direction is pulled back by the genuine stable
similarity branch. This includes the regular zero-time boundary. -/
theorem exists_reference_direction (hcone : LeadingStressWeights.FullTrueCone v) :
    ∃ T : Slow → Plane, ContinuousOn T (referenceSet W) ∧
      ∀ p ∈ referenceSet W, ‖T p‖ = 1 ∧
        PrimaryRepresentatives.ReferenceCone (referenceFrequency v p) (referenceShear v p) ∧
        PrimaryRepresentatives.TargetCone (referenceFrequency v p) (referenceShear v p) (T p) ∧
        ((PositiveRepresentatives.stableInner F.data.h p).1 ∈
          Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W) →
          T p = PrimaryRepresentatives.normalDirection
            (stressVector v.profiles F.data.h (PositiveRepresentatives.stableInner F.data.h p))) := by
  obtain ⟨D, hDc, hDn, hDi, hDs⟩ := exists_closed_direction v hcone
  let T : Slow → Plane := fun p => D (referenceLogPoint W p)
  refine ⟨T, hDc.comp (reference_continuous v).2.2 (fun p hp => (reference_point W hp).log_mem), ?_⟩
  intro p hp
  have h := reference_point W hp
  have hs := hDs (referenceLogPoint W p) h.log_mem (referenceFrequency v p) (referenceFrequency_pos v hp)
  have hshear : logShear v (referenceFrequency v p) (referenceLogPoint W p) = referenceShear v p := by
    unfold logShear referenceShear LeadingStressWeights.logShearA LeadingStressWeights.logShearB
    rw [referenceLogPoint_profile hp]
  rw [hshear] at hs
  refine ⟨hDn _ h.log_mem, hs.1, hs.2, ?_⟩
  intro hinner
  have hlog : (referenceLogPoint W p).2 ∈
      Ioo (LeadingStressWeights.leftEdge W) (LeadingStressWeights.rightEdge W) := by
    constructor
    · exact Real.log_lt_log (NominalConeAssembly.activeLeft_pos W) hinner.1
    · exact Real.log_lt_log h.inner_pos hinner.2
  have he := hDi (referenceLogPoint W p) ⟨h.parameter, hlog⟩
  change T p = _ at he
  rw [he]
  change PrimaryRepresentatives.normalDirection (stressVector v.profiles F.data.h
    (LeadingStressWeights.logPoint (referenceLogPoint W p))) = _
  rw [referenceLogPoint_profile hp]

/-- All reference parameters and the mixed target margin are now derived
for the actual positive-time representatives of the same aligned base.
The constants and one threshold precede every active band and label. -/
theorem modulated_representative_bounds (H : NominalConeAssembly.Certificate W)
    (hcone : LeadingStressWeights.FullTrueCone v) :
    let K := referenceSet W
    let F₀ := BaseChartJets.leadingFrequency F.data.h W.axis.normalization
      (EntranceAlignedBase.modulatedCoefficients H v)
    let G₀ := BaseChartJets.leadingAxial F.data.h (EntranceAlignedBase.modulatedCoefficients H v)
    let g₀ := PhaseEstimates.shearVector F₀ G₀
    ∃ (T : Slow → Plane) (M u eta : ℝ), 1 ≤ M ∧ 0 < u ∧ 0 < eta ∧
      ContinuousOn T K ∧ (∀ p ∈ K, ‖T p‖ = 1) ∧
      (∀ p ∈ K, (PositiveRepresentatives.stableInner F.data.h p).1 ∈
        Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W) →
        T p = PrimaryRepresentatives.normalDirection
          (stressVector v.profiles F.data.h (PositiveRepresentatives.stableInner F.data.h p))) ∧
      (∀ L : PositiveRepresentatives.ActiveLabel K,
        PrimaryRepresentatives.ParameterBounds M (PositiveRepresentatives.representative K L).1
          (F₀ (PositiveRepresentatives.representative K L))
          (g₀ (PositiveRepresentatives.representative K L))) ∧
      ∃ N : ℕ, ∀ L : PositiveRepresentatives.ActiveLabel K, N ≤ L.val.1 →
        ∀ p ∈ PositiveRepresentatives.positivePart K,
          p ∈ PrimaryRepresentatives.gridBox L.val.1 L.val.2 2 →
          ⟪T p, PrimaryRepresentatives.normalDirection (g₀ (PositiveRepresentatives.representative K L))⟫_ℝ ≤ -eta ∧
          |PrimaryRepresentatives.c0 (F₀ (PositiveRepresentatives.representative K L))
              (g₀ (PositiveRepresentatives.representative K L)) *
            ⟪T p, PrimaryRepresentatives.transverseDirection (g₀ (PositiveRepresentatives.representative K L))⟫_ℝ /
            ⟪T p, PrimaryRepresentatives.normalDirection (g₀ (PositiveRepresentatives.representative K L))⟫_ℝ| + eta ≤
            PrimaryRepresentatives.slopeRatio u := by
  dsimp only
  obtain ⟨T, hT, hspec⟩ := exists_reference_direction v hcone
  have hcont := reference_continuous v
  have hF : EqOn (BaseChartJets.leadingFrequency F.data.h W.axis.normalization
      (EntranceAlignedBase.modulatedCoefficients H v)) (referenceFrequency v)
      (PositiveRepresentatives.positivePart (referenceSet W)) := by
    intro p hp
    exact (referenceFrequency_eq_actual v H hp.2 (reference_point W hp.1).radius).symm
  have hg : EqOn (PhaseEstimates.shearVector
      (BaseChartJets.leadingFrequency F.data.h W.axis.normalization (EntranceAlignedBase.modulatedCoefficients H v))
      (BaseChartJets.leadingAxial F.data.h (EntranceAlignedBase.modulatedCoefficients H v)))
      (referenceShear v) (PositiveRepresentatives.positivePart (referenceSet W)) := by
    intro p hp
    exact (referenceShear_eq_actual v H hp.2 (reference_point W hp.1).radius).symm
  obtain ⟨M, hM, hMb⟩ := PositiveRepresentatives.representative_parameter_bounds
    (referenceSet_compact W) hcont.1 hcont.2.1 (fun p hp => (reference_point W hp).radius)
      (fun p hp => (hspec p hp).2.1) hF hg
  obtain ⟨u, eta, hu, he, N, hNb⟩ := PositiveRepresentatives.representative_target_margin
    (T := T) (Text := T) (referenceSet_compact W) hcont.1 hcont.2.1 hT
      (fun p hp => (hspec p hp).2.1) (fun p hp => (hspec p hp).2.2.1)
        hF hg (fun _ _ => rfl)
  exact ⟨T, M, u, eta, hM, hu, he, hT, fun p hp => (hspec p hp).1,
    fun p hp => (hspec p hp).2.2.2, hMb, N, hNb⟩

end ReferenceFunctions

end NavierStokes.AlignedProfileSpectralCone

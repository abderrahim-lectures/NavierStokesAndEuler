import NavierStokes.PositiveRepresentatives
import NavierStokes.SlowBorelBase
import NavierStokes.ModulatedExterior
import NavierStokes.FinalSlowBase
import NavierStokes.JointResidualLimits
import NavierStokes.SpacetimeGluing
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Endpoint extensions of the actual summed slow base

At nonzero axial coordinate the stable coordinate extension has positive q.
The original cutoff schedule therefore gives a locally finite series on an
open neighborhood crossing t = 1.  No new summation or cutoff choice is made.

For velocity and pressure, the nonzero-axial extension combines with the
proved heat exterior on the central plane.  The forward-integral potential
is only extended at nonzero axial coordinate here; a central-plane gauge
correction is a separate construction.
-/
/-! Merged from `NavierStokes.EndpointCoordinates` (in a section, so its `open`s cannot leak). -/
section
/-!
# Actual similarity coordinates across the nonzero axial endpoint

At `t=1`, `z != 0`, the explicit positive root lies on the regular stable
branch.  The extension below is built from that branch and agrees with all
actual physical coordinate jets at every point with `t<1`.
-/

noncomputable section

namespace NavierStokes.EndpointCoordinates

open Set Filter Function
open scoped Topology ContDiff
open SimilarityCoordinates

abbrev PhysicalPoint := SimilarityProfile.PhysicalPoint
abbrev Chart := SlowBorelBase.Chart

/-- The positive solution of the zero-time similarity equation. -/
noncomputable def endpointRoot (a z : ℝ) : ℝ := (z ^ 2) ^ (1 - a)⁻¹

theorem endpointRoot_pos (a : ℝ) {z : ℝ} (hz : z ≠ 0) : 0 < endpointRoot a z :=
  Real.rpow_pos_of_pos (sq_pos_of_ne_zero hz) _

theorem endpointRoot_power {a z : ℝ} (ha1 : a < 1) :
    endpointRoot a z ^ (1 - a) = z ^ 2 :=
  Real.rpow_inv_rpow (sq_nonneg z) (sub_pos.mpr ha1).ne'

theorem endpointRoot_equation {a z : ℝ} (ha1 : a < 1) (hz : z ≠ 0) :
    forwardScalar a z (endpointRoot a z) = 0 := by
  rw [forwardScalar_factor (endpointRoot_pos a hz), endpointRoot_power ha1]
  ring

theorem endpointRoot_slope {a z : ℝ} (ha1 : a < 1) (hz : z ≠ 0) :
    scalarSlope a z (endpointRoot a z) = 1 - a := by
  have hp := endpointRoot_pos a hz
  have he := endpointRoot_equation ha1 hz
  have hprod : z ^ 2 * endpointRoot a z ^ a = endpointRoot a z := by
    dsimp only [forwardScalar] at he
    linarith
  rw [scalarSlope, Real.rpow_sub_one hp.ne']
  rw [show z ^ 2 * a * (endpointRoot a z ^ a / endpointRoot a z) =
      a * (z ^ 2 * endpointRoot a z ^ a) / endpointRoot a z by ring,
    hprod, mul_div_cancel_right₀ _ hp.ne']

/-- Every nonzero point of the zero-time axis belongs to the actual regular
stable target. No inverse-coordinate extension is assumed. -/
theorem zeroTime_mem_stableTarget {a z : ℝ} (_ha : 0 < a) (ha1 : a < 1) (hz : z ≠ 0) :
    (0, z) ∈ PositiveRepresentatives.stableTarget a := by
  refine ⟨(endpointRoot a z, z), ⟨endpointRoot_pos a hz, ?_⟩,
    Prod.ext (endpointRoot_equation ha1 hz) rfl⟩
  change 0 < scalarSlope a z (endpointRoot a z)
  rw [endpointRoot_slope ha1 hz]
  linarith

theorem stableInverse_zeroTime {a z : ℝ} (ha : 0 < a) (ha1 : a < 1) (hz : z ≠ 0) :
    PositiveRepresentatives.stableInverse a (0, z) = (endpointRoot a z, z) := by
  have hs : (endpointRoot a z, z) ∈ PositiveRepresentatives.stableSource a := by
    refine ⟨endpointRoot_pos a hz, ?_⟩
    change 0 < scalarSlope a z (endpointRoot a z)
    rw [endpointRoot_slope ha1 hz]
    linarith
  have he := PositiveRepresentatives.stableInverse_forwardMap ha.le ha1.le hs
  have hf : forwardMap a (endpointRoot a z, z) = (0, z) :=
    Prod.ext (endpointRoot_equation ha1 hz) rfl
  rwa [hf] at he

noncomputable def timeAxial (p : PhysicalPoint) : ℝ × ℝ := (1 - p.1, p.2.2)

noncomputable def domain (h : ℝ) : Set PhysicalPoint :=
  timeAxial ⁻¹' PositiveRepresentatives.stableTarget (2 * h)

noncomputable def qExtension (h : ℝ) (p : PhysicalPoint) : ℝ :=
  (PositiveRepresentatives.stableInverse (2 * h) (timeAxial p)).1

noncomputable def etaExtension (h : ℝ) (p : PhysicalPoint) : ℝ :=
  p.2.2 / qExtension h p ^ ((1 - 2 * h) / 2)

noncomputable def XExtension (h : ℝ) (p : PhysicalPoint) : ℝ := p.2.1 / qExtension h p

noncomputable def innerExtension (h : ℝ) (p : PhysicalPoint) : ℝ × ℝ :=
  (XExtension h p, etaExtension h p)

noncomputable def chartExtension (h : ℝ) (p : PhysicalPoint) : Chart :=
  (qExtension h p, innerExtension h p)

theorem timeAxial_smooth : ContDiff ℝ ∞ timeAxial :=
  (contDiff_const.sub contDiff_fst).prodMk contDiff_snd.snd

theorem domain_open (h : ℝ) : IsOpen (domain h) :=
  (PositiveRepresentatives.stableTarget_open (2 * h)).preimage timeAxial_smooth.continuous

theorem endpoint_mem_domain {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (s : ℝ) {z : ℝ} (hz : z ≠ 0) : (1, (s, z)) ∈ domain h := by
  change (1 - 1, z) ∈ PositiveRepresentatives.stableTarget (2 * h)
  simpa only [sub_self] using zeroTime_mem_stableTarget (by linarith : 0 < 2 * h)
    (by linarith : 2 * h < 1) hz

theorem past_mem_domain {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) : p ∈ domain h :=
  PositiveRepresentatives.positiveTime_mem_stableTarget (by linarith) (by linarith) (sub_pos.mpr hp)

theorem qExtension_pos {h : ℝ} {p : PhysicalPoint} (hp : p ∈ domain h) : 0 < qExtension h p :=
  (PositiveRepresentatives.stableInverse_spec hp).1.1


theorem qExtension_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p ∈ domain h) : ContDiffAt ℝ ∞ (qExtension h) p :=
  ((PositiveRepresentatives.stableInverse_smoothAt (by linarith) (by linarith) hp).comp p
    timeAxial_smooth.contDiffAt).fst

theorem innerExtension_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p ∈ domain h) : ContDiffAt ℝ ∞ (innerExtension h) p := by
  have hq := qExtension_smoothAt hh hh1 hp
  have hpos := qExtension_pos hp
  exact (contDiffAt_snd.fst.div hq hpos.ne').prodMk
    (contDiffAt_snd.snd.div (hq.rpow_const_of_ne hpos.ne') (Real.rpow_pos_of_pos hpos _).ne')

theorem chartExtension_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p ∈ domain h) : ContDiffAt ℝ ∞ (chartExtension h) p :=
  (qExtension_smoothAt hh hh1 hp).prodMk (innerExtension_smoothAt hh hh1 hp)

theorem chartExtension_smoothOn {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ (chartExtension h) (domain h) :=
  fun _ hp => (chartExtension_smoothAt hh hh1 hp).contDiffWithinAt

theorem qExtension_endpoint {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (s : ℝ) {z : ℝ} (hz : z ≠ 0) : qExtension h (1, (s, z)) = endpointRoot (2 * h) z := by
  simpa only [qExtension, timeAxial, sub_self] using
    congrArg (fun x : ℝ × ℝ => x.1)
      (stableInverse_zeroTime (by linarith : 0 < 2 * h) (by linarith : 2 * h < 1) hz)

theorem chartExtension_endpoint {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (s : ℝ) {z : ℝ} (hz : z ≠ 0) :
    chartExtension h (1, (s, z)) =
      (endpointRoot (2 * h) z,
        (s / endpointRoot (2 * h) z, z / endpointRoot (2 * h) z ^ ((1 - 2 * h) / 2))) := by
  simp only [chartExtension, innerExtension, XExtension, etaExtension, qExtension_endpoint hh hh1 s hz]

theorem qExtension_eq_physical {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) : qExtension h p = SimilarityProfile.q h p := by
  simpa only [qExtension, timeAxial, SimilarityProfile.q, inverseMap] using
    congrArg (fun x : ℝ × ℝ => x.1)
      (PositiveRepresentatives.stableInverse_eq_inverseMap
        (by linarith : 0 < 2 * h) (by linarith : 2 * h < 1) (sub_pos.mpr hp))


theorem chartExtension_eq_physical {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) : chartExtension h p = SlowBorelBase.physicalChart h p := by
  change (qExtension h p, (p.2.1 / qExtension h p, p.2.2 / qExtension h p ^ ((1 - 2 * h) / 2))) =
    (SimilarityProfile.q h p,
      (p.2.1 / SimilarityProfile.q h p, p.2.2 / SimilarityProfile.q h p ^ ((1 - 2 * h) / 2)))
  rw [qExtension_eq_physical hh hh1 hp]




noncomputable def lowerDomain (h c : ℝ) : Set PhysicalPoint :=
  domain h ∩ {p | c < qExtension h p}

theorem lowerDomain_open {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (c : ℝ) :
    IsOpen (lowerDomain h c) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hD := (domain_open h).mem_nhds hp.1
  have hq := (qExtension_smoothAt hh hh1 hp.1).continuousAt.eventually (Ioi_mem_nhds hp.2)
  filter_upwards [hD, hq] with q hDq hqq
  exact ⟨hDq, hqq⟩

/-- An actual open neighborhood across the endpoint, with an explicit
positive lower bound. The bound applies to the physical coordinate on its
past portion and to the smooth extension throughout the neighborhood. -/
theorem endpoint_neighborhood {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (s : ℝ) {z : ℝ} (hz : z ≠ 0) :
    ∃ U : Set PhysicalPoint, IsOpen U ∧ (1, (s, z)) ∈ U ∧ U ⊆ domain h ∧
      ContDiffOn ℝ ∞ (chartExtension h) U ∧
      0 < endpointRoot (2 * h) z / 2 ∧
      ∀ p ∈ U, endpointRoot (2 * h) z / 2 < qExtension h p ∧
        (p.1 < 1 → endpointRoot (2 * h) z / 2 < SimilarityProfile.q h p) := by
  let U := lowerDomain h (endpointRoot (2 * h) z / 2)
  have hq := endpointRoot_pos (2 * h) hz
  have hu : (1, (s, z)) ∈ U := by
    refine ⟨endpoint_mem_domain hh hh1 s hz, ?_⟩
    change endpointRoot (2 * h) z / 2 < qExtension h (1, (s, z))
    rw [qExtension_endpoint hh hh1 s hz]
    linarith
  refine ⟨U, lowerDomain_open hh hh1 _, hu, inter_subset_left,
    (chartExtension_smoothOn hh hh1).mono inter_subset_left, half_pos hq, ?_⟩
  intro p hp
  refine ⟨hp.2, fun ht => ?_⟩
  rw [← qExtension_eq_physical hh hh1 ht]
  exact hp.2

/-! ## The actual Cartesian chart used by the slow base -/

noncomputable def cartesianDomain (h : ℝ) : Set ProblemStatement.SpaceTime :=
  (fun z => AxisymmetricFields.profilePoint z.1 z.2) ⁻¹' domain h

noncomputable def cartesianExtension (h : ℝ) (z : ProblemStatement.SpaceTime) : Chart :=
  chartExtension h (AxisymmetricFields.profilePoint z.1 z.2)

theorem cartesianDomain_open (h : ℝ) : IsOpen (cartesianDomain h) :=
  (domain_open h).preimage (AxisymmetricFields.contDiff_profilePoint (n := ∞)).continuous

theorem cartesian_endpoint_mem {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {x : ProblemStatement.Space} (hx : x 2 ≠ 0) : (1, x) ∈ cartesianDomain h :=
  endpoint_mem_domain hh hh1 (AxisymmetricFields.radialEnergy x) hx

theorem cartesianExtension_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {z : ProblemStatement.SpaceTime} (hz : z ∈ cartesianDomain h) :
    ContDiffAt ℝ ∞ (cartesianExtension h) z :=
  (chartExtension_smoothAt hh hh1 hz).comp z AxisymmetricFields.contDiff_profilePoint.contDiffAt

theorem cartesianExtension_smoothOn {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ (cartesianExtension h) (cartesianDomain h) :=
  fun _ hz => (cartesianExtension_smoothAt hh hh1 hz).contDiffWithinAt



theorem cartesianExtension_endpoint {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {x : ProblemStatement.Space} (hx : x 2 ≠ 0) :
    cartesianExtension h (1, x) =
      (endpointRoot (2 * h) (x 2),
        (AxisymmetricFields.radialEnergy x / endpointRoot (2 * h) (x 2),
          x 2 / endpointRoot (2 * h) (x 2) ^ ((1 - 2 * h) / 2))) :=
  chartExtension_endpoint hh hh1 (AxisymmetricFields.radialEnergy x) hx

theorem cartesianExtension_eq_physical {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {z : ProblemStatement.SpaceTime} (hz : z.1 < 1) :
    cartesianExtension h z = SlowBorelBase.cartesianChart h z :=
  chartExtension_eq_physical hh hh1 hz



theorem cartesian_endpoint_neighborhood {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {x : ProblemStatement.Space} (hx : x 2 ≠ 0) :
    ∃ U : Set ProblemStatement.SpaceTime, IsOpen U ∧ (1, x) ∈ U ∧ U ⊆ cartesianDomain h ∧
      ContDiffOn ℝ ∞ (cartesianExtension h) U ∧
      0 < endpointRoot (2 * h) (x 2) / 2 ∧
      ∀ z ∈ U, endpointRoot (2 * h) (x 2) / 2 < (cartesianExtension h z).1 ∧
        (z.1 < 1 → endpointRoot (2 * h) (x 2) / 2 < (SlowBorelBase.cartesianChart h z).1) := by
  obtain ⟨V, hV, hxV, hVD, hsmooth, hq, hb⟩ :=
    endpoint_neighborhood hh hh1 (AxisymmetricFields.radialEnergy x) hx
  let P := fun z : ProblemStatement.SpaceTime => AxisymmetricFields.profilePoint z.1 z.2
  refine ⟨P ⁻¹' V, hV.preimage (AxisymmetricFields.contDiff_profilePoint (n := ∞)).continuous,
    hxV, fun z hz => hVD hz, ?_, hq, ?_⟩
  · exact (cartesianExtension_smoothOn hh hh1).mono (fun z hz => hVD hz)
  · intro z hz
    refine ⟨(hb (P z) hz).1, fun ht => ?_⟩
    rw [← cartesianExtension_eq_physical hh hh1 ht]
    exact (hb (P z) hz).1

/-! ## Smooth composition and genuine derivative transfer -/




end NavierStokes.EndpointCoordinates
end


namespace NavierStokes.SlowBaseEndpoint

noncomputable section

open Set Filter Metric
open ProblemStatement SimilarityProfile SlowBorelBase
open scoped Topology ContDiff BigOperators

section LocallyFiniteProfiles

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The same coefficient series evaluated at the actual stable coordinate
extension, including the original leading power. -/
noncomputable def profileExtension (a : ℕ → ℕ) (h b : ℝ) (f : ℕ → Inner → V)
    (p : PhysicalPoint) : V :=
  (EndpointCoordinates.chartExtension h p).1 ^ b •
    slowSum a h f (EndpointCoordinates.chartExtension h p)

noncomputable def cartesianProfileExtension (a : ℕ → ℕ) (h b : ℝ)
    (f : ℕ → Inner → V) (z : SpaceTime) : V :=
  profileExtension a h b f (AxisymmetricFields.profilePoint z.1 z.2)

theorem profileExtension_smoothAt {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {f : ℕ → Inner → V}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (b : ℝ) {p : PhysicalPoint}
    (hp : p ∈ EndpointCoordinates.domain h) :
    ContDiffAt ℝ ∞ (profileExtension a h b f) p := by
  have hc := EndpointCoordinates.chartExtension_smoothAt hh hh1 hp
  have hq : 0 < (EndpointCoordinates.chartExtension h p).1 :=
    EndpointCoordinates.qExtension_pos hp
  exact (hc.fst.rpow_const_of_ne hq.ne').smul
    ((slowSum_smoothAt ha hf h hq).comp p hc)


theorem profileExtension_eq_physical (a : ℕ → ℕ) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (b : ℝ) (f : ℕ → Inner → V)
    {p : PhysicalPoint} (hp : p.1 < 1) :
    profileExtension a h b f p = physicalProfile a h b f p := by
  simp only [profileExtension, EndpointCoordinates.chartExtension_eq_physical hh hh1 hp,
    physicalProfile]

theorem profileExtension_eventuallyEq (a : ℕ → ℕ) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (b : ℝ) (f : ℕ → Inner → V)
    {p : PhysicalPoint} (hp : p.1 < 1) :
    profileExtension a h b f =ᶠ[𝓝 p] physicalProfile a h b f := by
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hp] with y hy
  exact profileExtension_eq_physical a hh hh1 b f hy

theorem cartesianProfileExtension_smoothAt {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {f : ℕ → Inner → V}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (b : ℝ) {z : SpaceTime}
    (hz : z ∈ EndpointCoordinates.cartesianDomain h) :
    ContDiffAt ℝ ∞ (cartesianProfileExtension a h b f) z :=
  (profileExtension_smoothAt ha hh hh1 hf b hz).comp z
    AxisymmetricFields.contDiff_profilePoint.contDiffAt

theorem cartesianProfileExtension_smoothOn {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {f : ℕ → Inner → V}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (b : ℝ) :
    ContDiffOn ℝ ∞ (cartesianProfileExtension a h b f) (EndpointCoordinates.cartesianDomain h) :=
  fun _ hz => (cartesianProfileExtension_smoothAt ha hh hh1 hf b hz).contDiffWithinAt


end LocallyFiniteProfiles

section ActualFields

noncomputable def streamExtension (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) : PhysicalProfile :=
  profileExtension a h (-CoordinateAlgebra.A h) (bundleComponent C d 0)

noncomputable def swirlExtension (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) : PhysicalProfile :=
  profileExtension a h (1 / 2 - CoordinateAlgebra.A h) (bundleComponent C d 1)

noncomputable def potentialExtension (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) : VelocityField :=
  AxisymmetricFields.potential (streamExtension a h C d) (swirlExtension a h C d)

noncomputable def velocityExtension (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) : VelocityField :=
  SpatialCurl.spatialCurl (potentialExtension a h C d)

noncomputable def pressureExtension (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) : PressureField :=
  cartesianProfileExtension a h (-2 * CoordinateAlgebra.A h) (bundleComponent C d 2)

theorem potentialExtension_smoothOn {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients}
    (hd : SmoothCoefficients d) (C : ℝ) :
    ContDiffOn ℝ ∞ (potentialExtension a h C d) (EndpointCoordinates.cartesianDomain h) := by
  rw [potentialExtension, BaseResidual.potential_eq_scalars]
  exact BaseResidual.potentialFromScalars_smooth
    (cartesianProfileExtension_smoothOn ha hh hh1 (bundleComponent_smooth hd C 0) _)
    (cartesianProfileExtension_smoothOn ha hh hh1 (bundleComponent_smooth hd C 1) _)

theorem velocityExtension_smoothOn {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients}
    (hd : SmoothCoefficients d) (C : ℝ) :
    ContDiffOn ℝ ∞ (velocityExtension a h C d) (EndpointCoordinates.cartesianDomain h) := by
  intro z hz
  exact (SpatialCurl.contDiffAt_spatialCurl
    ((potentialExtension_smoothOn ha hh hh1 hd C).contDiffAt
      ((EndpointCoordinates.cartesianDomain_open h).mem_nhds hz)) (by simp)).contDiffWithinAt

theorem pressureExtension_smoothOn {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients}
    (hd : SmoothCoefficients d) (C : ℝ) :
    ContDiffOn ℝ ∞ (pressureExtension a h C d) (EndpointCoordinates.cartesianDomain h) :=
  cartesianProfileExtension_smoothOn ha hh hh1 (bundleComponent_smooth hd C 2) _

theorem potentialExtension_eq (a : ℕ → ℕ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (C : ℝ) (d : Coefficients) {z : SpaceTime} (hz : z.1 < 1) :
    potentialExtension a h C d z = BaseResidual.summedPotential a h C d z := by
  have h0 := profileExtension_eq_physical a hh hh1 (-CoordinateAlgebra.A h)
    (bundleComponent C d 0) (p := AxisymmetricFields.profilePoint z.1 z.2) hz
  have h1 := profileExtension_eq_physical a hh hh1 (1 / 2 - CoordinateAlgebra.A h)
    (bundleComponent C d 1) (p := AxisymmetricFields.profilePoint z.1 z.2) hz
  simp only [potentialExtension, BaseResidual.summedPotential, AxisymmetricFields.potential,
    streamExtension, swirlExtension, h0, h1, streamFactor, swirlPotential]

theorem potentialExtension_eventuallyEq (a : ℕ → ℕ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (C : ℝ) (d : Coefficients) {z : SpaceTime} (hz : z.1 < 1) :
    potentialExtension a h C d =ᶠ[𝓝 z] BaseResidual.summedPotential a h C d := by
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hz] with y hy
  exact potentialExtension_eq a hh hh1 C d hy

theorem velocityExtension_eventuallyEq (a : ℕ → ℕ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (C : ℝ) (d : Coefficients) {z : SpaceTime} (hz : z.1 < 1) :
    velocityExtension a h C d =ᶠ[𝓝 z] baseVelocity a h C d :=
  SolenoidalDiagonal.spatialCurl_eventuallyEq (potentialExtension_eventuallyEq a hh hh1 C d hz)

theorem pressureExtension_eventuallyEq (a : ℕ → ℕ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (C : ℝ) (d : Coefficients) {z : SpaceTime} (hz : z.1 < 1) :
    pressureExtension a h C d =ᶠ[𝓝 z] basePressure a h C d := by
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hz] with y hy
  exact profileExtension_eq_physical a hh hh1 (-2 * CoordinateAlgebra.A h)
    (bundleComponent C d 2) hy


noncomputable def velocityNonzeroAxial {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d)
    (C : ℝ) {x : Space} (hx : x 2 ≠ 0) :
    JointResidualLimits.OneSidedExtension (baseVelocity a h C d) x where
  value := velocityExtension a h C d
  domain := EndpointCoordinates.cartesianDomain h
  isOpen := EndpointCoordinates.cartesianDomain_open h
  mem := EndpointCoordinates.cartesian_endpoint_mem hh hh1 hx
  smooth := velocityExtension_smoothOn ha hh hh1 hd C
  agrees := fun _ hz => (velocityExtension_eventuallyEq a hh hh1 C d hz.2.1).self_of_nhds

noncomputable def pressureNonzeroAxial {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d)
    (C : ℝ) {x : Space} (hx : x 2 ≠ 0) :
    JointResidualLimits.OneSidedExtension (basePressure a h C d) x where
  value := pressureExtension a h C d
  domain := EndpointCoordinates.cartesianDomain h
  isOpen := EndpointCoordinates.cartesianDomain_open h
  mem := EndpointCoordinates.cartesian_endpoint_mem hh hh1 hx
  smooth := pressureExtension_smoothOn ha hh hh1 hd C
  agrees := fun _ hz => (pressureExtension_eventuallyEq a hh hh1 C d hz.2.1).self_of_nhds

/-- The fixed physical radial anchor used for the exact gauge correction. -/
noncomputable def radialAnchor (p : PhysicalPoint) : PhysicalPoint := (p.1, (1, p.2.2))

theorem radialAnchor_smooth : ContDiff ℝ ∞ radialAnchor :=
  contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd.snd)

/-- This is the literal anchored-potential formula.  Equality of its curl
with the original velocity is proved in the separate gauge module. -/
noncomputable def anchoredPotential (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) : VelocityField :=
  AxisymmetricFields.potential (streamFactor a h C d)
    (fun p => swirlPotential a h C d p - swirlPotential a h C d (radialAnchor p))

noncomputable def anchoredPotentialExtension (a : ℕ → ℕ) (h C : ℝ)
    (d : Coefficients) : VelocityField :=
  AxisymmetricFields.potential (streamExtension a h C d)
    (fun p => swirlExtension a h C d p - swirlExtension a h C d (radialAnchor p))

theorem anchoredPotentialExtension_smoothOn {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients}
    (hd : SmoothCoefficients d) (C : ℝ) :
    ContDiffOn ℝ ∞ (anchoredPotentialExtension a h C d) (EndpointCoordinates.cartesianDomain h) := by
  have hanchor : ContDiffOn ℝ ∞
      (fun z : SpaceTime => swirlExtension a h C d (radialAnchor (AxisymmetricFields.profilePoint z.1 z.2)))
      (EndpointCoordinates.cartesianDomain h) := by
    intro z hz
    have hz' : radialAnchor (AxisymmetricFields.profilePoint z.1 z.2) ∈
        EndpointCoordinates.domain h := hz
    exact ((profileExtension_smoothAt ha hh hh1 (bundleComponent_smooth hd C 1)
      (1 / 2 - CoordinateAlgebra.A h) hz').comp z
        (radialAnchor_smooth.comp AxisymmetricFields.contDiff_profilePoint).contDiffAt).contDiffWithinAt
  rw [anchoredPotentialExtension, BaseResidual.potential_eq_scalars]
  exact BaseResidual.potentialFromScalars_smooth
    (cartesianProfileExtension_smoothOn ha hh hh1 (bundleComponent_smooth hd C 0) _)
    ((cartesianProfileExtension_smoothOn ha hh hh1 (bundleComponent_smooth hd C 1) _).sub hanchor)

theorem anchoredPotentialExtension_eq (a : ℕ → ℕ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (C : ℝ) (d : Coefficients) {z : SpaceTime} (hz : z.1 < 1) :
    anchoredPotentialExtension a h C d z = anchoredPotential a h C d z := by
  have h0 := profileExtension_eq_physical a hh hh1 (-CoordinateAlgebra.A h)
    (bundleComponent C d 0) (p := AxisymmetricFields.profilePoint z.1 z.2) hz
  have h1 := profileExtension_eq_physical a hh hh1 (1 / 2 - CoordinateAlgebra.A h)
    (bundleComponent C d 1) (p := AxisymmetricFields.profilePoint z.1 z.2) hz
  have hr := profileExtension_eq_physical a hh hh1 (1 / 2 - CoordinateAlgebra.A h)
    (bundleComponent C d 1) (p := radialAnchor (AxisymmetricFields.profilePoint z.1 z.2)) hz
  simp only [anchoredPotentialExtension, anchoredPotential, AxisymmetricFields.potential,
    streamExtension, swirlExtension, h0, h1, hr, streamFactor, swirlPotential]

/-- The exact anchored potential also extends at every nonzero axial
endpoint.  In particular the subtracted gauge uses the same sum and schedule. -/
noncomputable def anchoredPotentialNonzeroAxial {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d)
    (C : ℝ) {x : Space} (hx : x 2 ≠ 0) :
    JointResidualLimits.OneSidedExtension (anchoredPotential a h C d) x where
  value := anchoredPotentialExtension a h C d
  domain := EndpointCoordinates.cartesianDomain h
  isOpen := EndpointCoordinates.cartesianDomain_open h
  mem := EndpointCoordinates.cartesian_endpoint_mem hh hh1 hx
  smooth := anchoredPotentialExtension_smoothOn ha hh hh1 hd C
  agrees := fun _ hz => anchoredPotentialExtension_eq a hh hh1 C d hz.2.1

end ActualFields

section LocalClosedExtension

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Convert a genuine locally smooth closed-side continuation into an
ambient smooth extension.  A local bump and the already proved joint
Taylor--Borel extension are the actual construction. -/
theorem oneSidedExtension_of_closed_local {f g : SpaceTime → V} {x : Space}
    {U : Set SpaceTime} (hU : IsOpen U) (hxU : (1, x) ∈ U)
    (hg : ContDiffOn ℝ ∞ g (U ∩ SpacetimeEndpoint.closedPast 1))
    (he : EqOn g f (U ∩ SpacetimeEndpoint.openPast 1)) :
    Nonempty (JointResidualLimits.OneSidedExtension f x) := by
  obtain ⟨r, hr, hrU⟩ : ∃ r, 0 < r ∧ closedBall (1, x) r ⊆ U :=
    nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hxU)
  let χ : ContDiffBump ((1 : ℝ), x) :=
    { rIn := r / 2, rOut := r, rIn_pos := half_pos hr, rIn_lt_rOut := half_lt_self hr }
  let cut : SpaceTime → V := fun z => χ z • g z
  have hlocal : ContDiffOn ℝ ∞ cut (SpacetimeEndpoint.closedPast 1) := by
    intro z hz
    by_cases hzU : z ∈ U
    · have hgs : ContDiffWithinAt ℝ ∞ g (SpacetimeEndpoint.closedPast 1) z :=
        (hg z ⟨hzU, hz⟩).mono_of_mem_nhdsWithin
          (inter_mem (nhdsWithin_le_nhds (hU.mem_nhds hzU)) self_mem_nhdsWithin)
      exact χ.contDiff.contDiffWithinAt.smul hgs
    · have hzχ : z ∉ tsupport (χ : SpaceTime → ℝ) := by
        rw [χ.tsupport_eq]
        exact fun hzχ => hzU (hrU hzχ)
      have hz0 : (χ : SpaceTime → ℝ) =ᶠ[𝓝 z] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp hzχ
      have hl0 : cut =ᶠ[𝓝 z] (fun _ => 0) := by
        filter_upwards [hz0] with y hy
        change χ y = 0 at hy
        simp only [cut, hy, zero_smul]
      exact (contDiffAt_const.congr_of_eventuallyEq hl0).contDiffWithinAt
  let G := SpacetimeGluing.smoothExtension 1 cut hlocal
  refine ⟨⟨G, ball (1, x) (r / 2), isOpen_ball, mem_ball_self (half_pos hr),
    (SpacetimeGluing.smoothExtension_contDiff hlocal).contDiffOn, ?_⟩⟩
  intro z hz
  have hzU : z ∈ U := hrU ((ball_subset_closedBall.trans
    (closedBall_subset_closedBall (half_le_self hr.le))) hz.1)
  have hzP : z ∈ SpacetimeEndpoint.closedPast 1 :=
    ⟨(show z.1 < 1 from hz.2.1).le, hz.2.2⟩
  change SpacetimeGluing.smoothExtension 1 cut hlocal z = f z
  rw [SpacetimeGluing.smoothExtension_eqOn_past hlocal hzP]
  change χ z • g z = f z
  rw [χ.one_of_mem_closedBall (mem_closedBall.mpr (mem_ball.mp hz.1).le), one_smul]
  exact he ⟨hzU, hz.2⟩

end LocalClosedExtension

theorem radialEnergy_pos_of_nonzero_of_axial_zero {x : Space} (hx : x ≠ 0) (hz : x 2 = 0) :
    0 < AxisymmetricFields.radialEnergy x := by
  by_contra h
  have hr := AxisymmetricFields.radialEnergy_nonneg x
  have he : AxisymmetricFields.radialEnergy x = 0 := le_antisymm (le_of_not_gt h) hr
  have h0 : x 0 = 0 := by
    dsimp only [AxisymmetricFields.radialEnergy] at he
    nlinarith [sq_nonneg (x 1), sq_nonneg (x 0)]
  have h1 : x 1 = 0 := by
    dsimp only [AxisymmetricFields.radialEnergy] at he
    nlinarith [sq_nonneg (x 1), sq_nonneg (x 0)]
  apply hx
  ext i
  fin_cases i <;> simpa only [PiLp.zero_apply] using (show x _ = 0 from by assumption)

section CompleteAwayExtensions

open GlobalSlowProfiles AssembledSlowBase ModulatedExterior

/-- For the actual repaired scheme, velocity and pressure have ambient
smooth continuations at every nonzero point of the terminal slice. -/
theorem realized_fields_awayExtensions {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
    {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)
    {s : Scheme S F.data.h W.axis.normalization} {d : Coefficients}
    (hd : RealizesScheme s M.contains d)
    (hbase : s.base = (modifiedScheme W Q M).base) (houter : s.B = nominalOuterRadius W)
    (hds : SmoothCoefficients d) (henergy : RestoredSquaredSwirl W Q (S := S))
    {a : ℕ → ℕ} (ha : StrictMono a) :
    JointResidualLimits.AwayExtensions (baseVelocity a F.data.h W.axis.normalization d) ∧
      JointResidualLimits.AwayExtensions (basePressure a F.data.h W.axis.normalization d) := by
  have hall (x : Space) (hx : x ≠ 0) :
      Nonempty (JointResidualLimits.OneSidedExtension
        (baseVelocity a F.data.h W.axis.normalization d) x) ∧
      Nonempty (JointResidualLimits.OneSidedExtension
        (basePressure a F.data.h W.axis.normalization d) x) := by
    by_cases hz : x 2 = 0
    · obtain ⟨U, hU, hxU, _, _, hu, hp⟩ := realized_terminal_extension W Q M hd hbase houter
        hds henergy ha hz (radialEnergy_pos_of_nonzero_of_axial_zero hx hz)
      constructor
      · apply oneSidedExtension_of_closed_local hU hxU hu
        exact fun _ hy => completedVelocity_before _ _ _ hy.2.1
      · apply oneSidedExtension_of_closed_local hU hxU hp
        exact fun _ hy => completedPressure_before _ _ _ hy.2.1
    · exact ⟨⟨velocityNonzeroAxial ha F.data.h_pos F.data.h_lt_half hds W.axis.normalization hz⟩,
        ⟨pressureNonzeroAxial ha F.data.h_pos F.data.h_lt_half hds W.axis.normalization hz⟩⟩
  exact ⟨fun x hx => (hall x hx).1, fun x hx => (hall x hx).2⟩

end CompleteAwayExtensions

section FinalBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)



noncomputable def finalPressureNonzeroAxial (upper : ℝ) (B : ℕ) {x : Space}
    (hx : x 2 ≠ 0) :
    JointResidualLimits.OneSidedExtension (FinalSlowBase.pressure H v upper B) x :=
  pressureNonzeroAxial (FinalSlowBase.scales_strictMono H v upper B)
    F.data.h_pos F.data.h_lt_half (FinalSlowBase.coefficients_smooth H v) W.axis.normalization hx


/-- This includes the central plane and the spatial axis away from zero.
The inputs are the actual finite profile witnesses, not endpoint assumptions. -/
theorem final_fields_awayExtensions (upper : ℝ) (B : ℕ) :
    JointResidualLimits.AwayExtensions (FinalSlowBase.velocity H v upper B) ∧
      JointResidualLimits.AwayExtensions (FinalSlowBase.pressure H v upper B) :=
  realized_fields_awayExtensions W v.profiles v.finiteModification
    (FinalSlowBase.realizesScheme H v) (EntranceAlignedBase.modulated_base_eq H v)
    (EntranceAlignedBase.modulated_outer H v) (FinalSlowBase.coefficients_smooth H v)
    (ModulatedExterior.actual_squared_swirl_restored v) (FinalSlowBase.scales_strictMono H v upper B)



end FinalBase

end

end NavierStokes.SlowBaseEndpoint

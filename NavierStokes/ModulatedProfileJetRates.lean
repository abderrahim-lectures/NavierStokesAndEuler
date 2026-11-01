import NavierStokes.ModulatedCone

noncomputable section

namespace NavierStokes.ModulatedProfileJetRates

open Set Filter Function ModulatedHistories
open scoped Topology ContDiff BigOperators

/-- One coefficient family and one local inverse branch serve all derivative
orders. Only the asymptotic threshold and constant may depend on the order. -/
structure SmoothRepairFamily (P : FiveProfileMoments.Patch) (b : ℝ)
    (A G : ℝ → ℝ) (d : ℝ → ℝ → Debt) (S : Set ℝ) where
  coefficients : ℝ → ℝ → Coeff
  smooth : ∀ N, ContDiff ℝ ∞ (coefficients N)
  region : ℝ → Set ℝ
  region_open : ∀ N, IsOpen (region N)
  threshold : ℝ
  threshold_ge_one : 1 ≤ threshold
  contains : ∀ N, threshold ≤ N → S ⊆ region N
  solves : ∀ N eta, eta ∈ region N →
    FiveProfileMoments.physicalMoments P b (A eta) (G eta) (coefficients N eta) = d N eta
  positive : ∀ N eta, eta ∈ region N → ∀ X, 0 < X →
    0 < FiveProfileMoments.physicalE P b (A eta) (coefficients N eta) X
  rates : ∀ q : ℕ, ∃ Nq C : ℝ, 1 ≤ Nq ∧ 0 < C ∧ ∀ N : ℝ, Nq ≤ N →
    JetBounds.FiniteJetBound q (coefficients N) S (C / N)



variable {a m p₁ p₂ : Point → ℝ} {K B : Set Point}


theorem localized_profile_eta_rates (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (S : Set ℝ) (hS : IsCompact S) (q : ℕ) :
    ∃ CF CU : ℝ, 0 ≤ CF ∧ 0 ≤ CU ∧ ∀ N : ℝ, 1 ≤ N → ∀ X eta : ℝ, eta ∈ S →
      |iteratedDeriv q (fun e => localizedF W r f N (X, e)) eta -
        iteratedDeriv q (fun e => f (X, e)) eta| ≤ CF / N ∧
      |iteratedDeriv q (fun e => localizedU W r E U N (X, e)) eta -
        iteratedDeriv q (fun e => U (X, e)) eta| ≤ CU / N := by
  obtain ⟨CF, _, hCF, _, hbF⟩ := ParametricModulation.realized_profiles_uniform_eta_jets
    r f U ha hm hp₂ hf hU (Icc W.left W.right) S isCompact_Icc hS q
  obtain ⟨_, CU, _, hCU, hbU⟩ := ParametricModulation.realized_profiles_uniform_eta_jets
    r E U ha hm hp₂ hE hU (Icc W.left W.right) S isCompact_Icc hS q
  refine ⟨CF, CU, hCF, hCU, ?_⟩
  intro N hN X eta heta
  by_cases hX : X ∈ Ioc W.left W.right
  · have heF : (fun e => localizedF W r f N (X, e)) = ParametricModulation.realizedE r f N X := by
      funext e
      simp only [localizedF, splice, hX, ite_true, rawF]
    have heU : (fun e => localizedU W r E U N (X, e)) = ParametricModulation.realizedU r E U N X := by
      funext e
      simp only [localizedU, splice, hX, ite_true, rawU]
    rw [heF, heU]
    exact ⟨(hbF N hN X ⟨hX.1.le, hX.2⟩ eta heta).1, (hbU N hN X ⟨hX.1.le, hX.2⟩ eta heta).2⟩
  · have heF : (fun e => localizedF W r f N (X, e)) = (fun e => f (X, e)) := by
      funext e
      simp only [localizedF, splice, hX, ite_false]
    have heU : (fun e => localizedU W r E U N (X, e)) = (fun e => U (X, e)) := by
      funext e
      simp only [localizedU, splice, hX, ite_false]
    rw [heF, heU]
    simpa only [sub_self, abs_zero] using
      And.intro (div_nonneg hCF (zero_lt_one.trans_le hN).le) (div_nonneg hCU (zero_lt_one.trans_le hN).le)

theorem localized_profile_eta_smooth (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U) (N X : ℝ) :
    ContDiff ℝ ∞ (fun e => localizedF W r f N (X, e)) ∧
      ContDiff ℝ ∞ (fun e => localizedU W r E U N (X, e)) := by
  have hbase : ContDiff ℝ ∞ (fun e : ℝ => (X, e)) := contDiff_const.prodMk contDiff_id
  by_cases hX : X ∈ Ioc W.left W.right
  · have heF : (fun e => localizedF W r f N (X, e)) = fun e =>
        f (X, e) * Real.exp (r.angularPrimitive ((X, e), N * Real.log X) / N) := by
      funext e
      simp only [localizedF, splice, hX, ite_true, rawF, ParametricModulation.realizedE,
        RadialModulation.modulatedE, RadialModulation.phasePoint, ParametricModulation.asRadialPrimitive]
    have heU : (fun e => localizedU W r E U N (X, e)) = fun e =>
        U (X, e) + r.axialPrimitive E ((X, e), N * Real.log X) / N := by
      funext e
      simp only [localizedU, splice, hX, ite_true, rawU, ParametricModulation.realizedU,
        RadialModulation.modulatedU, RadialModulation.phasePoint, ParametricModulation.asRadialPrimitive]
    rw [heF, heU]
    have hp := r.primitives_smooth E ha hm hp₂ hE
    have hz : ContDiff ℝ ∞ (fun e : ℝ => ((X, e), N * Real.log X)) := hbase.prodMk contDiff_const
    exact ⟨(hf.comp hbase).mul (((hp.1.comp hz).div_const N).exp),
      (hU.comp hbase).add ((hp.2.comp hz).div_const N)⟩
  · have heF : (fun e => localizedF W r f N (X, e)) = fun e => f (X, e) := by
      funext e
      simp only [localizedF, splice, hX, ite_false]
    have heU : (fun e => localizedU W r E U N (X, e)) = fun e => U (X, e) := by
      funext e
      simp only [localizedU, splice, hX, ite_false]
    rw [heF, heU]
    exact ⟨hf.comp hbase, hU.comp hbase⟩

/-- Every fixed parameter derivative of the actual repaired profiles has
the same inverse-frequency rate, for one previously selected repair family. -/
theorem SmoothRepairFamily.profile_eta_rates
    (W : Window) (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    {P : FiveProfileMoments.Patch} {b : ℝ} {A G : ℝ → ℝ} {d : ℝ → ℝ → Debt} {S : Set ℝ}
    (H : SmoothRepairFamily P b A G d S) (hS : IsCompact S) (hA : ContDiff ℝ ∞ A) (q : ℕ) :
    ∃ Nq C : ℝ, 1 ≤ Nq ∧ 0 < C ∧ ∀ N : ℝ, Nq ≤ N → ∀ X eta : ℝ, eta ∈ S →
      |iteratedDeriv q (fun e => applyRepairF P A (H.coefficients N) (localizedF W r f N) (X, e)) eta -
        iteratedDeriv q (fun e => f (X, e)) eta| ≤ C / N ∧
      |iteratedDeriv q (fun e => applyRepairU P A (H.coefficients N) (localizedU W r E U N) (X, e)) eta -
        iteratedDeriv q (fun e => U (X, e)) eta| ≤ C / N := by
  obtain ⟨Nq, Cc, hNq, hCc, hcb⟩ := H.rates q
  obtain ⟨CF, CU, hCF, hCU, hmod⟩ := localized_profile_eta_rates W r f E U ha hm hp₂ hf hE hU S hS q
  obtain ⟨Ce, hCe, hedit⟩ := normalized_edits_eta_bound P S hS A hA q
  refine ⟨Nq, 1 + CF + CU + Ce * Cc, hNq, by positivity, ?_⟩
  intro N hN X eta heta
  have hN1 := hNq.trans hN
  have hNp := zero_lt_one.trans_le hN1
  have hmodb := hmod N hN1 X eta heta
  have heditb := hedit (H.coefficients N) (H.smooth N) (Cc / N) (div_nonneg hCc.le hNp.le)
    (hcb N hN) eta heta q le_rfl X
  have hs := localized_profile_eta_smooth W r f E U ha hm hp₂ hf hE hU N X
  have heF : ContDiff ℝ ∞ (fun e => editF P A (H.coefficients N) (X, e)) :=
    (editF_contDiff P A (H.coefficients N) hA (H.smooth N)).comp (contDiff_const.prodMk contDiff_id)
  have heU : ContDiff ℝ ∞ (fun e => editU P A (H.coefficients N) (X, e)) :=
    (editU_contDiff P A (H.coefficients N) hA (H.smooth N)).comp (contDiff_const.prodMk contDiff_id)
  have horder : (q : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  constructor
  · change |iteratedDeriv q (fun e => localizedF W r f N (X, e) + editF P A (H.coefficients N) (X, e)) eta - _| ≤ _
    rw [iteratedDeriv_fun_add (hs.1.of_le horder).contDiffAt (heF.of_le horder).contDiffAt]
    calc
      _ = |(iteratedDeriv q (fun e => localizedF W r f N (X, e)) eta -
          iteratedDeriv q (fun e => f (X, e)) eta) + iteratedDeriv q (fun e => editF P A (H.coefficients N) (X, e)) eta| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans ((add_le_add hmodb.1 heditb.1).trans (by
        calc
          CF / N + Ce * (Cc / N) = (CF + Ce * Cc) / N := by ring
          _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hNp.le))
  · change |iteratedDeriv q (fun e => localizedU W r E U N (X, e) + editU P A (H.coefficients N) (X, e)) eta - _| ≤ _
    rw [iteratedDeriv_fun_add (hs.2.of_le horder).contDiffAt (heU.of_le horder).contDiffAt]
    calc
      _ = |(iteratedDeriv q (fun e => localizedU W r E U N (X, e)) eta -
          iteratedDeriv q (fun e => U (X, e)) eta) + iteratedDeriv q (fun e => editU P A (H.coefficients N) (X, e)) eta| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans ((add_le_add hmodb.2 heditb.2).trans (by
        calc
          CU / N + Ce * (Cc / N) = (CU + Ce * Cc) / N := by ring
          _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hNp.le))

/-- All five actual integral histories share that same repaired family and
the same inverse-frequency rate, uniformly in every upper radial endpoint. -/
theorem SmoothRepairFamily.history_eta_rates
    (W : Window) (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    {P : FiveProfileMoments.Patch} (hWP : W.right < P.left) {b : ℝ} {A G : ℝ → ℝ}
    {d : ℝ → ℝ → Debt} {S : Set ℝ} (H : SmoothRepairFamily P b A G d S)
    (hS : IsCompact S) (hA : ContDiff ℝ ∞ A) (q : ℕ) :
    ∃ Nq C : ℝ, 1 ≤ Nq ∧ 0 < C ∧ ∀ N : ℝ, Nq ≤ N → ∀ X : ℝ, 0 ≤ X →
      JetBounds.FiniteJetBound q (fun eta =>
        axisHistory (applyRepairF P A (H.coefficients N) (localizedF W r f N))
          (applyRepairU P A (H.coefficients N) (localizedU W r E U N)) (X, eta) - axisHistory f U (X, eta))
        S (C / N) := by
  obtain ⟨Nc, Cc, hNc, hCc, hcb⟩ := H.rates q
  obtain ⟨delta, C1, C2, hd, hC1, hC2, hb⟩ := repaired_axisHistory_jets
    W r f E U ha hm hp₂ hf hE hU P hWP A hA S hS q
  refine ⟨max Nc (Cc / delta), C1 + C2 * Cc, hNc.trans (le_max_left _ _), by positivity, ?_⟩
  intro N hN X hX
  have hnc : Nc ≤ N := (le_max_left _ _).trans hN
  have hN1 := hNc.trans hnc
  have hNp := zero_lt_one.trans_le hN1
  have he : Cc / N ≤ delta := by
    apply (div_le_iff₀ hNp).mpr
    have ht := (div_le_iff₀ hd).mp ((le_max_right _ _).trans hN)
    nlinarith
  convert hb N hN1 (H.coefficients N) (H.smooth N) (Cc / N)
    (div_nonneg hCc.le hNp.le) he (hcb N hnc) X hX using 1
  ring

/-- The parameter estimates apply to the physical angular field, axial field,
and all five profile rows (including pressure) of the same repaired profiles. -/
theorem SmoothRepairFamily.repaired_profiles_eta_rates
    (W : Window) (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    {patch : FiveProfileMoments.Patch} (hgap : W.right < patch.left)
    {b : ℝ} {A G : ℝ → ℝ} {d : ℝ → ℝ → Debt} {S : Set ℝ}
    (H : SmoothRepairFamily patch b A G d S) (hS : IsCompact S) (hA : ContDiff ℝ ∞ A)
    {D D' : ProfileHistories.RadialDomain}
    (R : ℝ → ProfileHistories.Profiles D) (Q : ProfileHistories.Profiles D')
    (hRf : ∀ N, (R N).f = applyRepairF patch A (H.coefficients N) (localizedF W r f N))
    (hRU : ∀ N, (R N).U = applyRepairU patch A (H.coefficients N) (localizedU W r E U N))
    (hQf : Q.f = f) (hQU : Q.U = U) (hP0 : ∀ N, (R N).pressure0 = Q.pressure0)
    (Xmax : ℝ) (q : ℕ) :
    ∃ Nq C : ℝ, 1 ≤ Nq ∧ 0 < C ∧ ∀ N : ℝ, Nq ≤ N →
      (∀ X eta : ℝ, X ≤ Xmax → eta ∈ S →
        |iteratedDeriv q (fun e => (R N).E (X, e)) eta -
          iteratedDeriv q (fun e => Q.E (X, e)) eta| ≤ C / N ∧
        |iteratedDeriv q (fun e => (R N).U (X, e)) eta -
          iteratedDeriv q (fun e => Q.U (X, e)) eta| ≤ C / N) ∧
      (∀ X : ℝ, 0 ≤ X → JetBounds.FiniteJetBound q
        (fun eta => profileRows (R N) (X, eta) - profileRows Q (X, eta)) S (C / N)) := by
  obtain ⟨Np, Cp, hNp, hCp, hp⟩ := H.profile_eta_rates W r f E U ha hm hp₂ hf hE hU hS hA q
  obtain ⟨Nh, Ch, hNh, hCh, hh⟩ := H.history_eta_rates W r f E U ha hm hp₂ hf hE hU hgap hS hA q
  let C := (1 + Real.sqrt (2 * Xmax)) * Cp + Ch
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨max Np Nh, C, hNp.trans (le_max_left _ _), hC, ?_⟩
  intro N hN
  have hnp := (le_max_left _ _).trans hN
  have hnh := (le_max_right _ _).trans hN
  have hNpos := zero_lt_one.trans_le (hNp.trans hnp)
  have hCpC : Cp ≤ C := by dsimp [C]; nlinarith [Real.sqrt_nonneg (2 * Xmax)]
  have hChC : Ch ≤ C := by dsimp [C]; nlinarith [Real.sqrt_nonneg (2 * Xmax)]
  constructor
  · intro X eta hX heta
    have hb := hp N hnp X eta heta
    constructor
    · simp only [ProfileHistories.Profiles.E, hRf N, hQf,
        iteratedDeriv_const_mul_field, ← mul_sub, abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg (2 * X))]
      calc
        _ ≤ Real.sqrt (2 * X) * (Cp / N) := mul_le_mul_of_nonneg_left hb.1 (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt (2 * Xmax) * (Cp / N) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (div_nonneg hCp.le hNpos.le)
        _ = (Real.sqrt (2 * Xmax) * Cp) / N := by ring
        _ ≤ C / N := div_le_div_of_nonneg_right (by dsimp [C]; nlinarith) hNpos.le
    · rw [hRU N, hQU]
      exact hb.2.trans (div_le_div_of_nonneg_right hCpC hNpos.le)
  · intro X hX
    have heq : (fun eta => profileRows (R N) (X, eta) - profileRows Q (X, eta)) =
        (fun eta => axisHistory (applyRepairF patch A (H.coefficients N) (localizedF W r f N))
          (applyRepairU patch A (H.coefficients N) (localizedU W r E U N)) (X, eta) -
          axisHistory f U (X, eta)) := by
      funext eta
      rw [profileRows_sub (R N) Q (hP0 N), hRf N, hRU N, hQf, hQU]
    rw [heq]
    intro eta heta j hj
    exact (hh N hnh X hX eta heta j hj).trans (div_le_div_of_nonneg_right hChC hNpos.le)

open ProfileHistories (RadialDomain Profiles)
open ParametricModulation ModulatedCone ModulatedCone.Repaired


end NavierStokes.ModulatedProfileJetRates

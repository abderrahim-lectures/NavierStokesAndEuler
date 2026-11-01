import NavierStokes.ReferenceUniformJets
import NavierStokes.ClosedIntervalJetAlgebra

/-! # Reference history and stock bounds chosen before amplitude and width -/

noncomputable section

namespace NavierStokes.ReferenceUniformStocks

open Set Filter MeasureTheory ProfileHistories ReferencePath
open ReferenceUniformJets ClosedIntervalJetAlgebra
open scoped Topology ContDiff

/-- A family of smooth parameter functions with one bound for all its members. -/
def Uniform {ι : Type*} (k : ℕ) (F : ι → ℝ → ℝ) : Prop :=
  (∀ i, ContDiffOn ℝ ∞ (F i) J) ∧ ∃ B, 0 ≤ B ∧ ∀ i, Bound k (F i) B

namespace Uniform

variable {ι κ : Type*} {k : ℕ} {F G : ι → ℝ → ℝ}

theorem reindex (hF : Uniform k F) (r : κ → ι) : Uniform k (fun i => F (r i)) :=
  ⟨fun i => hF.1 (r i), by obtain ⟨B,hB,hb⟩ := hF.2; exact ⟨B,hB,fun i => hb (r i)⟩⟩

theorem of_le (hF : Uniform k F) {n : ℕ} (hn : n ≤ k) : Uniform n F :=
  ⟨hF.1, by obtain ⟨B,hB,hb⟩ := hF.2; exact ⟨B,hB,fun i => (hb i).of_le hn⟩⟩

theorem const (c : ℝ) : Uniform k (fun _ : ι => fun _ : ℝ => c) :=
  ⟨fun _ => contDiffOn_const, |c|, abs_nonneg c, fun _ => Bound.const k c⟩

theorem id : Uniform k (fun _ : ι => fun η : ℝ => η) :=
  ⟨fun _ => contDiffOn_id, 1, zero_le_one, fun _ => Bound.id k⟩

theorem parameter (c : ι → ℝ) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i, |c i| ≤ B) :
    Uniform k (fun i => fun _ : ℝ => c i) :=
  ⟨fun _ => contDiffOn_const, B, hB, fun i => (Bound.const k (c i)).mono (hb i)⟩

theorem add (hF : Uniform k F) (hG : Uniform k G) :
    Uniform k (fun i η => F i η + G i η) := by
  obtain ⟨B,hB,hb⟩ := hF.2
  obtain ⟨C,hC,hc⟩ := hG.2
  exact ⟨fun i => (hF.1 i).add (hG.1 i), B+C, add_nonneg hB hC,
    fun i => (hb i).add (hF.1 i) (hG.1 i) (hc i)⟩

theorem sub (hF : Uniform k F) (hG : Uniform k G) :
    Uniform k (fun i η => F i η - G i η) := by
  obtain ⟨B,hB,hb⟩ := hF.2
  obtain ⟨C,hC,hc⟩ := hG.2
  exact ⟨fun i => (hF.1 i).sub (hG.1 i), B+C, add_nonneg hB hC,
    fun i => (hb i).sub (hF.1 i) (hG.1 i) (hc i)⟩

theorem mul (hF : Uniform k F) (hG : Uniform k G) :
    Uniform k (fun i η => F i η * G i η) := by
  obtain ⟨B,hB,hb⟩ := hF.2
  obtain ⟨C,hC,hc⟩ := hG.2
  exact ⟨fun i => (hF.1 i).mul (hG.1 i), 2^k*B*C,
    mul_nonneg (mul_nonneg (by positivity) hB) hC,
    fun i => (hb i).mul (hF.1 i) (hG.1 i) (hc i)⟩

theorem neg (hF : Uniform k F) : Uniform k (fun i η => -F i η) := by
  simpa only [zero_sub] using (const (ι := ι) (k := k) 0).sub hF

theorem congr (hF : Uniform k F) (he : ∀ i, EqOn (G i) (F i) J) : Uniform k G := by
  obtain ⟨B,hB,hb⟩ := hF.2
  exact ⟨fun i => (hF.1 i).congr (he i), B,hB,fun i => (hb i).congr (he i)⟩

theorem inverse (hF : Uniform k F) {μ : ℝ} (hμ : 0 < μ)
    (hp : ∀ i η, η ∈ J → μ ≤ F i η) : Uniform k (fun i η => (F i η)⁻¹) := by
  obtain ⟨B,hB,hb⟩ := hF.2
  obtain ⟨C,hC,hc⟩ := inverse_bound k μ B hμ
  exact ⟨fun i => (hF.1 i).inv (fun η hη => (hμ.trans_le (hp i η hη)).ne'),
    C,hC,fun i => hc _ (hF.1 i) (hp i) (hb i)⟩

end Uniform




abbrev Slab (R : ℝ) := {X : ℝ // X ∈ Icc 0 R}

abbrev FieldUniform {ι : Type*} (k : ℕ) (R : ℝ) (F : ι → Field) : Prop :=
  Uniform k (fun q : ι × Slab R => fun η => F q.1 (q.2,η))




theorem parameterPartial_const_mul (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) (c : ℝ) {p : Point} (hp : p ∈ D.carrier) :
    parameterPartial (fun q => c*F q) p = c*parameterPartial F p :=
  (parameterPartial_hasDerivAt D (contDiffOn_const.mul hF) hp).unique
    ((parameterPartial_hasDerivAt D hF hp).const_mul c)

def axialFormula {D : RadialDomain} (P : Profiles D) (h : ℝ) (p : Point) : ℝ :=
  (-ActivationStocks.massFlux h p.1 p.2 (P.M p) (parameterPartial P.M p)*P.U p +
    NaturalAxisData.D h*(P.M p-p.2*parameterPartial P.M p) +
    4*h*p.2*P.S p-NaturalAxisData.d p.2*parameterPartial P.S p +
    p.1*(4*NaturalAxisData.A h*p.2*P.pressure p-
      NaturalAxisData.d p.2*parameterPartial P.pressure p)) / NaturalAxisData.L h p.2


def angularNormalizedFormula {D : RadialDomain} (P : Profiles D) (h C : ℝ) (p : Point) : ℝ :=
  (-ActivationStocks.massFlux h p.1 p.2 (P.M p) (parameterPartial P.M p) +
    ActivationStocks.angularRemainder h p.2 (C*P.I p)
      (parameterPartial (fun q => C*P.I q) p) (C*P.J p)
      (parameterPartial (fun q => C*P.J q) p) * (2*p.1)⁻¹ * (C*P.f p)⁻¹) /
      NaturalAxisData.L h p.2


section ActualReference

open NaturalProfile

variable {h j σ Λ : ℝ} {P0 : ℝ → ℝ}
    (d : NaturalAxisCoefficients.AnalyticInputs h j σ P0)

/-- All amplitudes and all admissible cutoff widths are quantified together. -/
structure Choice (Λ : ℝ) where
  C : ℝ
  C_ge_one : 1 ≤ C
  profile : NaturalEntrance.CoefficientProfile d Λ C
  δ : ℝ
  δ_pos : 0 < δ
  δ_lt : 2*δ < rampLimit

namespace Choice

variable {d}

def input (hΛ : 0 < Λ) (q : Choice d Λ) : Input := Input.ofNatural hΛ q.profile.family

def profiles (hΛ : 0 < Λ) (hP0 : ContDiff ℝ ∞ P0) (q : Choice d Λ) :
    Profiles (q.input hΛ).radialDomain :=
  (q.input hΛ).histories q.δ_pos q.δ_lt P0 hP0

theorem mem (hΛ : 0 < Λ) (q : Choice d Λ) {X η : ℝ} (hX : 0 ≤ X)
    (hη : η ∈ J) : (X,η) ∈ (q.input hΛ).radialDomain.carrier :=
  ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg hΛ.le hX), NaturalAxisCoefficients.original_interval_interior hη⟩


end Choice

variable (hΛ : 0 < Λ) (hP0 : ContDiff ℝ ∞ P0)








abbrev PositiveSlab (a R : ℝ) := {X : ℝ // X ∈ Icc a R}

def toSlab {a R : ℝ} (ha : 0 ≤ a) (X : PositiveSlab a R) : Slab R :=
  ⟨X,ha.trans X.property.1,X.property.2⟩



end ActualReference

end NavierStokes.ReferenceUniformStocks

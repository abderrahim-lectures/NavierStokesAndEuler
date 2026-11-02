import NavierStokes.ClosedIntervalJetAlgebra
import NavierStokes.NaturalAxisData
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Parameter-jet comparison for the actual five cumulative seed histories

The comparison is on the closed parameter interval, using one-sided derivatives
at its endpoints. Profiles need not be regular at the axis. The constants are
uniform over all profiles with the stated positivity and finite jet bounds.
-/

noncomputable section

namespace NavierStokes.SeedHandbackJets

open Set ClosedIntervalJetAlgebra
open scoped ContDiff

abbrev Curves := Fin 7 → ℝ → ℝ
abbrev Packet := Fin 12 → ℝ → ℝ
abbrev Basis := Fin 19 → ℝ → ℝ

/-- `E,U,M,I,J,S,Cp`, followed by the first parameter derivatives needed by the lags. -/
def packet (P₀ : ℝ → ℝ) (f : Curves) : Packet :=
  ![f 0, f 1, f 2, derivWithin (f 2) J,
    f 3, derivWithin (f 3) J, f 4, derivWithin (f 4) J,
    f 5, derivWithin (f 5) J, (fun η => P₀ η + f 6 η),
    derivWithin (fun η => P₀ η + f 6 η) J]


def basis (h X : ℝ) (p : Packet) : Basis :=
  ![p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7, p 8, p 9, p 10, p 11,
    (fun η => η), (fun _ => X), (fun _ => X⁻¹),
    (fun _ => (Real.sqrt (2*X))⁻¹), (fun η => (p 0 η)⁻¹),
    (fun η => (NaturalAxisData.L h η)⁻¹), NaturalAxisData.d]

abbrev Expr := PolynomialExpression (Fin 19)

private def v (i : Fin 19) : Expr := .input i
private def c (x : ℝ) : Expr := .constant x
def massExpression (h : ℝ) : Expr :=
  .mul (.sub (.sub (v 13) (.mul (.mul (c (2*NaturalAxisData.D h)) (v 12)) (v 2)))
    (.mul (v 18) (v 3))) (v 14)

def angularExpression (h : ℝ) : Expr :=
  .add (.sub (c 0) (massExpression h))
    (.mul (.mul (.mul
      (.add (.sub (.sub (.mul (c (1-h)) (v 4))
        (.mul (.mul (c (NaturalAxisData.D h)) (v 12)) (v 5))) (.mul (v 18) (v 7)))
        (.mul (.mul (c (2*(h-NaturalAxisData.D h))) (v 12)) (v 6))) (v 14)) (v 15)) (v 16))

def axialExpression (h : ℝ) : Expr :=
  .sub (.add (.add (.sub (c 0) (.mul (massExpression h) (v 1)))
    (.mul (.sub (.add (.mul (c (NaturalAxisData.D h)) (.sub (v 2) (.mul (v 12) (v 3))))
      (.mul (.mul (c (4*h)) (v 12)) (v 8))) (.mul (v 18) (v 9))) (v 14)))
    (.mul (.mul (c (4*NaturalAxisData.A h)) (v 12)) (v 10))) (.mul (v 18) (v 11))

/-- The four components are `Q_s,N_s,p_{s,1},p_{s,2}`. -/
def outputExpression (h : ℝ) : Fin 4 → Expr :=
  ![angularExpression h, axialExpression h,
    .mul (.mul (v 13) (v 17)) (angularExpression h),
    .mul (.mul (.mul (v 13) (v 17)) (v 16)) (axialExpression h)]

def stocks (h X : ℝ) (P₀ : ℝ → ℝ) (f : Curves) (i : Fin 4) : ℝ → ℝ :=
  (outputExpression h i).eval (basis h X (packet P₀ f))









/-- An arbitrary positive-radius comparison profile; no regular-axis representation is required. -/
structure Profile where
  E : (ℝ × ℝ) → ℝ
  U : (ℝ × ℝ) → ℝ

namespace Profile

def density (P : Profile) (i : Fin 5) (x η : ℝ) : ℝ :=
  ![P.U (x,η), Real.sqrt (2*x)*P.E (x,η),
    P.U (x,η)*(Real.sqrt (2*x)*P.E (x,η)),
    P.U (x,η)^2-P.E (x,η)^2/2, P.E (x,η)^2/(2*x)] i

/-- The manuscript's actual cumulative Lebesgue integrals `M,I,J,S,Cp`. -/
def history (P : Profile) (i : Fin 5) (X η : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..X, P.density i x η

def curves (P : Profile) (X : ℝ) : Curves :=
  ![(fun η => P.E (X,η)), (fun η => P.U (X,η)),
    P.history 0 X, P.history 1 X, P.history 2 X, P.history 3 X, P.history 4 X]

def outputs (P : Profile) (h : ℝ) (P₀ : ℝ → ℝ) (X : ℝ) : Fin 4 → ℝ → ℝ :=
  stocks h X P₀ (P.curves X)


def JetBound (P : Profile) (k : ℕ) (X₀ X₁ B : ℝ) : Prop :=
  ∀ X ∈ Icc X₀ X₁, ∀ i, Bound k (P.curves X i) B

end Profile











def historyDifference (P Q : Profile) (i : Fin 5) (X η : ℝ) : ℝ :=
  Q.history i X η-P.history i X η



end NavierStokes.SeedHandbackJets

import NavierStokes.ClosedIntervalCkOperators
import NavierStokes.MomentRepairPicard
import NavierStokes.QuadraticLinearization
import NavierStokes.SmoothQuadraticBranch

noncomputable section

namespace NavierStokes.ClosedIntervalMomentRepair

open Set Filter ClosedIntervalCk
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The printed smooth matrix, bilinear coefficient, and moment discrepancy. -/
structure Data (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  B : ℝ → E →L[ℝ] E
  A : ℝ → E →L[ℝ] E →L[ℝ] E
  d : ℝ → E
  hB : ContDiffOn ℝ ∞ B I
  hA : ContDiffOn ℝ ∞ A I
  hd : ContDiffOn ℝ ∞ d I
  invertible : ∀ x ∈ I, (B x).IsInvertible

namespace Data

variable (D : Data E)

def matrix (k : ℕ) : CK (E := E) k ≃L[ℝ] CK (E := E) k :=
  coefficientEquiv k D.B (D.hB.of_le (by simp)) D.invertible

def bilinearMap (k : ℕ) : CK (E := E) k →L[ℝ] CK (E := E) k →L[ℝ] CK (E := E) k :=
  quadraticOperator k D.A (D.hA.of_le (by simp))

def debt (k : ℕ) : CK (E := E) k := ofContDiffOn D.d (D.hd.of_le (by simp))

/-- The exact norm of multiplication by the inverse matrix on `C^k`. -/
def inverseNorm (k : ℕ) : ℝ := ‖(D.matrix k).symm.toContinuousLinearMap‖

/-- The exact norm of the actual bilinear coefficient operator on `C^k`. -/
def quadraticNorm (k : ℕ) : ℝ := ‖D.bilinearMap k‖

def debtNorm (k : ℕ) : ℝ := ‖D.debt k‖

def Small (k : ℕ) : Prop := 8 * D.inverseNorm k ^ 2 * D.quadraticNorm k * D.debtNorm k ≤ 1




@[simp] theorem matrix_value (k : ℕ) (f : CK (E := E) k) (x : I) :
    value k (D.matrix k f) x = D.B x (value k f x) :=
  coefficientOperator_value k D.B _ f x

@[simp] theorem bilinearMap_value (k : ℕ) (f g : CK (E := E) k) (x : I) :
    value k (D.bilinearMap k f g) x = D.A x (value k f x) (value k g x) :=
  quadraticOperator_value k D.A _ f g x

@[simp] theorem debt_value (k : ℕ) (x : I) : value k (D.debt k) x = D.d x := rfl











end Data
end NavierStokes.ClosedIntervalMomentRepair

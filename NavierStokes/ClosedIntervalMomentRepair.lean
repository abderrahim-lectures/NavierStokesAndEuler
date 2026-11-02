import NavierStokes.ClosedIntervalCkOperators
import NavierStokes.SmoothMomentRepair
import NavierStokes.QuadraticLinearization
import NavierStokes.SmoothQuadraticBranch


/-! Merged from `NavierStokes.MomentRepairPicard`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! Compatibility of the same quadratic correction in two Banach norms.
Both solutions are limits of the same zero-started Picard iterates. -/

/-! Merged from `NavierStokes.MomentRepairPicardConvergence`. The body is wrapped in a section so that its `open`s cannot leak into this file. -/
section

/-! # Convergence of the actual quadratic moment-repair iterates

The Banach fixed-point theorem is applied to the explicit correction iteration
on its invariant quantitative ball. The returned solution is the limit of
those iterates starting from zero.
-/

noncomputable section

open Set Function Filter
open scoped Topology NNReal

namespace NavierStokes.MomentRepairPicardConvergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


end NavierStokes.MomentRepairPicardConvergence


end


noncomputable section

open Filter Function
open scoped Topology

namespace NavierStokes.MomentRepairPicard

variable {E₀ Eₖ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [NormedAddCommGroup Eₖ] [NormedSpace ℝ Eₖ]







end NavierStokes.MomentRepairPicard


end

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

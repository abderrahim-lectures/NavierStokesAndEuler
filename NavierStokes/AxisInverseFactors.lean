import NavierStokes.AxisOperators

/-! Inserting undifferentiated factors inside the regular radial inverse. -/

noncomputable section

namespace NavierStokes.AxisInverseFactors

open Finset Finset.Nat Set AxisWeightEstimates AxisCoefficientSpace AxisOperators
open scoped BigOperators Topology BoundedContinuousFunction

private local instance (I : Window) (ε : ℝ) : NormedAddCommGroup (AxisSpace I ε) := inferInstance
private local instance (I : Window) (ε : ℝ) : NormedSpace ℝ (AxisSpace I ε) := inferInstance

def degreeMultiplier (r n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) + r - 1)

theorem degreeMultiplier_nonneg {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    0 ≤ degreeMultiplier r n := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hn : 0 ≤ (n : ℝ) := by positivity
  unfold degreeMultiplier
  exact mul_nonneg hn (by linarith)

theorem degreeMultiplier_mono {r : ℕ} (hr : 1 ≤ r) : Monotone (degreeMultiplier r) := by
  intro i n hin
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hi : 0 ≤ (i : ℝ) := by positivity
  have hn : (i : ℝ) ≤ n := by exact_mod_cast hin
  unfold degreeMultiplier
  nlinarith

theorem degreeMultiplier_pos {r n : ℕ} (hr : 1 ≤ r) (hn : 0 < n) :
    0 < degreeMultiplier r n := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold degreeMultiplier
  exact mul_pos hn' (by linarith)

@[simp] theorem degreeMultiplier_zero (r : ℕ) : degreeMultiplier r 0 = 0 := by
  simp [degreeMultiplier]

@[simp] theorem degreeMultiplier_succ (r n : ℕ) :
    degreeMultiplier r (n+1) = radialDivisor r n := by
  simp only [degreeMultiplier, radialDivisor, Nat.cast_add, Nat.cast_one]
  ring

/-- The harmless cutoff only makes the coefficient ratio bounded for
indices outside the convolution range. -/
def ratio (r n i : ℕ) : ℝ := degreeMultiplier r (min i n) / degreeMultiplier r n

theorem ratio_mem_Icc {r : ℕ} (hr : 1 ≤ r) (n i : ℕ) : ratio r n i ∈ Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg (degreeMultiplier_nonneg hr _) (degreeMultiplier_nonneg hr _), ?_⟩
  by_cases hn : n = 0
  · simp [ratio, hn]
  · exact (div_le_one (degreeMultiplier_pos hr (Nat.pos_of_ne_zero hn))).mpr
      (degreeMultiplier_mono hr (min_le_right _ _))


def insertFamily (I : Window) (ε : ℝ) (r : ℕ) (A B : AxisSpace I ε)
    (n m : ℕ) (x : ℝ) : ℝ :=
  jetProduct (fun i k => ratio r n i * inputJet I ε A i k x)
    (fun j l => inputJet I ε B j l x) n m

theorem insertFamily_continuous (I : Window) (ε : ℝ) (r : ℕ)
    (A B : AxisSpace I ε) (n m : ℕ) :
    ContinuousOn (insertFamily I ε r A B n m) I.interval := by
  change ContinuousOn (fun x => ∑ ij ∈ antidiagonal n,
    leibnizSum (fun k => ratio r n ij.1 * inputJet I ε A ij.1 k x)
      (fun l => inputJet I ε B ij.2 l x) m) I.interval
  apply continuousOn_finsetSum
  intro ij _
  apply continuousOn_leibnizSum I
  · intro k
    exact continuousOn_const.mul (continuous_jet I (weight ε) A.1 ij.1 k).continuousOn
  · intro k
    exact (continuous_jet I (weight ε) B.1 ij.2 k).continuousOn

theorem insertFamily_deriv (I : Window) (ε : ℝ) (r : ℕ)
    (A B : AxisSpace I ε) (n m : ℕ) (x : ℝ) (hx : x ∈ I.interval) :
    HasDerivWithinAt (insertFamily I ε r A B n m)
      (insertFamily I ε r A B n (m+1) x) I.interval x := by
  exact HasDerivWithinAt.fun_sum (u := antidiagonal n) (fun ij _ =>
    hasDerivWithinAt_leibnizSum I _ _
      (fun k y hy => (hasDerivWithinAt_jet I (weight ε) A ij.1 k hy).const_mul (ratio r n ij.1))
      (fun k y hy => hasDerivWithinAt_jet I (weight ε) B ij.2 k hy) m hx)

theorem insertFamily_bound (I : Window) {ε : ℝ} (hε : 0 < ε)
    {r : ℕ} (hr : 1 ≤ r) (A B : AxisSpace I ε) (n m : ℕ) (x : ℝ) :
    |insertFamily I ε r A B n m x| ≤ (64 * ‖A‖ * ‖B‖) * weight ε n m := by
  apply jetProduct_bound hε (norm_nonneg A) (norm_nonneg B)
  · intro i k
    rw [abs_mul, abs_of_nonneg (ratio_mem_Icc hr n i).1]
    exact (mul_le_mul_of_nonneg_left (inputJet_bound I hε A i k x)
      (ratio_mem_Icc hr n i).1).trans
      (mul_le_of_le_one_left (mul_nonneg (norm_nonneg A) (weight_pos hε i k).le)
        (ratio_mem_Icc hr n i).2)
  · intro j k
    exact inputJet_bound I hε B j k x

/-- The first argument is an already inverted source. The second is
inserted before that inverse, with one algebra constant. -/
def insert (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (A B : AxisSpace I ε) : AxisSpace I ε :=
  ofJetFamily I (weight ε) (weight_pos hε) (insertFamily I ε r A B)
    (insertFamily_continuous I ε r A B) (insertFamily_deriv I ε r A B)
    (64 * ‖A‖ * ‖B‖) (by positivity)
    (fun n m x _ => insertFamily_bound I hε hr A B n m x)

theorem norm_insert_le (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (A B : AxisSpace I ε) : ‖insert I hε r hr A B‖ ≤ 64 * ‖A‖ * ‖B‖ :=
  norm_ofJetFamily_le _ _ _ _ _ _ _ _ _




/-- Repeat insertion for any finite list of factors. -/
def insertFactors (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (A : AxisSpace I ε) : List (AxisSpace I ε) → AxisSpace I ε
  | [] => A
  | B :: Bs => insertFactors I hε r hr (insert I hε r hr A B) Bs








end NavierStokes.AxisInverseFactors

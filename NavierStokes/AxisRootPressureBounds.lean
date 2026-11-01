import NavierStokes.NaturalAxisRange

/-! # Pressure-scaled positivity at the actual natural-axis root -/

noncomputable section

namespace NavierStokes.AxisRootPressureBounds

open Set NaturalAxisData

/-- The root margin retains the square of the pressure-prefix amplitude. -/
theorem Z_at_root_pressure_lower {h j η B : ℝ} {P : ℝ → ℝ}
    (p : NaturalAxisRange.Parameters h j) (hB : 2 ≤ B)
    (hη : η ∈ Ioo (-j / 4) (-j / 5)) (hz : H h j η = 0)
    (hP : P η ≤ -(B ^ 2 / 4)) (hP' : deriv P η ≤ 0) :
    j * B ^ 2 / 20 < Z h j P η := by
  have hηn : η < 0 := by linarith [hη.2, p.j_pos]
  have hI : η ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hη.1, hη.2, p.j_pos, p.j_le]
  have hU : 0 < U j η := by dsimp [U]; linarith [hη.1]
  have hUj : U j η < j / 5 := by dsimp [U]; linarith [hη.2]
  have hrU : -η * U j η ≤ U j η := by
    simpa using mul_le_mul_of_nonneg_right (show -η ≤ 1 by linarith [hI.1]) hU.le
  have hfactor : 1 - 2 * η * U j η ≤ 2 := by nlinarith [p.j_le]
  have hadverse : (1 - 2 * η * U j η) * U j η < 2 * j / 5 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hfactor hU.le) (by linarith)
  have hBsq : (4 : ℝ) ≤ B ^ 2 := by nlinarith
  have hpressure := mul_le_mul_of_nonpos_left hP hηn.le
  have hroot := mul_lt_mul_of_pos_right hη.2 (show 0 < B ^ 2 by positivity)
  have hcore : j * B ^ 2 / 10 < -(1 - 2 * η * U j η) * U j η + 4 * η * P η := by
    have hjB := mul_le_mul_of_nonneg_left hBsq p.j_pos.le
    nlinarith
  have hderiv : d η * deriv P η ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (d_nonneg hI) hP'
  calc
    j * B ^ 2 / 20 ≤ A h * (j * B ^ 2 / 10) := by
      have hm := mul_nonneg (show 0 ≤ A h - 1 / 2 by
        linarith [(NaturalAxisRange.A_bounds p).1])
        (mul_nonneg p.j_pos.le (sq_nonneg B))
      nlinarith
    _ < A h * (-(1 - 2 * η * U j η) * U j η + 4 * η * P η) :=
      mul_lt_mul_of_pos_left hcore (NaturalAxisRange.A_pos p)
    _ ≤ Z h j P η := by
      unfold Z
      rw [hz]
      nlinarith


end NavierStokes.AxisRootPressureBounds

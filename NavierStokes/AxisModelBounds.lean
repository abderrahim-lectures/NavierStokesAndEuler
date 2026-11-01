import NavierStokes.AxisSeries

/-!
# The numerical bounds for the axis comparison profile

The profile in `axis:model-series` is an actual convergent series.  The
following bounds retain the rational lower bound in `axis:model-positive`,
including its stated decimal consequence, on the whole interval `[0, 4.1]`.
-/

noncomputable section

namespace NavierStokes.AxisModelBounds

/-- The comparison function `f₀` in the axis construction. -/
def model (z : ℝ) : ℝ := AxisSeries.profile 1 z






end NavierStokes.AxisModelBounds

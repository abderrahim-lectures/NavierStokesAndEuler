import Mathlib
import NavierStokes.ProblemStatement

/-!
# Coordinate and viscosity bridge to the periodic Clay statement

This module translates the project's physical differential operators to the
comparator's operators, and normalizes any positive viscosity to one. It uses
only the independent comparator definitions; no reference theorem is imported.
The application to the constructed candidate is in `ComparatorTheorem`.
-/
/-! Merged from `NavierStokes.ComparatorDefinitions` (in a section, so its `open`s cannot leak). -/
section
/-!
# Independent definitions for the Navier–Stokes Comparator submission

This is a copy of the definitions and helper lemmas in `NavierStokes.Comparator`,
without either challenge theorem or an import of the reference. The proof adapters
use this module so their import closure contains no reference placeholders.
Comparator checks these definitions against the independent reference at runtime.

Source:
https://github.com/google-deepmind/formal-conjectures/blob/8bf45ed70d48b2b2a501de9c00b26bfa38c573ee/FormalConjectures/Millenium/NavierStokes.lean
-/

open ContDiff Set InnerProductSpace MeasureTheory
open scoped Laplacian

namespace NavierStokes.Comparator

-- Inlined notation from FormalConjecturesForMathlib.Geometry.Euclidean and Geometry.«3d».
local notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

variable {n : ℕ}

/--
The divergence $\nabla \cdot v$ of a vector field $v : \mathbb{R}^n \to \mathbb{R}^n$
at a point $x$, computed as the trace of the Jacobian matrix.

In coordinates, $\nabla \cdot v = \sum_i \partial v_i / \partial x_i$.

This is available as the notation `∇⬝ v`. If `v` is not differentiable at `x`, then
`fderiv` is the zero map, so this definition has the corresponding junk value $0$.
-/
noncomputable
def divergence (v : ℝ^n → ℝ^n) (x : ℝ^n) : ℝ := (fderiv ℝ v x).trace ℝ (ℝ^n)

@[inherit_doc]
local notation "∇⬝" => divergence

/-- The divergence of a vector field is $0$ at points where `fderiv` has its junk value. -/
@[simp]
theorem divergence_of_not_differentiableAt {v : ℝ^n → ℝ^n} {x : ℝ^n}
    (hv : ¬ DifferentiableAt ℝ v x) : ∇⬝ v x = 0 := by
  simp [divergence, fderiv_zero_of_not_differentiableAt hv]

/-- The divergence of the zero vector field is zero. -/
@[simp]
theorem divergence_zero (x : ℝ^n) : ∇⬝ (0 : ℝ^n → ℝ^n) x = 0 := by
  simp [divergence]

/-- The divergence of a constant vector field is zero. -/
@[simp]
theorem divergence_const (c : ℝ^n) (x : ℝ^n) :
    ∇⬝ (fun _ : ℝ^n => c) x = 0 := by
  simp [divergence]

/-- Divergence is additive at points where both vector fields are differentiable. -/
theorem divergence_add {v w : ℝ^n → ℝ^n} {x : ℝ^n}
    (hv : DifferentiableAt ℝ v x) (hw : DifferentiableAt ℝ w x) :
    ∇⬝ (fun y => v y + w y) x = ∇⬝ v x + ∇⬝ w x := by
  rw [divergence, fderiv_fun_add hv hw]
  exact map_add _ _ _

/-- Divergence commutes with scalar multiplication at differentiability points. -/
theorem divergence_smul (c : ℝ) {v : ℝ^n → ℝ^n} {x : ℝ^n}
    (hv : DifferentiableAt ℝ v x) : ∇⬝ (fun y => c • v y) x = c * ∇⬝ v x := by
  rw [divergence, fderiv_fun_const_smul hv c]
  simp [divergence]

/--
A function $f : \mathbb{R}^n \to \alpha$ is 1-periodic if it is periodic in each
coordinate with period $1$, i.e. $f(x + e_i) = f(x)$ for each unit vector $e_i$.
This captures functions on the $n$-torus $\mathbb{R}^n/\mathbb{Z}^n$.
-/
def IsOnePeriodic {α : Sort*} (f : ℝ^n → α) : Prop :=
  ∀ x i, f (x + EuclideanSpace.single i 1) = f x

/--
Basic conditions on initial velocity field for the Navier-Stokes equations
in $n$-dimensional space.

The initial velocity must be:
- Divergence-free (incompressibility condition: $\nabla \cdot u_0 = 0$)
- Smooth ($C^\infty$)

These conditions apply regardless of spatial dimension.
-/
structure InitialVelocityCondition (u₀ : ℝ^n → ℝ^n) : Prop where
  /-- The initial velocity field is divergence-free (equation 2).
      This is the incompressibility constraint for the fluid. -/
  div_free : ∀ x, ∇⬝ u₀ x = 0
  /-- The initial velocity field is smooth ($C^\infty$ in all variables). -/
  smooth : ContDiff ℝ ∞ u₀

/--
Initial velocity conditions for the Navier-Stokes problem on all of $\mathbb{R}^n$.

In addition to being smooth and divergence-free, the velocity must decay
faster than any polynomial at spatial infinity (condition 4 in Fefferman's paper).

This condition ensures the velocity field has finite energy and reasonable
behavior as $\lVert x \rVert \to \infty$.
-/
structure InitialVelocityConditionDecay (u₀ : ℝ^n → ℝ^n) : Prop extends
    InitialVelocityCondition u₀ where
  /-- All derivatives of u₀ decay faster than any polynomial (condition 4).
  For any derivative order $m$ and any decay rate $K$, there exists a constant $C$
  such that $\lVert \partial^m u_0(x) \rVert \le C/(1+\lVert x \rVert)^K$. -/
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ m u₀ x‖ ≤ C / (1 + ‖x‖) ^ K

/--
Initial velocity conditions for the periodic Navier-Stokes problem on
$\mathbb{R}^n/\mathbb{Z}^n$.

The velocity must be smooth, divergence-free, and 1-periodic in each coordinate
(condition 8, part 1 in Fefferman's paper).
-/
structure InitialVelocityConditionPeriodic (u₀ : ℝ^n → ℝ^n) : Prop extends
    InitialVelocityCondition u₀ where
  /-- The initial velocity is 1-periodic in each direction (condition 8, part 1). -/
  isOnePeriodic : IsOnePeriodic u₀

/--
The basic smoothness condition on the external forcing term.

The force $f(x,t)$ must be smooth ($C^\infty$) in both space and time variables
for $t \ge 0$.
-/
structure ForceCondition (f : ℝ^n → ℝ → ℝ^n) : Prop where
  /-- The force is smooth on $\mathbb{R}^n \times [0,\infty)$. -/
  smooth : ContDiffOn ℝ ∞ (↿f) (Set.univ ×ˢ Set.Ici 0)

/--
Force conditions for the Navier-Stokes problem on all of $\mathbb{R}^n$.

The force must be smooth and decay faster than any polynomial
in both space and time (condition 5 in Fefferman's paper).
-/
structure ForceConditionDecay (f : ℝ^n → ℝ → ℝ^n) : Prop extends ForceCondition f where
  /-- All derivatives of f decay faster than any polynomial in space and time (condition 5).
  For any derivative order $m$ and any decay rate $K$, there exists $C$ such that
  $\lVert \partial^m_{x,t} f(x,t) \rVert \le C/(1+\lVert x \rVert+t)^K$ for
  $t \ge 0$. -/
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
    ‖iteratedFDerivWithin ℝ m (↿f) (Set.univ ×ˢ Set.Ici 0) (x, t)‖ ≤ C / (1 + ‖x‖ + t) ^ K

/--
Force conditions for the periodic Navier-Stokes problem on
$\mathbb{R}^n/\mathbb{Z}^n$.

The force must be smooth, 1-periodic in space, and decay in time
(conditions 8, part 1 and 9 in Fefferman's paper).
-/
structure ForceConditionPeriodic (f : ℝ^n → ℝ → ℝ^n) : Prop extends ForceCondition f where
  /-- The force is 1-periodic in space for all times $t \ge 0$ (condition 8, part 1). -/
  isOnePeriodic : ∀ t ≥ 0, IsOnePeriodic (f · t)
  /-- All derivatives of f decay faster than any polynomial in time (condition 9). -/
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
    ‖iteratedFDerivWithin ℝ m (↿f) (Set.univ ×ˢ Set.Ici 0) (x, t)‖ ≤ C / (1 + t) ^ K

/--
A solution (v, p) to the Navier-Stokes equations in n-dimensional space
with viscosity $\nu$, initial velocity $u_0$, and external force $f$.

This structure captures the core requirements for a solution:
1. The velocity and pressure satisfy the Navier-Stokes PDE (equation 1)
2. The velocity remains divergence-free for all time (equation 2)
3. The initial condition is satisfied (equation 3)
4. The solution is smooth ($C^\infty$) for all time $t \ge 0$ (equations 6, 11)
-/
structure NavierStokesExistenceAndSmoothness
    (nu : ℝ) (u₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v : ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) : Prop where
  /-- The Navier-Stokes equation (equation 1):
  $\partial v/\partial t + (v \cdot \nabla)v = \nu\Delta v - \nabla p + f$. -/
  navier_stokes : ∀ x, ∀ t ≥ 0,
    derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) =
      nu • Δ (v · t) x - gradient (p · t) x + f x t
  /-- Incompressibility constraint (equation 2): $\nabla \cdot v = 0$ for all
  $x$ and $t \ge 0$. -/
  div_free : ∀ x, ∀ t ≥ 0, ∇⬝ (v · t) x = 0
  /-- Initial condition (equation 3): $v(x,0) = u_0(x)$ for all $x$. -/
  initial_condition : ∀ x, v x 0 = u₀ x
  /-- The velocity field is smooth ($C^\infty$) on $\mathbb{R}^n \times [0,\infty)$
  (conditions 6, 11). -/
  velocity_smooth : ContDiffOn ℝ ∞ (↿v) (Set.univ ×ˢ Set.Ici 0)
  /-- The pressure field is smooth ($C^\infty$) on $\mathbb{R}^n \times [0,\infty)$
  (conditions 6, 11). -/
  pressure_smooth : ContDiffOn ℝ ∞ (↿p) (Set.univ ×ˢ Set.Ici 0)

/--
A solution to the Navier-Stokes equations on all of $\mathbb{R}^n$ with appropriate
decay and energy bounds.

In addition to the basic solution properties, we require:
- The velocity is in $L^2$ at each time $t \ge 0$ (finite kinetic energy)
- The total energy remains bounded for all time (condition 7)
-/
structure NavierStokesExistenceAndSmoothnessRn
    (nu : ℝ) (u₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v : ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) : Prop
  extends NavierStokesExistenceAndSmoothness nu u₀ f v p where
  /-- The velocity is square-integrable at each time $t \ge 0$ (condition 7). -/
  integrable : ∀ t ≥ 0, MemLp (‖v · t‖) 2
  /-- The kinetic energy $\int \lVert v(x,t) \rVert^2\,dx$ remains uniformly bounded
  for all time (condition 7), where the integral is the Lebesgue integral. -/
  globally_bounded_energy : ∃ E, ∀ t ≥ 0, (∫ x : ℝ^n, ‖v x t‖ ^ 2) < E

/--
A solution to the Navier-Stokes equations on the $n$-torus $\mathbb{R}^n/\mathbb{Z}^n$.

The velocity must be 1-periodic in each spatial direction for all times (condition 10).
The pressure is also required to be 1-periodic, following the errata appended to the
Clay problem statement.
-/
structure NavierStokesExistenceAndSmoothnessPeriodic
    (nu : ℝ) (u₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v : ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) : Prop
  extends NavierStokesExistenceAndSmoothness nu u₀ f v p where
  /-- The velocity is 1-periodic in space for all times $t \ge 0$ (condition 10). -/
  isOnePeriodic_velocity : ∀ t ≥ 0, IsOnePeriodic (v · t)
  /-- The pressure is 1-periodic in space for all times $t \ge 0$ (Clay errata). -/
  isOnePeriodic_pressure : ∀ t ≥ 0, IsOnePeriodic (p · t)

end NavierStokes.Comparator
end


noncomputable section

namespace NavierStokes.ComparatorBridge

open Set Function InnerProductSpace ProblemStatement
open scoped ContDiff Laplacian RealInnerProductSpace

/-- Change the argument order from `(time, space)` to `space, time`. -/
def toComparator {V : Type*} (f : SpaceTime → V) : Space → ℝ → V :=
  fun x t => f (t, x)

/-- Change the argument order from `space, time` to `(time, space)`. -/
def fromComparator {V : Type*} (f : Space → ℝ → V) : SpaceTime → V :=
  fun z => f z.2 z.1

theorem divergence_eq (v : VelocityField) (t : ℝ) (x : Space) :
    spatialDivergence v t x = Comparator.divergence (fun y => v (t, y)) x := by
  rw [Comparator.divergence, LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [spatialDivergence, spatialDerivative, coordinateVector,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

theorem gradient_eq (p : PressureField) (t : ℝ) (x : Space) :
    pressureGradient p t x = gradient (fun y => p (t, y)) x := by
  apply ext_inner_left_basis (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  intro i
  simp [pressureGradient, coordinateVector, EuclideanSpace.basisFun_apply,
    inner_gradient_right, EuclideanSpace.inner_single_left, Pi.single_apply]

theorem laplacian_eq (v : VelocityField) (t : ℝ) (x : Space)
    (hv : ContDiff ℝ 2 (fun y => v (t, y))) :
    spatialLaplacian v t x = Δ (fun y => v (t, y)) x := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [spatialLaplacian, spatialDerivative, EuclideanSpace.basisFun_apply,
    coordinateVector]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun y => v (t, y))) x :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem temporalDerivative_eq (v : VelocityField) {t : ℝ} (ht : 0 < t) (x : Space) :
    temporalDerivative v t x = derivWithin (fun s => v (s, x)) (Ici 0) t := by
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht)]
  rfl

/-- Time change and amplitude change for a spacetime field. -/
def rescale {V : Type*} [SMul ℝ V] (a c : ℝ) (f : SpaceTime → V) : SpaceTime → V :=
  fun z => a • f (c * z.1, z.2)


theorem rescale_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : SpaceTime → V} (hf : ContDiffOn ℝ ∞ f futureDomain)
    (a : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ContDiffOn ℝ ∞ (rescale a c f) futureDomain := by
  apply (hf.comp ((contDiff_fst.const_smul c).prodMk contDiff_snd).contDiffOn ?_).const_smul a
  intro z hz
  exact ⟨mul_nonneg hc hz.1, mem_univ _⟩



theorem fromComparator_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Space → ℝ → V} (hf : ContDiffOn ℝ ∞ (↿f) (univ ×ˢ Ici 0)) :
    ContDiffOn ℝ ∞ (fromComparator f) futureDomain := by
  exact hf.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
    (fun z hz => ⟨mem_univ _, hz.1⟩)

theorem toComparator_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : SpaceTime → V} (hf : ContDiffOn ℝ ∞ f futureDomain) :
    ContDiffOn ℝ ∞ (↿(toComparator f)) (univ ×ˢ Ici 0) := by
  exact hf.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
    (fun z hz => ⟨hz.2, mem_univ _⟩)

theorem toComparator_jet_norm (f : VelocityField) (m : ℕ) (x : Space)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖iteratedFDerivWithin ℝ m (↿(toComparator f)) (univ ×ˢ Ici 0) (x, t)‖ =
      ‖iteratedFDerivWithin ℝ m f futureDomain (t, x)‖ := by
  change ‖iteratedFDerivWithin ℝ m (fun z : Space × ℝ => f (z.2, z.1))
    (univ ×ˢ Ici 0) (x, t)‖ = _
  have hs : UniqueDiffOn ℝ futureDomain :=
    (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have he : (LinearIsometryEquiv.prodComm ℝ Space ℝ) ⁻¹' futureDomain = univ ×ˢ Ici 0 := by
    ext z
    simp [futureDomain, and_comm]
  simpa [he, Function.comp_def, Prod.swap] using
    (LinearIsometryEquiv.prodComm ℝ Space ℝ).norm_iteratedFDerivWithin_comp_right f hs
      (x := (x, t)) ⟨ht, mem_univ _⟩ m

/-- All real decay exponents follow from the nonnegative-exponent jet bounds. -/
theorem forceConditionPeriodic_of_decay {f : VelocityField}
    (hf : ContDiffOn ℝ ∞ f futureDomain)
    (hp : UnitSpatialPeriodsOn (Ici 0) f)
    (hd : ∀ m : ℕ, ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
        ‖iteratedFDerivWithin ℝ m f futureDomain (t, x)‖ ≤ C * (1 + t) ^ (-K)) :
    Comparator.ForceConditionPeriodic (toComparator f) := by
  refine ⟨⟨toComparator_smooth hf⟩, ?_, ?_⟩
  · intro t ht x i
    exact hp t ht x i
  · intro m K
    obtain ⟨C, hC, hb⟩ := hd m (max K 0) (le_max_right _ _)
    refine ⟨C, ?_⟩
    intro x t ht
    rw [toComparator_jet_norm f m x ht, div_eq_mul_inv,
      ← Real.rpow_neg (by linarith : 0 ≤ 1 + t)]
    exact (hb t ht x).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg (le_max_left _ _))) hC.le)

theorem zero_initial_condition :
    Comparator.InitialVelocityConditionPeriodic (fun _ : Space => (0 : Space)) := by
  refine ⟨⟨?_, contDiff_const⟩, ?_⟩
  · intro x
    exact Comparator.divergence_const 0 x
  · intro x i
    rfl

theorem rescale_spatialDerivative (a c : ℝ) (v : VelocityField) (t : ℝ) (x : Space) :
    spatialDerivative (rescale a c v) t x = a • spatialDerivative v (c * t) x := by
  exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) a) x

theorem rescale_divergence (a c : ℝ) (v : VelocityField) (t : ℝ) (x : Space) :
    spatialDivergence (rescale a c v) t x = a * spatialDivergence v (c * t) x := by
  simp [spatialDivergence, rescale_spatialDerivative, Finset.mul_sum]

theorem rescale_advection (a c : ℝ) (v : VelocityField) (t : ℝ) (x : Space) :
    advection (rescale a c v) t x = a ^ 2 • advection v (c * t) x := by
  simp [advection, rescale_spatialDerivative, rescale, smul_smul, pow_two]

theorem rescale_gradient (a c : ℝ) (p : PressureField) (t : ℝ) (x : Space) :
    pressureGradient (rescale a c p) t x = a • pressureGradient p (c * t) x := by
  unfold pressureGradient rescale
  simp only [← Pi.smul_def, fderiv_const_smul_field]
  simp [smul_smul, Finset.smul_sum]

theorem rescale_laplacian (a c : ℝ) (v : VelocityField) (t : ℝ) (x : Space) :
    spatialLaplacian (rescale a c v) t x = a • spatialLaplacian v (c * t) x := by
  simp only [spatialLaplacian, rescale_spatialDerivative, smul_apply]
  simp only [← Pi.smul_def, fderiv_const_smul_field]
  simp [Finset.smul_sum]

theorem rescale_temporalDerivative (a c : ℝ) (v : VelocityField) (t : ℝ) (x : Space)
    (hv : DifferentiableAt ℝ (fun s => v (s, x)) (c * t)) :
    temporalDerivative (rescale a c v) t x = (a * c) • temporalDerivative v (c * t) x := by
  have hd := (hv.hasDerivAt.scomp t ((hasDerivAt_id t).const_mul c)).const_smul a
  change deriv (fun s => a • v (c * s, x)) t =
    (a * c) • deriv (fun s => v (s, x)) (c * t)
  simpa only [Function.comp_def, Pi.smul_def, mul_one, smul_smul] using hd.deriv

theorem smooth_space_slice {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {v : SpaceTime → V} (hv : ContDiffOn ℝ ∞ v futureDomain)
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ∞ (fun x => v (t, x)) := by
  rw [← contDiffOn_univ]
  exact hv.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun _ _ => ⟨ht, mem_univ _⟩)


/-- The original project conventions for a global viscosity-one solution. -/
structure GlobalSolutionOne (f : VelocityField) (v : VelocityField) (p : PressureField) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ v futureDomain
  pressure_smooth : ContDiffOn ℝ ∞ p futureDomain
  velocity_periodic : UnitSpatialPeriodsOn (Ici 0) v
  pressure_periodic : UnitSpatialPeriodsOn (Ici 0) p
  initial_velocity : ∀ x : Space, v (0, x) = 0
  divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Space, spatialDivergence v t x = 0
  navier_stokes : ∀ t : ℝ, 0 < t → ∀ x : Space, navierStokesResidual v p t x = f (t, x)

theorem comparator_equation {ν : ℝ} {u₀ : Space → Space} {f v : Space → ℝ → Space}
    {p : Space → ℝ → ℝ}
    (h : Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν u₀ f v p)
    {t : ℝ} (ht : 0 < t) (x : Space) :
    temporalDerivative (fromComparator v) t x + advection (fromComparator v) t x -
      ν • spatialLaplacian (fromComparator v) t x +
      pressureGradient (fromComparator p) t x = f x t := by
  have hv := smooth_space_slice (fromComparator_smooth h.velocity_smooth) ht.le
  rw [temporalDerivative_eq _ ht, laplacian_eq _ _ _ (hv.of_le (by
    exact (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2).le)), gradient_eq]
  change derivWithin (v x) (Ici 0) t + fderiv ℝ (v · t) x (v x t) -
    ν • Δ (v · t) x + gradient (p · t) x = f x t
  rw [h.navier_stokes x t ht.le]
  abel


end NavierStokes.ComparatorBridge

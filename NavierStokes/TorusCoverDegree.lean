import NavierStokes.CommonCoverSolve
import NavierStokes.TorusCoverLattice

/-!
# Sheets of the integer torus cover

The actual map induced by `[[3,1],[1,5]]` has the lattice quotient as its
fiber. An injective native chart lifts to one disjoint chart per lattice class.
-/

noncomputable section

namespace NavierStokes.TorusCoverDegree

open Set Function TorusInverse SmoothFourierData TorusAverages CommonCoverSolve

/-- Real representatives of every point on the two-dimensional torus. -/
theorem quotientPoint_surjective : Surjective quotientPoint := by
  rintro ⟨x, y⟩
  refine Quotient.inductionOn' x (fun a => ?_)
  refine Quotient.inductionOn' y (fun b => ?_)
  exact ⟨(a, b), rfl⟩


theorem quotientPoint_sub (x y : Plane) :
    quotientPoint (x - y) = quotientPoint x - quotientPoint y := by
  ext <;> simp [quotientPoint]

/-- Equality on the torus is precisely translation by an integral vector. -/
theorem quotientPoint_eq_iff (x y : Plane) :
    quotientPoint x = quotientPoint y ↔ ∃ k : Frequency, x = y + latticePoint k := by
  constructor
  · intro h
    have hz : quotientPoint (x - y) = 0 := by rw [quotientPoint_sub, h, sub_self]
    have h1 : ((x.1 - y.1 : ℝ) : UnitAddCircle) = 0 := congrArg Prod.fst hz
    have h2 : ((x.2 - y.2 : ℝ) : UnitAddCircle) = 0 := congrArg Prod.snd hz
    obtain ⟨k1, hk1⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h1
    obtain ⟨k2, hk2⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h2
    refine ⟨(k1, k2), ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk1 hk2
    ext <;> dsimp [latticePoint] <;> linarith
  · rintro ⟨k, rfl⟩
    simpa [add_comm] using quotientPoint_lattice_add k y

theorem quotient_coverPower (d : ℕ) (x : Plane) :
    quotientPoint (coverPower d x) = torusCovering^[d] (quotientPoint x) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      change quotientPoint (coverEquiv (coverPower d x)) = _
      rw [coverEquiv_apply, SlotGeometry.cover_apply]
      change quotientPoint (covering (coverPower d x)) = _
      rw [quotient_covering, ih, Function.iterate_succ_apply']

/-- The explicit inverse chart based at the integral label `k`. -/
def rawLift (d : ℕ) (k : Frequency) (y : Plane) : Torus :=
  quotientPoint ((coverPower d).symm (y + latticePoint k))

theorem covering_rawLift (d : ℕ) (k : Frequency) (y : Plane) :
    torusCovering^[d] (rawLift d k y) = quotientPoint y := by
  rw [rawLift, ← quotient_coverPower, ContinuousLinearEquiv.apply_symm_apply]
  simpa [add_comm] using quotientPoint_lattice_add k y

/-- Integral deck translations give exactly the same inverse chart. -/
theorem rawLift_eq_iff (d : ℕ) (k l : Frequency) (y : Plane) :
    rawLift d k y = rawLift d l y ↔ ∃ n : Frequency, k = l + coverIndex d n := by
  rw [rawLift, rawLift, quotientPoint_eq_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, latticePoint_injective ?_⟩
    have heq := congrArg (coverPower d) hn
    simp only [map_add, ContinuousLinearEquiv.apply_symm_apply, coverPower_lattice] at heq
    rw [latticePoint_add]
    exact add_left_cancel (by simpa only [add_assoc] using heq)
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    rw [latticePoint_add, ← coverPower_lattice, ← add_assoc, map_add,
      ContinuousLinearEquiv.symm_apply_apply]

/-- Every point over a real native point belongs to one integral inverse chart. -/
theorem covering_eq_iff_rawLift (d : ℕ) (p : Torus) (y : Plane) :
    torusCovering^[d] p = quotientPoint y ↔ ∃ k : Frequency, p = rawLift d k y := by
  constructor
  · intro hp
    obtain ⟨x, rfl⟩ := quotientPoint_surjective p
    rw [← quotient_coverPower, quotientPoint_eq_iff] at hp
    obtain ⟨k, hk⟩ := hp
    exact ⟨k, congrArg quotientPoint ((coverPower d).eq_symm_apply.mpr hk)⟩
  · rintro ⟨k, rfl⟩
    exact covering_rawLift d k y




/-- The explicit sheet is the copy-point formula used by the common-cover
ODE construction, with the same center and native basis. -/
theorem rawLift_geometry_point (g : Geometry) (k : Frequency) (z : Plane) :
    rawLift g.gap k (g.center + g.basis z) = quotientPoint (g.point k z) := by
  unfold rawLift Geometry.point
  congr 2
  abel

/-- The original native parameter rectangle. -/
def nativeRectangle (g : Geometry) (r : ℝ) : Set Torus :=
  (fun z => quotientPoint (g.center + g.basis z)) '' Metric.ball (0 : Plane) r

/-- One of the inverse parallelograms displayed in the manuscript. -/
def liftedRectangle (g : Geometry) (r : ℝ) (k : Frequency) : Set Torus :=
  (fun z => quotientPoint (g.point k z)) '' Metric.ball (0 : Plane) r

theorem liftedRectangle_eq_rawLift (g : Geometry) (r : ℝ) (k : Frequency) :
    liftedRectangle g r k = rawLift g.gap k ''
      ((fun z => g.center + g.basis z) '' Metric.ball (0 : Plane) r) := by
  rw [Set.image_image]
  unfold liftedRectangle
  congr 1
  funext z
  exact (rawLift_geometry_point g k z).symm



open TorusCoverLattice

/-- One inverse chart for each class in the actual covering lattice. -/
def sheetLift (d : ℕ) (i : Sheet d) (y : Plane) : Torus :=
  Quotient.lift (fun k => rawLift d k y)
    (fun k l h => (rawLift_eq_iff d k l y).mpr
      ((sheet_eq_iff d k l).mp (Quotient.sound h))) i

@[simp] theorem sheetLift_mk (d : ℕ) (k : Frequency) (y : Plane) :
    sheetLift d (QuotientAddGroup.mk k) y = rawLift d k y := rfl

theorem covering_sheetLift (d : ℕ) (i : Sheet d) (y : Plane) :
    torusCovering^[d] (sheetLift d i y) = quotientPoint y := by
  induction i using Quotient.inductionOn with | h k => exact covering_rawLift d k y

theorem sheetLift_injective (d : ℕ) (y : Plane) :
    Injective (fun i : Sheet d => sheetLift d i y) := by
  intro i j
  induction i, j using Quotient.inductionOn₂ with
  | h k l =>
      intro h
      exact (sheet_eq_iff d k l).mpr ((rawLift_eq_iff d k l y).mp h)

/-- Every point of every fiber occurs once, with no duplicated lattice labels. -/
def fiberEquiv (d : ℕ) (y : Plane) :
    Sheet d ≃ {p : Torus // torusCovering^[d] p = quotientPoint y} :=
  Equiv.ofBijective (fun i => ⟨sheetLift d i y, covering_sheetLift d i y⟩) (by
    constructor
    · intro i j h
      exact sheetLift_injective d y (congrArg Subtype.val h)
    · rintro ⟨p, hp⟩
      obtain ⟨k, hk⟩ := (covering_eq_iff_rawLift d p y).mp hp
      exact ⟨QuotientAddGroup.mk k, Subtype.ext hk.symm⟩)


/-- A native rectangle lifted on the sheet indexed by a lattice class. -/
def sheetRectangle (g : Geometry) (r : ℝ) (i : Sheet g.gap) : Set Torus :=
  sheetLift g.gap i '' ((fun z => g.center + g.basis z) '' Metric.ball (0 : Plane) r)

@[simp] theorem sheetRectangle_mk (g : Geometry) (r : ℝ) (k : Frequency) :
    sheetRectangle g r (QuotientAddGroup.mk k) = liftedRectangle g r k :=
  (liftedRectangle_eq_rawLift g r k).symm










end NavierStokes.TorusCoverDegree

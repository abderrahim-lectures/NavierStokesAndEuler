import NavierStokes.ParticularWaveBounds

/-!
# A single deck shift of the actual particular solve

Only invariance under the specified lattice vector is assumed.  Equality of
the actual anchored coefficient and forcing paths gives equality of the
Volterra solves, and a bijective copy reindexing gives the same symmetry of
the periodized velocity and pressure.
-/

noncomputable section

namespace NavierStokes.SubcoverPeriodicity

open Set Function CommonCoverSolve TorusInverse HarmonicCalculus ParticularWaveBounds
open scoped Topology BigOperators

section LinearSolve

variable {P V E : Type}
variable [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]



variable [CompleteSpace E]



end LinearSolve

section ParticularCopies

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]







end ParticularCopies

section PeriodizedCopies

variable {P H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]


end PeriodizedCopies

section CommonFields

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]




end CommonFields

/-! ## The inherited sublattice, without a unit-lattice assertion -/

/-- Periodicity on the image of the integer lattice under the d-fold
cover. The parameter is fixed throughout the statement. -/
def SubcoverPeriodicAt {P V : Type} (d : ℕ) (f : P × Plane → V) (p : P) : Prop :=
  ∀ Y : Plane, ∀ k : Frequency,
    f (p, Y + TorusAverages.latticePoint (coverIndex d k)) = f (p,Y)

/-- The actual inverse-cover pullback of a source. -/
noncomputable def inverseCoverSource {P V : Type} (d : ℕ) (f : P × Plane → V) : P × Plane → V :=
  fun x => f (x.1, (coverPower d).symm x.2)




section SubcoverFields

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]







end SubcoverFields

end NavierStokes.SubcoverPeriodicity

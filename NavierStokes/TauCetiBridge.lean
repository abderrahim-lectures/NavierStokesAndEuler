import TauCeti.Analysis.Calculus.ParametricIntegral

/-!
# Bridge to TauCeti

This module is the single point at which the repository depends on
[TauCeti](https://github.com/TauCetiProject/TauCeti), the downstream analysis library.
It exists so that the dependency is explicit, versioned and checkable, and so that the
mapping between project-local analysis gadgets and their library counterparts is recorded
in Lean rather than only in prose.

## What TauCeti supplies here

* `TauCeti.contDiff_intervalIntegral` and `TauCeti.iteratedFDeriv_intervalIntegral`
  (in `TauCeti.Analysis.Calculus.ParametricIntegral`) give the all-orders differentiation
  of an interval integral of a family that is `C^N` for every fixed `N`, with measurable
  and uniformly integrable derivative bounds. This is a strict generalisation of
  `EulerCompactParameterIntegral.integral_contDiff`, which is the project-local proof of
  the `C^∞` case for a jointly smooth integrand on `[a,b]`. The alias below records the
  identification at the level of statements.
* `TauCeti/Analysis/Sobolev/Mollification` gives the mollification identity for weak
  derivatives; the project's `Euler/OrdinaryMollifier.lean` builds an `L²`-valued
  convolution from Mathlib's `ContDiffBump` instead, and is not yet replaced.
* `TauCeti/Analysis/PDE/HeatKernel` is the natural home for the exterior swirl heat
  propagator of the Navier--Stokes construction (`NavierStokes/R3/HeatKernel.lean` here).

The full replacement plan, including the parts that are *not* replaceable without
changing the meaning of the objects (the word-lattice Sobolev spaces and the weighted
band classes of the construction), is in `MIGRATION.md` and in Section 6 of
`paper/main.tex`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Interval

namespace NavierStokes.TauCetiBridge

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The all-orders regularity theorem of TauCeti for interval integrals, restated at the
project's names so that downstream modules can depend on one local name. -/
theorem contDiff_intervalIntegral
    {μ : Measure ℝ} {u : ℝ → E → F} {a b : ℝ} {N : ℕ}
    (hu : ∀ᵐ s ∂μ.restrict (Ι a b), ContDiff ℝ N (u s))
    (hmeas : ∀ k ≤ N, ∀ x,
      AEStronglyMeasurable (fun s => iteratedFDeriv ℝ k (u s) x) (μ.restrict (Ι a b)))
    {bound : ℕ → ℝ → ℝ} (hb : ∀ k ≤ N, IntervalIntegrable (bound k) μ a b)
    (hub : ∀ k ≤ N, ∀ᵐ s ∂μ.restrict (Ι a b), ∀ x,
      ‖iteratedFDeriv ℝ k (u s) x‖ ≤ bound k s) :
    ContDiff ℝ N fun x => ∫ s in a..b, u s x ∂μ :=
  TauCeti.contDiff_intervalIntegral hu hmeas hb hub

/-- The corresponding identification of every integrated jet with the integral of the jet,
also from TauCeti. This is the form in which the Euler development uses differentiation
under the integral sign. -/
theorem iteratedFDeriv_intervalIntegral
    {μ : Measure ℝ} {u : ℝ → E → F} {a b : ℝ} {N : ℕ}
    (hu : ∀ᵐ s ∂μ.restrict (Ι a b), ContDiff ℝ N (u s))
    (hmeas : ∀ k ≤ N, ∀ x,
      AEStronglyMeasurable (fun s => iteratedFDeriv ℝ k (u s) x) (μ.restrict (Ι a b)))
    {bound : ℕ → ℝ → ℝ} (hb : ∀ k ≤ N, IntervalIntegrable (bound k) μ a b)
    (hub : ∀ k ≤ N, ∀ᵐ s ∂μ.restrict (Ι a b), ∀ x,
      ‖iteratedFDeriv ℝ k (u s) x‖ ≤ bound k s)
    {k : ℕ} (hk : k ≤ N) :
    iteratedFDeriv ℝ k (fun x => ∫ s in a..b, u s x ∂μ) =
      fun x => ∫ s in a..b, iteratedFDeriv ℝ k (u s) x ∂μ :=
  TauCeti.iteratedFDeriv_intervalIntegral hu hmeas hb hub hk

end NavierStokes.TauCetiBridge

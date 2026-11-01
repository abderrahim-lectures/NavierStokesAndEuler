# Migration to Lean v4.36.0-rc1, Mathlib 2cabef97 and TauCeti

This document records the migration of the repository from its original pin
(Lean `v4.34.0-rc2`) to the current library generation, and what the move broke.

## The new pin

| component | before | after |
|---|---|---|
| Lean | `leanprover/lean4:v4.34.0-rc2` | `leanprover/lean4:v4.36.0-rc1` |
| Mathlib | `v4.34.0-rc2` | `2cabef97b63d3275776b8b060d802de6a6fa1055` |
| TauCeti | — | `b8cbc774e9a48bd8e6d4b99d99354e6ae7505b7d` |
| Comparator | `v4.34.0-rc2` | removed from the dependency set |

Both `rev` fields are full commit hashes, so `lake update` is deterministic.

### Why this pin

TauCeti pins a toolchain and a Mathlib commit, and Lake requires the root package and its
dependencies to agree on the toolchain. At the time of the migration:

* TauCeti `main` is on Lean `v4.36.0-rc1` with Mathlib `2cabef97…`;
* the newest Mathlib release is `v4.36.0-rc2`, whose toolchain no TauCeti revision uses;
* Comparator is released per toolchain and its tags stop at `v4.35.0`.

We therefore took the newest TauCeti and the newest Mathlib that TauCeti supports.

### Why Comparator was removed

Comparator only supplies `lake exe comparator`, used to re-check the four headline
theorems through an independent kernel. Its releases stop one toolchain below what TauCeti
requires, so keeping it would have forced the whole project down to `v4.35.0`. Since it is
a checking tool and not part of any proof, it was dropped from `lakefile.toml`.

The challenge modules themselves are unchanged and still import only Mathlib, so
independent checking remains possible with a Comparator installation matching whatever
toolchain is in use:

```sh
lake exe cache get
lake exe comparator ComparatorChallenges/NavierStokes.json
lake exe comparator ComparatorChallenges/Euler.json
```

## What broke, and why

The failures are overwhelmingly in the `L^p`/`eLpNorm` API of Mathlib. Three kinds:

1. **`MemLp` became a definition.** `MemLp f p μ` is now *defined* as
   `eLpNorm f p μ < ∞`, not a structure. Field projections `hf.1`, `hf.2` must become the
   lemmas `hf.aestronglyMeasurable` and `hf.eLpNorm_lt_top`, and anonymous-constructor
   terms `⟨hmeas, hfin⟩` must become the finiteness proof alone.

2. **Measurability hypotheses moved in both directions.** `eLpNorm` is now `∞` (rather
   than `0`) on non-a.e.-strongly-measurable functions. Hence
   `eLpNorm_mono_ae` and `eLpNorm_one_eq_lintegral_enorm` gained explicit measurability
   hypotheses, while `eLpNorm_add_le` lost its two measurability arguments. One project
   lemma, `NavierStokesR3.LpNormTools.lpNorm_mono_of_norm_le_ae`, is *false* without an
   extra measurability hypothesis under the new convention and now proves the
   non-measurable case by a case split (where `eLpNorm = ∞`, so `toReal = 0`).

3. **Explicit exponent hypotheses became a structure.**
   `eLpNorm'_le_eLpNorm'_mul_eLpNorm'` now takes a single `Real.HolderTriple p q r`
   instead of separate hypotheses, and its measurability arguments moved to the middle of
   the argument list.

Two further, smaller classes:

4. **Arguments became implicit.** `contDiff_apply` took the order explicitly and now takes
   it implicitly; `norm_iteratedFDeriv_fderiv` reoriented its statement, so applications
   need an explicitly typed `have`.

5. **Typeclass requirements changed.** `Finset.prod_le_prod` now needs a `MulLeftMono`
   instance, which `ℝ` does not have; monotonicity of a product of the form
   `∏ k, (b + k)` must be reproved from positivity of the factors.

## Module-system warnings

Lean 4.36's module system makes Mathlib and TauCeti emit, for every import from a file that
does not start with `module`:

```
warning: NavierStokes/R3/ComparisonGronwall.lean: imports
  `Mathlib.Analysis.Calculus.Deriv.MeanValue` from package `mathlib`, which is designed for
  use with the module system; consider adding `module` to the start of this file
```

These are warnings, not errors. A `module` file cannot import a non-`module` file, so
adopting the header is all-or-nothing across the tree; see the note at the end of this file.

## How to reproduce

```sh
lake update            # resolves the pins above; Mathlib's cache is fetched automatically
lake build             # builds NavierStokes, Euler and ComparatorChallenges
lake build NavierStokes.R3.Theorem     # a single target
```

Mathlib's prebuilt oleans make the first step a download (about 4.8 GB of build artifacts)
rather than a three-hour compile; the project's own 644k lines are then elaborated from
source.

## Where TauCeti is used

TauCeti is a first-class dependency. The parts of this repository that can be expressed in
its API are catalogued in `paper/sec6-libraries.tex`; the module
`NavierStokes/TauCetiBridge.lean` imports the relevant TauCeti modules and records, in one
place, which project-local gadgets they replace.

## Measuring duplication against the libraries

`scripts/DuplicateProbe.lean` finds theorems whose statements agree with another theorem of
the environment (Mathlib, TauCeti, Lean, Std or this repository) up to binder order, binder
information and universe levels. It vendors the core of `Mathlib.Tactic.DuplicateDecls`,
whose declarations are not `public` under the module system. `scripts/PlantedControls.lean`
supplies two deliberate duplicates so that a "no duplicates" report can be distinguished
from a broken probe.

Sample result (22 modules, 944 project theorems scanned): 2,401 duplicate groups in the
environment, **none** involving this repository once the planted controls are removed. The
duplication that does exist is conceptual — eighteen infrastructure files rebuilding
mollification, cutoffs, Sobolev spaces and parametric integration in project-specific form —
and is catalogued in Section 6 of `paper/main.tex`.

## Dead code removed

Reachability analysis from the six entry points (`NavierStokes.lean`, `Euler.lean`,
`Euler/Solution.lean`, `ComparatorChallenges/NavierStokes.lean`,
`ComparatorChallenges/Euler.lean`, and `NavierStokes/TauCetiBridge.lean`) leaves 75 modules
that no entry point reaches. **74 of them were deleted in this migration** (the 75th,
`NavierStokes/TauCetiBridge.lean`, is kept: it is the TauCeti bridge and is deliberately a
leaf).

| | files | lines |
|---|---|---|
| before | 2,659 | 643,986 |
| removed | 74 | 26,089 |
| after | 2,588 | 614,948 |

4.0% of the tree. The removed set is:

* eleven `*NoOptions*` modules — verbatim copies of existing modules placed in a separate
  namespace so that a heartbeat-heavy proof could be re-elaborated under different limits
  (7,032 lines). They document an investigation, not a result;
* two `*Investigation` modules;
* the rest are fragments of earlier versions of the construction that no lemma depends on.

The deletion is safe by construction: no remaining file imports any of them (checked after
removal: 0 dangling imports), so no reachable declaration changed. It is also one command
away from being undone:

```sh
git revert <this-commit>          # or: git checkout HEAD~1 -- <paths>
```

Nothing else in the repository was deleted, and no `.lean` file was edited by this step.

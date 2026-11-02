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
rather than a three-hour compile; the project's own 540k lines are then elaborated from
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

Sample result (22 modules, 802 project theorems scanned): 1,533 duplicate groups in the
environment, **none** involving this repository once the planted controls are removed. (The
same sample scanned 944 theorems and 2,401 groups before the unused-lemma removal below; the
last number is the one that matters and it was zero both times.) The
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

## Unused lemmas removed

The second reduction pass deletes `theorem`s and `lemma`s that nothing names.
`scripts/PruneUnusedLemmas.py` counts, for every declaration, how many times its
name occurs in the library; if the answer is one — the declaration itself — and
the declaration carries no attribute, its whole span goes: docstring,
`omit`/`include`/`variable`/`open … in` prefix, and body.

| | lines before | lines after | `theorem`/`lemma` before | after |
|---|---|---|---|---|
| `NavierStokes` | 404,716 | 344,369 | 25,733 | 20,651 |
| `Euler` | 210,317 | 196,721 | 11,218 | 9,970 |
| total | 615,033 | 541,090 | 36,951 | 30,621 |

12.0% of the two libraries, in three commits, one of which is the first pass and
two of which carry the fixed point.

### Why it is safe, and what the safety actually consists of

A declaration whose name occurs nowhere else is referenced by nothing, so
deleting it cannot change any remaining declaration. Everything else is tool
hygiene, and each item below cost a build to find:

* **One pass is not a fixed point.** Deleting a lemma can remove the last
  reference to another. The tool iterates: on `NavierStokes` the first pass
  removes 2,720 theorems and the fixed point removes 5,082.
* **The paper protects its own content.** A lemma that nothing uses is not
  necessarily dead: a standalone theorem stating a result is the point of a
  formalization, and it is what the paper cites. The name criterion alone
  deleted all eighteen theorems of `NavierStokes/AppendixHeatResults.lean` (the
  endpoint jets of the gamma integral) and `theorem_1_1_with_dissipation`, a
  variant of the headline theorem that `paper/sec2-results.tex` quotes. The tool
  takes `--keep` with a list of names --- every name the paper cites, every
  declaration of the eighteen infrastructure files and of the statement layer,
  435 names in all --- and costs 926 lines of the reduction.
* **Attributes are excluded.** A lemma used only through `@[simp]` is never
  named by its user, and `attribute [...]` lower down a file is a use a naive
  count will not associate with the declaration. Any attributed declaration is
  kept.
* **Indented declarations.** `NavierStokes/PositiveAxisSystem.lean` indents nine
  of its theorems by one space. A span that does not stop at them swallows the
  following declaration; the build then reports unknown identifiers far from the
  edit. `scripts/PruneUnusedLemmas.py` stops at indented declarations and
  refuses any span that contains a second declaration.
* **Prefixes can be multi-line.** An `omit`/`include`/`variable` block may run
  over several lines, and a deletion that misses one leaves a prefix with no
  command after it — `end Foo` then reports *the current section is unnamed*.
  Orphaned prefixes (and `open X in`, which is a prefix too) are removed by the
  same tool.
* **Docstrings are prose.** One of them contains the sentence *"theorem makes
  no assertion of cancellation on every normalized band"*, which reads as a
  declaration unless comment blocks are masked.

### What each library is checked against

`NavierStokes` elaborates, so the deletion is checked by the build: 19,645 jobs,
816 modules, 0 errors, and `#print axioms` on the six headline statements still
gives `[propext, Classical.choice, Quot.sound]`.

`Euler` does not elaborate. Two modules fail — `Euler/EulerProof.lean` (28
sites) and `Euler/GevreyComposition.lean` (1) — and Lake skips rather than
attempts the 1,795 modules that import them, so 42 of the 1,839 modules produce
an object file. Compilation therefore says little, and three other checks are
used:

1. the name criterion above;
2. `scripts/CheckPureDeletion.py`, which verifies against a commit that every
   change is a *pure deletion of whole blocks* — 797 blocks, 13,596 lines, each
   block starting on a declaration boundary and bracket-balanced, no line edited
   or inserted;
3. a diff of the build's error set before and after, which is **identical**: the
   same 29 sites, in the same categories, in the same two modules.

### What was deliberately not deleted

`Euler/EulerProof.lean` and `Euler/GevreyComposition.lean` are excluded from the
prune. Pruning them was tried first and removed 3,963 lines from `EulerProof.lean`
alone — including three of its 29 error sites, because a lemma whose proof fails
and which nothing references satisfies the criterion too. That would have shrunk
the documented gap by deleting the work that constitutes it, so both files are
kept byte for byte.

### Reproducing and undoing

```sh
python3 scripts/MeasureSize.py NavierStokes Euler          # the counts above
python3 scripts/PruneUnusedLemmas.py --dry NavierStokes    # report only
python3 scripts/PruneUnusedLemmas.py --exclude Euler/EulerProof.lean,Euler/GevreyComposition.lean \
        --also NavierStokes.lean,ComparatorChallenges,scripts Euler
PRUNE_BASE=<commit> python3 scripts/CheckPureDeletion.py Euler
```

Each step is one `git revert` away; the removed text is in the commits, not
discarded.

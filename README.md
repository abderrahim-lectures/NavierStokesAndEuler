# Finite time blowup for Navier–Stokes and Euler equations

This repository contains Lean 4 formalizations of the results presented in
“[Finite time blowup for Navier–Stokes](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf)” and
“[Finite time blowup for the Euler equation](https://cdn.openai.com/pdf/315b36cd-ec98-4023-8342-93345194ece1/euler.pdf)” by OpenAI.

- [Read the blog post](https://openai.com/index/navier-stokes-solution/)
- [Read the Navier-Stokes paper](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf)
- [Read the Euler paper](https://cdn.openai.com/pdf/315b36cd-ec98-4023-8342-93345194ece1/euler.pdf)

## Navier Stokes

For every positive viscosity, we prove two results:

- **Whole space $\mathbb{R}^3$:** There exist smooth initial data and forcing for
  which no global smooth solution with uniformly bounded kinetic energy exists.
- **Periodic torus $\mathbb{R}^3/\mathbb{Z}^3$:** There exist smooth periodic
  initial data and forcing for which no global smooth solution exists.

These are alternatives [**(C)**](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf#page=2) “Breakdown of Navier–Stokes solutions on ℝ³”
and [**(D)**](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf#page=2) “Breakdown of Navier–Stokes Solutions on ℝ³/ℤ³”
in the Clay Mathematics Institute’s [official problem description](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf)
of the [Navier–Stokes existence and smoothness](https://www.claymath.org/millennium/navier-stokes-equation/)
[Millennium Prize Problem](https://www.claymath.org/millennium-problems/).

## Euler

We construct smooth, compactly supported, divergence-free initial velocity on
$\mathbb{R}^3$ whose solution to the unforced incompressible Euler equations
develops a singularity in finite time. The velocity’s $C^1$ norm becomes unbounded
near that time, and the time integral of the vorticity’s $L^\infty$ norm diverges.

## Building the formalizations

The project uses Lean 4.36.0-rc1, [Mathlib](https://github.com/leanprover-community/mathlib4)
at `2cabef97` and [TauCeti](https://github.com/TauCetiProject/TauCeti) at `b8cbc77`.
With [elan](https://github.com/leanprover/elan) installed, fetch the Mathlib cache and build:

```sh
lake update          # resolves the pins; Mathlib's prebuilt oleans are fetched for you
lake build NavierStokes        # green: 816 modules, 19,645 jobs
lake build ComparatorChallenges # green: the two challenge modules
lake build Euler               # does not build yet; see below
```

Both pins are full commit hashes, so the resolution is deterministic.

**Migration status.** The repository was written against Lean `v4.34.0-rc2` and has been
moved to the pins above. `NavierStokes` and `ComparatorChallenges` build; `Euler` does not:
`Euler/EulerProof.lean` rejects 28 sites and `Euler/GevreyComposition.lean` one, so 42 of
its 1,839 modules produce an object file and the 1,795 that import the two failures are not
attempted. Those 29 are the visible part only: with them replaced by `sorry` the build runs
on and reports 61 further errors in eleven modules, then 42 more, then 31 (see
[MIGRATION.md](MIGRATION.md)). Five of the 29 are not syntax: they apply `eLpNorm_le_mul_eLpNorm_of_ae_le_mul` to an iterated field
derivative with no measurability hypothesis, which the old Mathlib did not need — `eLpNorm`
was `0` on non-a.e.-strongly-measurable functions and is now `∞`. Closing them requires a
measurability lemma the development never had. The full record is in
[MIGRATION.md](MIGRATION.md).

The four headline theorems are unaffected: `lake build NavierStokes` typechecks them, and
`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for each.

**Size.** Three reduction steps are recorded in [MIGRATION.md](MIGRATION.md): 74 unreachable
modules (26,089 lines) were deleted, 6,330 unreachable `theorem`/`lemma` declarations
(73,943 lines) were pruned, and 89 modules that exactly one file imported were folded into
that file (`NavierStokes` 753 -> 504). The two libraries now stand at 538,303 lines and
30,533 theorem/lemma declarations in 2,335 files. Library substitution is the third step and it is
small: three `Real.image_exp_*` restatements and one TauCeti replacement
(`SchwartzMap.dense_hasCompactSupport` for a 235-line reconstruction). The pruning is
checked by a build on `NavierStokes`, by a diff of `Euler`'s failure set (unchanged), and,
for the merges, by a before/after dump of the type of every declaration.

## Paper

A paper describing the formalization, its statement audit and the library migration is in
[`paper/`](paper/main.tex). Build it with:

```sh
cd paper && latexmk -xelatex main.tex
```

## Independent proof checking

For instructions on checking the formalizations with Comparator, see the
[ComparatorChallenges README](ComparatorChallenges/README.md).

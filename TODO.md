# TODO

Ordered so that each item is easier than the one below it. Every item ends with
`lake build NavierStokes` green and a commit; nothing is reported done on a build
that fails. Measurements quoted are from this branch and are reproducible with the
script named beside them.

## Done

* **1 (prune)**: nothing to delete — already at its fixed point.
* **2 (merge)**: nothing to merge — already at its fixed point.
* **3 (collapse collapsible duplicates)**: applied and verified; the remaining
  blocked groups are item 4.
* **5 (unused imports)**: analysed, **blocked**. `scripts/UnusedImports.py` tests
  each import by elaborating that file alone: of 124 files scanned it finds **455
  redundant imports**. Applying them breaks the build at **286 sites in 7 files**,
  because removing an import from `F` also removes it from everything that imports
  `F` and was getting it transitively. Restricting to files nothing imports is
  vacuous — every one of the 124 has an importer. The mechanical version is
  therefore: remove from `F` *and* add the same import to each importer of `F` that
  breaks. That is a per-importer rewrite, not a sweep, and it is not obviously a
  win (it can move an import from one file to five).

## 1. Re-run the unused-declaration prune (mechanical)

The definition-dedupe changed bodies, which can orphan declarations. The prune is
idempotent by construction, so this is one command:

    python3 scripts/PruneUnusedLemmas.py --kinds theorem,lemma,def,abbrev \
        --keep .scratch/keep-names.txt --also Euler.lean,ComparatorChallenges,scripts NavierStokes

Gate: build green; `#print axioms` unchanged on the eight quoted statements.

## 2. Re-run the module merge (mechanical)

Same reason: a smaller body can make a module single-use. Threshold 600, the two
excluded parents kept:

    python3 scripts/MergeModules.py --max-lines 600 --keep .scratch/keep-modules.txt \
        --skip-parent NavierStokes/PaperAdditionalResults.lean,NavierStokes/PaperResults.lean NavierStokes

Gate: build green; type dump diff shows no changed statement
(`scripts/DumpTypes.lean`).

## 3. Collapse the duplicate definitions that are in dependency order (mechanical)

`scripts/DuplicateDefs.lean` finds 131 groups (70 type abbreviations, 61 with a
value). Seven are already collapsed. Of the rest, the ones whose canonical name is
importable by the duplicate can be collapsed by rewriting the body:

    python3 scripts/CollapseDuplicatedDefs.py --dry     # report
    python3 scripts/CollapseDuplicatedDefs.py           # rewrite

Two files must be left alone: `FinalSlowBase` and `CorrectionStep` — the alias
drops instance arguments the original body had inferred, so they need explicit
arguments, not a mechanical rewrite.

Gate: build green; type dump diff empty.

## 4. Common ancestor modules for the blocked duplicate definitions (mechanical but adds files)

The remaining ~85 duplicate groups cannot be collapsed because the canonical
definition sits *above* the copy in the import order. Fix: one small module per
family holding the definition, imported by both sides. Families, largest first:

* the `ActualSigned*` label family (`Label`, `SignedLabel`, `PulseLabel`, `Index`)
* `Coeff` (three copies)
* `Index` (four copies)

Cost: a few files. Benefit: removes the ambiguity that already broke two merges
(`majorant` in `PaperResults`, `CompleteSpace (RepairData E)` in
`PaperAdditionalResults`). **Not free** — this trades file count for cleanliness,
so it needs a decision if the file count matters.

## 5. Unused-import sweep (mechanical, slow)

After the merges, import lists were expanded in place and some entries are now
unused. Test by removing imports one file at a time and rebuilding that module
only. Roughly 2,000 candidates at ~6 s each — a few hours, so run it in the
background and take the wins in batches.

## 6. First scope-cut family: the `PhysicalSigned*` variants (needs proof repair)

The cut that failed as a sweep (see "Attempts that failed") does work per family.
Start with the variant layer that is largest and most self-contained. Method:
delete the family's off-closure theorems, build, repair what breaks by keeping the
lemmas `simp`/`rw` still need, repeat until green. Expect a few thousand lines per
session, not tens of thousands.

## 7. Second family: `ActualSigned*`

Same method.

## 8. Third family: `LocalPaper*`

Same method.

## 9. Euler: the 61 first-wave errors

`scripts/SorryPatch.py` already produces the list of modules. The first wave is
clean (it comes from twenty theorems). Repair them in dependency order; each fixed
theorem exposes the next wave, so this is a multi-session job. Full state in
`MIGRATION.md` and paper §6.3.

## 10. Decide the Lean `v4.36.0-rc2` / Mathlib `1b1ccf4b` bump (blocked)

Branch `bump/tauceti-latest` holds the attempt: 34 errors, 17 of them `whnf`
timeouts that survive 1,000,000 heartbeats. That is a definitional change in
Mathlib, not slowness, so the bump needs proof repairs, not a timeout bump. Only
worth doing when a newer TauCeti feature is actually needed.

---

## Attempts that failed (do not repeat)

**Scope cut by closure analysis.** Five variants, all reverted: environment
closure (104 errors), corrected names (110), text reachability (153 → 26 after
fixing span and dotted-name bugs), a build-feedback loop over six rounds (25, 28,
34, 26, 30, 24 errors, never converging), and deleting the five wholly-off-closure
modules plus their imports (34 errors — those modules' declarations are used by
other off-closure theorems, so the layer is not separable).

Reason: proofs here rely on the lemma *sets* that `simp`, `rw`, `aesop`,
`positivity` and `gcongr` see, not on named references. Removing a theorem nothing
names still breaks a proof elsewhere, and each repair exposes new failures.

**The 12,247 figure is wrong.** It counted every `thmInfo`, including ~9,400
generated proof auxiliaries (`_proof_3`, `_simp_1_5`). The real number of *source*
theorems outside the closure is 2,291–2,836 depending on how namespaced names are
matched.

**The environment closure under-reports.** `Expr.getUsedConstants` on a theorem's
stored value misses dependencies that the elaborator used, so the closure cannot
be used as a deletion oracle. Confirmed by checking two names it called unused
against the build.

## Measurements that close other questions

* No project theorem duplicates a Mathlib theorem: probe over the whole of
  Mathlib, `CROSS 0` (`scripts/DuplicateProbe.lean`).
* No project theorem duplicates a TauCeti theorem: probe over 24 TauCeti analysis
  modules, `CROSS 0`.
* Few project theorems are special cases of general library lemmas: `exact?` in
  each theorem's own context, 9 of 173 closed, of which four named a library lemma
  and all four are applied.
* TauCeti at the newest commit this toolchain supports: `97a5b235`. Newer needs
  `rc2`; see item 10.
* Other repositories checked: `uda-lab/leray-hopf` (117 files, 7 shared names),
  `rollroyces/ns-blowup` (14 files, 2 shared), `awkronos/navier` (1,066 files,
  22,197 shared names — a sibling copy of this same development, not a library).

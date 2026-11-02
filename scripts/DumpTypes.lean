import Lean

/-!
# Dump the type of every declaration of a library

One `name<TAB>type` line per declaration, sorted by name, for every constant
whose module lies under the given prefix. Diffing two dumps taken around a
refactoring proves that no statement changed --- a green build alone does not,
because a silent change to a declaration can still be elaborated by everything
downstream.

    lake env lean --run scripts/DumpTypes.lean NavierStokes > before.tsv
    ... refactoring ...
    lake env lean --run scripts/DumpTypes.lean NavierStokes > after.tsv
    diff before.tsv after.tsv
-/

open Lean

def main (args : List String) : IO UInt32 := do
  let some pref := args.head? | do
    IO.eprintln "usage: lake env lean --run scripts/DumpTypes.lean <ModulePrefix>"
    return 2
  let mods ← Lean.importModules (imports := #[{ module := pref.toName }])
    (opts := {}) (trustLevel := 1024)
  let mut out : Array String := #[]
  for (name, info) in mods.constants.map₁ do
    let some idx := mods.getModuleIdxFor? name | continue
    let modName := mods.header.moduleNames[idx.toNat]!
    unless pref.toName.isPrefixOf modName do continue
    out := out.push s!"{name}\t{info.type}"
  for l in out.qsort (· < ·) do
    IO.println l
  IO.eprintln s!"{out.size} declarations under {pref}"
  return 0

import NavierStokes
import NavierStokes.TauCetiBridge

/-!
# What the headline theorems actually depend on

Transitive closure of the constants mentioned by the statements and proofs of the
eight headline theorems, over the whole environment.

    lake env lean --run scripts/DependencyClosure.lean

Reported for the pinned tree: 94,415 constants, of which 31,157 are project
constants; 23,204 of the project's 35,451 theorems (65%) are in the closure. The
other 12,247 are not dead --- the unused-declaration prune, which iterates to a
fixed point, leaves none with a single textual occurrence --- they support the
other statements the repository proves (the local, physical, signed and variant
forms), spread over 462 modules.
-/

open Lean Meta

partial def depClosure (env : Environment) (seeds : Array Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut work : Array Name := seeds
  while Array.size work > 0 do
    let n : Name := work.back!
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut es : Array Expr := #[ci.type]
    if let some v := ci.value? (allowOpaque := true) then es := es.push v
    for e in es do
      for c in e.getUsedConstants do
        unless seen.contains c do work := work.push c
  return seen.toArray

def isProj (n : Name) : Bool := (`NavierStokes).isPrefixOf n || (`NavierStokesR3).isPrefixOf n

run_meta do
  let env ← getEnv
  let heads : Array Name := #[
    `NavierStokesR3.breakdownStatement, `NavierStokes.PeriodicPaper.breakdownStatement,
    `NavierStokes.Comparator.navier_stokes_breakdown_R3,
    `NavierStokes.Comparator.navier_stokes_breakdown_periodic,
    `NavierStokesR3.theorem_1_1, `NavierStokes.PeriodicPaper.periodic_corollary,
    `NavierStokesR3.theorem_1_1_with_dissipation, `NavierStokesR3.theorem_1_1_with_initial_rest]
  let all := depClosure env heads
  let proj := all.filter isProj
  logInfo m!"TOTAL {Array.size all}  PROJECT {Array.size proj}  LIBRARY {Array.size all - Array.size proj}"
  let seen : NameSet := ({} : NameSet).insertMany all
  let mut projThm : Nat := 0
  let mut inThm : Nat := 0
  let mut projDecl : Nat := 0
  for (n, ci) in env.constants.map₁ do
    unless isProj n do continue
    projDecl := projDecl + 1
    if ci matches .thmInfo _ then
      projThm := projThm + 1
      if seen.contains n then inThm := inThm + 1
  logInfo m!"PROJECT DECLS {projDecl}  THEOREMS {projThm}  THEOREMS IN CLOSURE {inThm}"
  for (n, ci) in env.constants.map₁ do
    unless isProj n do continue
    if ci matches .thmInfo _ then
      unless seen.contains n do IO.println s!"OUT {n}"

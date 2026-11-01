import Mathlib.Tactic.DuplicateDecls
import NavierStokes.ClosedIntervalCk
import NavierStokes.SmoothCutoffs
import NavierStokes.FlatCutoff
import NavierStokes.JetBounds
import NavierStokes.WeightedClasses
import NavierStokes.AxisCoefficientSpace
import NavierStokes.BlowupImplication
import NavierStokes.R3.ComparisonSetup
import NavierStokes.R3.PressureTestBounds
import NavierStokes.ClosedIntervalJetAlgebra
import NavierStokes.AxisOperators
import NavierStokes.AxisProfile
import NavierStokes.AxisWeightEstimates
import NavierStokes.AxisymmetricFields
import NavierStokes.ChartScales
import NavierStokes.AppendixHeatResults
import NavierStokes.ClosedIntervalCkOperators
import NavierStokes.R3.LpNormTools
import NavierStokes.R3.PairedKernelBound
import NavierStokes.R3.WeightedInterpolation
import NavierStokes.R3.PressureFunctionals

/-!
# Type-level duplicate-declaration probe

Finds theorems whose statements agree with another theorem of the environment up to
binder order, binder information and universe levels. Used to answer, mechanically,
whether this repository restates results that Mathlib, TauCeti or Lean already prove.

The tool is a vendored copy of the core of `Mathlib.Tactic.DuplicateDecls` (Jovan
Gerbscheid, Apache 2.0): that file's declarations are not `public` under the module
system, so an importing module cannot call them.

Run it with the imports of your choice (the list below is the sample reported in
`paper/sec6b-duplication.tex`):

    lake env lean scripts/DuplicateProbe.lean

To check that the probe is alive, import `scripts/PlantedControls.lean` as well: it
contains two planted duplicates, one of another project theorem and one of Mathlib's
`Nat.add_comm`, and the probe must report exactly two groups involving project names.
-/

-- project modules to scan (add or remove freely)


open Lean Meta

namespace DupProbe

partial def eraseUnivs (e : Expr) : Expr :=
  match e with
  | .sort _ => .sort 0
  | .const declName _ => .const declName []
  | .app fn arg => e.updateApp! (eraseUnivs fn) (eraseUnivs arg)
  | .lam _ t b _ => e.updateLambdaE! (eraseUnivs t) (eraseUnivs b)
  | .forallE _ t b _ => e.updateForallE! (eraseUnivs t) (eraseUnivs b)
  | .letE _ t v b _ => e.updateLetE! (eraseUnivs t) (eraseUnivs v) (eraseUnivs b)
  | .mdata _ expr => e.updateMData! (eraseUnivs expr)
  | .proj _ _ s => e.updateProj! (eraseUnivs s)
  | e => e

def sortBinders (e : Expr) : MetaM Expr := do
  (if e.isLambda then lambdaTelescope else forallTelescope) e fun fvars e ↦ do
  let n := fvars.size
  let fvars : Vector Expr n := fvars.toVector
  let mut remainingTypes ← fvars.mapM (return some <| eraseUnivs <| ← inferType ·)
  let mut e := eraseUnivs e
  let mut sortedTypes := #[]
  for _ in *...n do
    let mut minType? : Option (Fin n × Expr) := none
    for h : i in 0...n do
      if let some type := remainingTypes[i] then
        if !type.hasFVar then
          if let some (minIdx, minType) := minType? then
            if type.quickLt minType then
              continue
          minType? := some (⟨i, by get_elem_tactic⟩, type)
    let some (minIdx, minType) := minType? |
      panic! s!"All types have fvars: {remainingTypes.toArray}"
    sortedTypes := sortedTypes.push minType
    remainingTypes := remainingTypes.set minIdx none
    let abstractFVar (e : Expr) := (e.liftLooseBVars 0 1).abstract #[fvars[minIdx]]
    remainingTypes := remainingTypes.map (·.map abstractFVar)
    e := abstractFVar e
  return sortedTypes.foldr (init := e) fun type e ↦ .forallE `_ type e .default

def isAlias (cinfo : ConstantInfo) : Bool :=
  (cinfo.value? (allowOpaque := true)).any isConstBVarApp
where
  isConstBVarApp : Expr → Bool
  | .const .. => true
  | .app f (.bvar _) => isConstBVarApp f
  | .lam _ _ b _ => isConstBVarApp b
  | _ => false

def dups : CoreM (Array (Array Name)) := MetaM.run' do
  let env ← getEnv
  let mut visited : Std.HashMap Expr Name := {}
  let mut dups : Std.HashMap Expr (Array Name) := {}
  for (name, cinfo) in env.constants.map₁ do
    if name.isInternalDetail || name.isMetaprogramming
        || !allowCompletion env name || Linter.isDeprecated env name then continue
    unless ← isProp cinfo.type do continue
    let normType ← sortBinders cinfo.type
    if let some name' := visited[normType]? then
      dups := dups.alter normType (·.getD #[name'] |>.push name)
    else
      visited := visited.insert normType name
  return dups.valuesArray

def isProj (n : Name) : Bool := (`NavierStokes).isPrefixOf n || (`Euler).isPrefixOf n

end DupProbe

set_option maxHeartbeats 0 in
run_meta do
  let env ← getEnv
  let groups ← DupProbe.dups
  let proj := groups.filter (fun g => g.any DupProbe.isProj)
  let cross := proj.filter (fun g => g.any (fun n => !DupProbe.isProj n))
  let internal := proj.filter (fun g => g.all DupProbe.isProj)
  logInfo m!"theorem-duplicate groups in environment: {groups.size}"
  logInfo m!"groups involving a project theorem: {proj.size}"
  logInfo m!"  project vs library (Mathlib/Lean/Std): {cross.size}"
  logInfo m!"  project vs project: {internal.size}"
  let mut shown := 0
  for g in cross do
    if shown < 20 then
      shown := shown + 1
      logInfo m!"{g}"
  let mut shown2 := 0
  for g in internal do
    if shown2 < 10 then
      shown2 := shown2 + 1
      logInfo m!"INTRA {g}"

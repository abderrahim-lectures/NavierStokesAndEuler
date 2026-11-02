import NavierStokes
open Lean Meta

/-- Project definitions grouped by (type, value): two entries in a group are the same
constant defined twice. Generated auxiliaries are skipped. -/
run_meta do
  let env ← getEnv
  let mut byPair : Std.HashMap String (Array Name) := {}
  for (n, ci) in env.constants.map₁ do
    unless (`NavierStokes).isPrefixOf n || (`NavierStokesR3).isPrefixOf n do continue
    if n.isInternalDetail then continue
    let some v := ci.value? (allowOpaque := true) | continue
    unless ci matches .defnInfo _ do continue
    let key := s!"{ci.type}|{v}"
    byPair := byPair.insert key ((byPair.getD key #[]).push n)
  let groups := byPair.toArray.filter (fun (_, v) => v.size > 1)
  logInfo m!"DUPDEF GROUPS {groups.size}"
  for (k, v) in groups do
    let ci_type := k.splitOn "|" |>.head!
    logInfo m!"GROUP {v.toList} | TYPE {ci_type}"

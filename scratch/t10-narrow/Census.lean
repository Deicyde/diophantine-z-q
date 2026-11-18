import ZInQKernel.OneProof.Main
import Lean

/-! Census of the types and proof terms reachable from the base headline. -/

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let old := `T10Etale.T10_TateDuality
  let proj := `HDec.HSyn.OpenAddedLeaves28.t10TateDuality
  let mut todo := #[`ZInQ.OneProof.frozenTarget]
  let mut seen : NameSet := {}
  let mut values : Std.HashMap Name (Array Name) := {}
  let mut typeUsers : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      todo := todo ++ ci.getUsedConstantsAsSet.toList.toArray
      if ci.type.getUsedConstants.contains old then
        typeUsers := typeUsers.insert n
      if let some v := ci.value? (allowOpaque := true) then
        values := values.insert n v.getUsedConstants
  unless seen.contains proj do
    throwError "Base headline does not reach the expected projection"
  let mut mark : NameSet := typeUsers.insert proj
  let mut changed := true
  while changed do
    changed := false
    for (n, deps) in values.toList do
      if !mark.contains n && deps.any mark.contains then
        mark := mark.insert n
        changed := true
  let mut lines := #[]
  for n in mark.toList do
    let mod := (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)
    let calls := (values.getD n #[]).filter mark.contains
    let tag := if calls.contains proj then "READ" else if typeUsers.contains n then "TYPE" else "CALL"
    lines := lines.push s!"{tag} {mod.getD .anonymous} {n} -> {calls.toList}"
  logInfo m!"closure: {seen.size} constants; {lines.size} marked\n{String.intercalate "\n" (lines.qsort (· < ·)).toList}"

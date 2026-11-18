import ZInQKernel.OneProof.Main
import Lean

/-! Census of T10 references in the types and proof terms of the base headline. -/

open Lean Elab Command

-- Imported dependency packages cannot mention a constant introduced in ZInQKernel.
private def inProject (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => (`ZInQKernel).isPrefixOf env.header.modules[i.toNat]!.module
  | none => true

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let old := `T10Etale.T10_TateDuality
  let proj := `HDec.HSyn.OpenAddedLeaves28.t10TateDuality
  let mut todo := #[`ZInQ.OneProof.frozenTarget]
  let mut seen : Std.HashSet Name := {}
  let mut values : Std.HashMap Name (Array Name) := {}
  let mut rev : Std.HashMap Name (Array Name) := {}
  let mut typeUsers : Std.HashSet Name := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n || !inProject env n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      let types := ci.type.getUsedConstants
      todo := todo ++ types
      if types.contains old then
        typeUsers := typeUsers.insert n
      if let .inductInfo i := ci then
        todo := todo ++ i.ctors.toArray
      if let some v := ci.value? (allowOpaque := true) then
        let deps := v.getUsedConstants.filter (inProject env)
        values := values.insert n deps
        todo := todo ++ deps
        for d in deps do
          rev := rev.alter d (fun xs => some ((xs.getD #[]).push n))
  unless seen.contains proj do
    throwError "Base headline does not reach the expected projection"
  let mut mark := typeUsers.insert proj
  let mut visit := mark.toList.toArray
  while !visit.isEmpty do
    let n := visit.back!
    visit := visit.pop
    for c in rev.getD n #[] do
      unless mark.contains c do
        mark := mark.insert c
        visit := visit.push c
  let mut lines := #[]
  for n in mark.toList do
    let mod := (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)
    let calls := (values.getD n #[]).filter mark.contains
    let tag := if calls.contains proj then "READ" else if typeUsers.contains n then "TYPE" else "CALL"
    lines := lines.push s!"{tag} {mod.getD .anonymous} {n} -> {calls.toList}"
  logInfo m!"Project closure: {seen.size} constants; {lines.size} marked\n{String.intercalate "\n" (lines.qsort (· < ·)).toList}"

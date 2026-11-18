
/-! ss-faltings dead-field probe (appended by gen/make_check.sh --dead): for each field of the top bundles, whether any
projection with that field name occurs in the closure of the new top / the old top. Absent = the field is never read. -/
open Lean in
run_cmd do
  let env ← getEnv
  let cNew := ssfClosureOf env `HDec.HSyn.@NEWTOP@
  let cOld := ssfClosureOf env `HDec.HSyn.@OLDTOP@
  let projNames (cl : NameSet) : NameSet := cl.toList.foldl (fun s n =>
    if (env.getProjectionFnInfo? n).isSome then
      match n with | .str _ f => s.insert (.mkSimple f) | _ => s
    else s) {}
  let pNew := projNames cNew
  let pOld := projNames cOld
  for b in [`HDec.HSyn.@NEWR@, `HDec.HSyn.OpenTextbookLeaves18, `HDec.HSyn.OpenAddedLeaves27] do
    for f in getStructureFields env b do
      let a := pNew.contains f
      let o := pOld.contains f
      if !(a && o) then IO.println s!"{b}.{f}: new {a} old {o}"
  IO.println "dead-field probe done"

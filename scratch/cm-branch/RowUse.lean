import ZInQKernel.Contrib.OneProof.CMBranch.Top
open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  let root := `HDec.HSyn.sixContactMin_of_open72_cm
  let rows : List Name := [`LeafQM.AV.R1R2fp, `HDec.LeafAdopt.R1R2fpRepW, `HDec.LeafAdopt.R1R2fpRep, `LeafQM.AV.R5ptProps, `HDec.FS5NoCM.R1R2fpFull]
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[root]
  let mut typeUsers : Array Name := #[]
  let mut valUsers : Array Name := #[]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let s := n.toString
    if (s.startsWith "Mathlib") || (s.startsWith "Lean.") || (s.startsWith "Std.") then continue
    match env.find? n with
    | some ci =>
      let v := match ci with | .thmInfo t => t.value | .defnInfo d => d.value | _ => default
      let tc := ci.type.getUsedConstants
      if rows.any (fun r => tc.contains r) then typeUsers := typeUsers.push n
      else if rows.any (fun r => v.getUsedConstants.contains r) then valUsers := valUsers.push n
      for c in v.getUsedConstants ++ tc do
        if !seen.contains c then stack := stack.push c
    | none => pure ()
  IO.println s!"type mentions row ({typeUsers.size}): {typeUsers.toList}"
  IO.println s!"value-only mentions ({valUsers.size}): {valUsers.toList}"

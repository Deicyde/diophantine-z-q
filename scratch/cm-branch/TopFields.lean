import ZInQKernel.Contrib.OneProof.CMBranch.No5E
open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  let tops := [`HDec.HSyn.OpenResearchLeaves53, `HDec.HSyn.OpenTextbookLeaves18, `HDec.HSyn.OpenAddedLeaves27]
  let roots := #[`HDec.HSyn.sixContactMin_of_open72_cm_no5, `HDec.HSyn.sixContactMin_of_open72]
  let mut res : Array (List Name) := #[]
  for root in roots do
    let mut seen : Std.HashSet Name := {}
    let mut stack : Array Name := #[root]
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
        for c in v.getUsedConstants ++ ci.type.getUsedConstants do
          if !seen.contains c then stack := stack.push c
      | none => pure ()
    let used := tops.flatMap (fun t => (getStructureFields env t).toList.filter (fun f => seen.contains (t ++ f)) |>.map (t ++ ·))
    res := res.push used
    IO.println s!"{root}: {used.length} top fields read"
  let a := res[0]!
  let b := res[1]!
  IO.println s!"read by old, not by new: {b.filter (fun n => !a.contains n)}"
  IO.println s!"read by new, not by old: {a.filter (fun n => !b.contains n)}"

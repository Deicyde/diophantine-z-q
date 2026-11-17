import ZInQKernel.Contrib.OneProof.CMBranch.Top
open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  let root := `HDec.HSyn.sixContactMin_of_open67_cm
  -- closure
  let mut seen : Std.HashSet Name := {}
  let mut order : Array Name := #[]
  let mut stack : Array Name := #[root]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let s := n.toString
    if (s.startsWith "Mathlib") || (s.startsWith "Lean.") || (s.startsWith "Std.") then continue
    order := order.push n
    match env.find? n with
    | some ci =>
      let v := match ci with | .thmInfo t => t.value | .defnInfo d => d.value | _ => default
      for c in v.getUsedConstants ++ ci.type.getUsedConstants do
        if !seen.contains c then stack := stack.push c
    | none => pure ()
  -- affected fixpoint
  let base : Std.HashSet Name := Std.HashSet.ofList [`LeafQM.AV.R1R2fp, `HDec.LeafAdopt.R1R2fpRepW, `LeafQM.AV.R5ptProps]
  let mut aff := base
  let mut changed := true
  while changed do
    changed := false
    for n in order do
      if aff.contains n then continue
      match env.find? n with
      | some ci =>
        let v := match ci with | .thmInfo t => t.value | .defnInfo d => d.value | _ => default
        let cs := v.getUsedConstants ++ ci.type.getUsedConstants
        if cs.any (fun c => aff.contains c) then
          aff := aff.insert n; changed := true
      | none => pure ()
  let user := aff.toList.filter (fun n => !(n.toString.splitOn "_proof_").length > 1 && !(n.isInternal))
  IO.println s!"affected: {aff.size}, user-level: {user.length}"
  let mods := user.filterMap (fun n => (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!))
  let mut cnt : Std.HashMap Name Nat := {}
  for m in mods do cnt := cnt.insert m (cnt.getD m 0 + 1)
  IO.println s!"by module: {cnt.toList}"

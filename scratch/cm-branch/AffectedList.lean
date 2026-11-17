import ZInQKernel.Contrib.OneProof.CMBranch.Top
open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  let root := `HDec.HSyn.sixContactMin_of_open72_cm
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
  let base : Std.HashSet Name := Std.HashSet.ofList [`LeafQM.AV.R1R2fp, `HDec.LeafAdopt.R1R2fpRepW, `LeafQM.AV.R5ptProps, `GRDict.GonzalezRotgerThm512X6, `GR512Bridge.GonzalezRotgerThm512X6RCF]
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
          match ci with
          | .ctorInfo c => if !aff.contains c.induct then aff := aff.insert c.induct
          | _ => pure ()
      | none => pure ()
  for n in aff.toList do
    let mod := (env.getModuleIdxFor? n).map (fun i => (i.toNat, env.header.moduleNames[i.toNat]!))
    let rng ← findDeclarationRanges? n
    let kind := match env.find? n with
      | some (.thmInfo _) => "thm" | some (.defnInfo _) => "def" | some (.inductInfo _) => "ind"
      | some (.ctorInfo _) => "ctor" | some (.recInfo _) => "rec" | _ => "other"
    match rng with
    | some r => IO.println s!"{n}\t{kind}\t{mod}\t{r.range.pos.line}\t{r.range.endPos.line}"
    | none => IO.println s!"{n}\t{kind}\t{mod}\t-\t-"

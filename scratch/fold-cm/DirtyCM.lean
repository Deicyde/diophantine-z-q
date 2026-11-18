import ZInQKernel.OneProof.H.CMTopLive
/-! fold-cm: cm-fold-rebase's Dirty3 scan rooted at the CM-threaded live top `sixContactMin_of_open80_cm` (the R5ptProps prune set).
A constant is DIRTY if it is in the closure of the new top and its type or value mentions a dirty constant, starting
from the row conjunct `LeafQM.AV.R5ptProps` and the GR field. Prints each dirty constant with its module and
declaration range, and whether its TYPE mentions a dirty constant (then a weak copy needs a new statement). -/
open Lean Meta

#eval show MetaM Unit from do
  let env ← getEnv
  let root := `HDec.HSyn.sixContactMin_of_open80_cm
  -- closure
  let mut seen : Std.HashSet Name := {}
  let mut order : Array Name := #[]
  let mut stack : Array Name := #[root]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let inZ := match env.getModuleIdxFor? n with
      | some i => (env.header.moduleNames[i.toNat]!.toString.startsWith "ZInQKernel")
      | none => false
    if !inZ then continue
    order := order.push n
    match env.find? n with
    | some ci =>
      let v := match ci with | .thmInfo t => t.value | .defnInfo d => d.value | _ => default
      for c in v.getUsedConstants ++ ci.type.getUsedConstants do
        if !seen.contains c then stack := stack.push c
    | none => pure ()
  -- fixpoint on dirtiness
  let seeds : List Name := [`LeafQM.AV.R5ptProps]
  let mut dirty : Std.HashSet Name := {}
  for s in seeds do dirty := dirty.insert s
  let mut changed := true
  while changed do
    changed := false
    for n in order do
      if dirty.contains n then continue
      match env.find? n with
      | some ci =>
        let v := match ci with | .thmInfo t => t.value | .defnInfo d => d.value | _ => default
        if (ci.type.getUsedConstants ++ v.getUsedConstants).any (dirty.contains ·) then
          dirty := dirty.insert n; changed := true
          if n.isStr && n.getString! == "mk" then
            dirty := dirty.insert n.getPrefix
      | none => pure ()
  let mut cnt := 0
  for n in order do
    if !dirty.contains n then continue
    cnt := cnt + 1
    let ci := env.find? n |>.get!
    let tyDirty := ci.type.getUsedConstants.any (dirty.contains ·)
    let (mod, idx) := match env.getModuleIdxFor? n with
      | some i => (env.header.moduleNames[i.toNat]!.toString, i.toNat)
      | none => ("?", 0)
    let rng ← findDeclarationRanges? n
    let r := match rng with
      | some r => s!"{r.range.pos.line}-{r.range.endPos.line}"
      | none => "-"
    IO.println s!"{n}\t{mod}\t{idx}\t{r}\t{if tyDirty then "TYPE" else "value"}"
  IO.println s!"dirty: {cnt} of {order.size}"
  for n in order do
    IO.println s!"ALL\t{n}"

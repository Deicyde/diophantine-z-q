import ZInQKernel.OneProof.H.TailZ74
/-! Dependency closure for the GR §9 bypass: the declarations reachable from `sixContactMin_of_open67` whose type
mentions a bundle structure carrying the Bost field (any of the three forms). Prints, in dependency order,
`name<TAB>module<TAB>startLine<TAB>endLine<TAB>kind`. Scratch only. -/
open Lean Meta Elab Command

def bostNames : Array Name :=
  #[`ZInQ.R3Residual.BostLowerBoundAn, `ZInQ.HeightFix.BostLowerBoundPrinted, `ZInQ.HeightSplit.BostLowerBound]

partial def affStructs (env : Environment) : NameSet := Id.run do
  let mut aff : NameSet := {}
  let mut changed := true
  let structs := env.constants.fold (init := #[]) fun acc n _ =>
    if isStructure env n && (`HDec).isPrefixOf n then acc.push n else acc
  while changed do
    changed := false
    for n in structs do
      if aff.contains n then continue
      for f in getStructureFields env n do
        match env.find? (n ++ f) with
        | some pci =>
          let us := pci.type.getUsedConstants
          if us.any (fun c => bostNames.contains c || (aff.contains c && c != n)) then
            aff := aff.insert n; changed := true
        | none => pure ()
  return aff

run_cmd do
  let env ← getEnv
  let aff := affStructs env
  logInfo m!"affected structures: {aff.toList.length}"
  let mentions (c : Name) : Bool :=
    match env.find? c with
    | some ci => aff.contains c || ci.type.getUsedConstants.any aff.contains
    | none => false
  let isAux (c : Name) : Bool :=
    c.isInternal || (match c with | .str p _ => aff.contains p || (match p with | .str q _ => aff.contains q | _ => false) | _ => false)
  let mut visited : NameSet := {}
  let mut order : Array Name := #[]
  -- iterative DFS with post-order
  let mut stack : Array (Name × Bool) := #[(`HDec.HSyn.sixContactMin_of_open67, false)]
  while h : stack.size > 0 do
    let (c, done) := stack.back
    stack := stack.pop
    if done then order := order.push c; continue
    if visited.contains c then continue
    visited := visited.insert c
    stack := stack.push (c, true)
    let some ci := env.find? c | continue
    let deps := (ci.type.getUsedConstants ++ (ci.value? (allowOpaque := true) |>.map (·.getUsedConstants) |>.getD #[]))
    for d in deps do
      if !visited.contains d && mentions d then
        -- structures: also need their field types' deps (none mention aff except themselves)
        stack := stack.push (d, false)
  let mut out := ""
  for c in order do
    if isAux c && !aff.contains c then continue
    let some ci := env.find? c | continue
    let kind := if aff.contains c then "structure" else match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | _ => "other"
    let modName := match env.getModuleIdxFor? c with
      | some i => env.header.moduleNames[i.toNat]!
      | none => `current
    let r ← liftCoreM <| findDeclarationRanges? c
    let (s, e) := match r with
      | some rr => (rr.range.pos.line, rr.range.endPos.line)
      | none => (0, 0)
    out := out ++ s!"{c}\t{modName}\t{s}\t{e}\t{kind}\n"
  IO.FS.writeFile "scratch/bost-gr9/closure.tsv" out
  logInfo m!"wrote {order.size} entries"

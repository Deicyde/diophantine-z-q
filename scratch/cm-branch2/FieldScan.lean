import ZInQKernel.Contrib.OneProof.CMBranch.Open73
/-! cm-branch2: which fields of the top bundles does the new top read? (PruneScan-style, by projection occurrence) -/
open Lean Meta

def closureZ (env : Environment) (root : Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
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
    match env.find? n with
    | some ci =>
      let v := match ci with | .thmInfo t => t.value | .defnInfo d => d.value | _ => default
      for c in v.getUsedConstants ++ ci.type.getUsedConstants do
        if !seen.contains c then stack := stack.push c
    | none => pure ()
  return seen

#eval show MetaM Unit from do
  let env ← getEnv
  let s := closureZ env `HDec.HSyn.sixContactMin_of_open73_cm
  for S in [`HDec.HSyn.OpenResearchLeaves54CM, `HDec.HSyn.OpenAddedLeaves27, `HDec.HSyn.OpenTextbookLeaves18] do
    match getStructureInfo? env S with
    | some info =>
      let fs := info.fieldNames
      let unread := fs.filter (fun f => !s.contains (S ++ f))
      IO.println s!"{S}: {fs.size} fields, unread: {unread.toList}"
    | none => IO.println s!"{S}: not a structure"

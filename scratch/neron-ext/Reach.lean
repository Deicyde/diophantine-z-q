import ZInQKernel.OneProof.Main
open Lean Meta Elab Command

/-! Consumers of `NeronSchemeModelExistsDVR`, `RaynaudCriterion` (r6), `GrothendieckMonodromy` (r8) in the closure
of `ZInQ.OneProof.frozenTarget` (pattern of scratch/gt-qm/Reach.lean). -/

def reach (root : Name) : CommandElabM (Std.HashSet Name) := do
  let env ← getEnv
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[root]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let local? : Bool := match env.getModuleIdxFor? n with
      | some idx => let m := env.header.moduleNames[idx.toNat]!
                    (`ZInQKernel).isPrefixOf m || (`ZInQ).isPrefixOf m
      | none => true
    if !local? then continue
    let mut used := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then used := used ++ v.getUsedConstants
    for c in used do
      if !seen.contains c then stack := stack.push c
  return seen

def modOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).toString
  | none => "?"


elab "#scan " root:ident tgts:ident* : command => do
  let s ← reach root.getId
  let env ← getEnv
  let mut out : Array String := #[]
  for tgt in tgts do
    let t := tgt.getId
    let mut lines : Array String := #[]
    for n in s.toArray do
      let some ci := env.find? n | continue
      if n == t then continue
      let inType := ci.type.getUsedConstants.contains t
      let inVal := match ci.value? (allowOpaque := true) with
        | some v => v.getUsedConstants.contains t
        | none => false
      if inType || inVal then
        lines := lines.push s!"{n} [{modOf env n}] type:{inType} value:{inVal}"
    out := out.push s!"== {t}: {lines.size} reachable constants mention it\n{String.intercalate "\n" (lines.qsort (· < ·)).toList}"
  for f in [`neronSchemeExtensionExists, `t41, `n1] do
    let projs := s.toArray.filter fun n => (match n with | .str _ x => x == f.toString | _ => false) && (env.isProjectionFn n)
    let mut lines : Array String := #[]
    for p in projs do
      for n in s.toArray do
        let some ci := env.find? n | continue
        if let some v := ci.value? (allowOpaque := true) then
          if v.getUsedConstants.contains p then lines := lines.push s!"{p} <- {n} [{modOf env n}]"
    out := out.push s!"== projections .{f}\n{String.intercalate "\n" (lines.qsort (· < ·)).toList}"
  logInfo (String.intercalate "\n" out.toList)


#scan ZInQ.OneProof.frozenTarget ZInQ.Contrib.NeronC.NeronSchemeExtensionExists ZInQ.Contrib.NeronC.neronModelExists_of_extension GapNeron.neronSchemeModelExistsNF GapNeron.NeronSchemeModelExistsDVRNF ZInQ.H5Neron.NeronModelExists ZInQ.H5Glue.NeronModelExists HDec.HSyn.t41_of_extension5

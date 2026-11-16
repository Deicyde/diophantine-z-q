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

elab "#consumers " root:ident tgt:ident : command => do
  let s ← reach root.getId
  let env ← getEnv
  let t := tgt.getId
  let mut out : Array String := #[]
  for n in s.toArray do
    let some ci := env.find? n | continue
    if n == t then continue
    let inType := ci.type.getUsedConstants.contains t
    let inVal := match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstants.contains t
      | none => false
    if inType || inVal then
      out := out.push s!"{n} [{modOf env n}] type:{inType} value:{inVal}"
  logInfo m!"{t}: {out.size} reachable constants mention it\n{String.intercalate "\n" (out.qsort (· < ·)).toList}"

/-- reachable projections named `*.f` and the reachable constants whose value uses them -/
elab "#projUsers " root:ident f:ident : command => do
  let s ← reach root.getId
  let env ← getEnv
  let projs := s.toArray.filter fun n => (match n with | .str _ s => s == f.getId.toString | _ => false) && (env.isProjectionFn n)
  let mut out : Array String := #[]
  for p in projs do
    for n in s.toArray do
      let some ci := env.find? n | continue
      if let some v := ci.value? (allowOpaque := true) then
        if v.getUsedConstants.contains p then out := out.push s!"{p} <- {n} [{modOf env n}]"
  logInfo m!"projections .{f.getId}: {projs.qsort (·.toString < ·.toString)}\n{String.intercalate "\n" (out.qsort (· < ·)).toList}"

#consumers ZInQ.OneProof.frozenTarget ReductSplit.NeronSchemeModelExistsDVR
#consumers ZInQ.OneProof.frozenTarget PkgI2.GrothendieckMonodromy
#consumers ZInQ.OneProof.frozenTarget PkgI2.RaynaudCriterion
#projUsers ZInQ.OneProof.frozenTarget r8
#projUsers ZInQ.OneProof.frozenTarget r6
#consumers ZInQ.OneProof.frozenTarget ObjBridge.RaynaudCriterion
#consumers ZInQ.OneProof.frozenTarget ObjBridge.GrothendieckMonodromy

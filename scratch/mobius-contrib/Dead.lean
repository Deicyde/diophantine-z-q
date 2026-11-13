import ZInQKernel.Contrib.Mobius.ImagePlane
open Lean Meta Elab Command

/-- Constants reachable from `roots` through types, values and inductive structure. -/
partial def reach (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      let mut cs := ci.type.getUsedConstants.toList
      if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants.toList
      match ci with
      | .inductInfo i => cs := cs ++ i.ctors
      | .ctorInfo c => cs := cs ++ [c.induct]
      | _ => pure ()
      todo := cs ++ todo
  return seen

elab "#dead" : command => do
  let env ← getEnv
  let roots := [``LeafQM.AV.CurveGlue.mobiusGlue_of_T5, ``LeafQM.AV.CurveGlue.mobiusGlue_of_t5,
    ``LeafQM.AV.Pin.imagePlaneCurveClosed]
  let used := reach env roots
  let usedL := used.toList
  let mods := env.header.moduleNames
  for (n, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := mods[idx.toNat]!
    unless (`ZInQKernel.Contrib.Mobius).isPrefixOf m do continue
    if n.isInternalDetail then continue
    let isUsed := used.contains n || usedL.any (fun u => n.isPrefixOf u)
    let some r ← liftTermElabM (findDeclarationRanges? n) | continue
    logInfo m!"DECL {if isUsed then "USED" else "DEAD"} {m} {r.range.pos.line} {r.range.endPos.line} {n}"

#dead

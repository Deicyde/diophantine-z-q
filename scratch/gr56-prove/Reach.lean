import ZInQKernel.OneProof.Main
open Lean Meta Elab Command

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

elab "#reachR5 " root:ident : command => do
  let s ← reach root.getId
  let env ← getEnv
  let keys : List Name := [`LeafQM.AV.R5fpCount, `GRCountX6.GonzalezRotgerProp56X6,
    `ShimuraSplit.GonzalezRotgerCountX6Ab, `ShimuraSplit.GonzalezRotgerCountX6]
  logInfo m!"reached {s.size}"
  for n in (s.toArray.qsort (·.toString < ·.toString)) do
    let some ci := env.find? n | continue
    let tu := ci.type.getUsedConstants
    let tk := keys.filter tu.contains
    let vk : List Name := match ci.value? (allowOpaque := true) with
      | some v => let vu := v.getUsedConstants; keys.filter vu.contains
      | none => []
    if !tk.isEmpty || !vk.isEmpty then
      logInfo m!"{n} [{(env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)}] type:{tk} value:{vk}"

#reachR5 ZInQ.OneProof.frozenTarget

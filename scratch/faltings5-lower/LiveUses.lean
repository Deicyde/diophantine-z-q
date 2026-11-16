import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower

/-! faltings5-lower: which constants mentioning `faltingsLemma5`/`FaltingsLemma5` are in the
dependency closure of `ZInQ.OneProof.frozenTarget` (and of the proposed replacement term). -/

open Lean Meta Elab Command

partial def f5Closure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | some ci =>
      for c in ci.type.getUsedConstants do
        unless seen.contains c do todo := todo.push c
      if let some v := ci.value? (allowOpaque := true) then
        for c in v.getUsedConstants do
          unless seen.contains c do todo := todo.push c
    | none => pure ()
  return seen

elab "#liveUses " root:ident : command => do
  let env ← getEnv
  let s := f5Closure env root.getId
  let hits := s.toList.filter fun n =>
    let str := n.toString
    (str.splitOn "altingsLemma5").length > 1 || (str.splitOn "faltings5").length > 1
  logInfo m!"{root.getId}: {s.size} constants in closure; matches: {hits}"

#liveUses ZInQ.OneProof.frozenTarget

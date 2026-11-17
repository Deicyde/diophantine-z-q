import ZInQKernel.OneProof.Main
open Lean Meta Elab Command

partial def cloOf (env : Environment) (root : Name) : IO (Std.HashSet Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | some ci =>
      for c in ci.getUsedConstantsAsSet do
        if !seen.contains c then stack := stack.push c
    | none => pure ()
  return seen

elab "#probe" : command => do
  let env ← getEnv
  let cl ← cloOf env ``ZInQ.OneProof.frozenTarget
  IO.println s!"closure size {cl.size}"
  let targets := [``CToPrinted.SGA3_VIB_3_10, ``SGA3IdComp.SGA3_VIB_3_10_Nbhd, ``CToPrinted.idCompSet]
  for t in targets do
    IO.println s!"== users of {t}"
    for n in cl do
      if let some ci := env.find? n then
        if ci.getUsedConstantsAsSet.contains t then
          let inTy := ci.type.getUsedConstants.contains t
          IO.println s!"  {n} (inType={inTy}) mod={(env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)}"
#probe

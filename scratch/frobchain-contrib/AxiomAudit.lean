import ZInQKernel.Contrib.FrobChain.Main

/-! Axiom audit (task frobchain-contrib): every declaration whose module is
`ZInQKernel.Contrib.FrobChain.*` depends only on `propext`, `Classical.choice`, `Quot.sound`. -/

open Lean Elab Command in
elab "#audit_frobchain" : command => do
  let env ← getEnv
  let std := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut n := 0
  let mut nThm := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (c, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`ZInQKernel.Contrib.FrobChain).isPrefixOf mod do continue
    n := n + 1
    if ci matches .thmInfo _ then nThm := nThm + 1
    let axs ← liftCoreM <| collectAxioms c
    let extra := axs.filter (fun a => !std.contains a)
    unless extra.isEmpty do bad := bad.push (c, extra)
  logInfo m!"FrobChain declarations: {n} (theorems: {nThm}); with non-standard axioms: {bad.size} {bad.toList}"

#audit_frobchain

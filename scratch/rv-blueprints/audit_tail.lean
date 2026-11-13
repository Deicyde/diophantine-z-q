
/-! rv-blueprints axiom audit (appended): every declaration added in this file. -/
open Lean Elab Command in
elab "#rv_audit_axioms" : command => do
  let env ← getEnv
  let mut n : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for (c, _) in env.constants.map₂.toList do
    if c.isInternal then continue
    n := n + 1
    let axs ← liftCoreM <| Lean.collectAxioms c
    let extra := axs.filter (fun a => !std.contains a)
    if extra.size > 0 then bad := bad.push (c, extra)
  logInfo m!"rv_audit: {n} declarations; non-standard axioms in {bad.size}: {bad.toList.take 20}"
#rv_audit_axioms


open Lean Elab Command in
elab "#rvw17_check_axioms" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let mut cnt : Nat := 0
  for (n, _) in env.constants.map₂.toList do
    if n.isInternal then continue
    cnt := cnt + 1
    let axs ← liftCoreM (Lean.collectAxioms n)
    if axs.any (fun a => a ∉ [``propext, ``Classical.choice, ``Quot.sound]) then
      bad := bad.push n
      logInfo m!"BAD {n}: {axs}"
  logInfo m!"rvw17: {cnt} declarations checked, {bad.size} with nonstandard axioms"

#rvw17_check_axioms

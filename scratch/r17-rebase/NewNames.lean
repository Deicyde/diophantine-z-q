import ZInQKernel.Contrib.OneProof.CarayolPrintedIrr
open Lean in
-- Print every constant declared in the four new modules (r17-rebase clash check, scratch only).
#eval show Lean.CoreM Unit from do
  let env ← getEnv
  let mods := #[`ZInQKernel.Contrib.OneProof.CarayolPrintedIrr, `ZInQKernel.Contrib.OneProof.CarayolPrinted,
    `ZInQKernel.Contrib.OneProof.NewformDict, `ZInQKernel.Contrib.OneProof.CarayolLevel]
  let idxs := mods.filterMap env.getModuleIdx?
  let mut out := #[]
  for (n, _) in env.constants.map₁.toList do
    if let some i := env.getModuleIdxFor? n then
      if idxs.contains i && !n.isInternal then out := out.push n.toString
  IO.println s!"COUNT {out.size}"
  for s in out.qsort (· < ·) do IO.println s

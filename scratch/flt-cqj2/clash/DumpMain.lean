import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.CloudB2X0Transitive.ModularEquation
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut out : Array String := #[]
  for (n, idx) in env.const2ModIdx.toList do
    let m := mods[idx.toNat]!
    if (`Mathlib).isPrefixOf m || (`Init).isPrefixOf m || (`Lean).isPrefixOf m || (`Std).isPrefixOf m
      || (`Batteries).isPrefixOf m || (`Aesop).isPrefixOf m || (`Qq).isPrefixOf m || (`Lake).isPrefixOf m
      || (`Plausible).isPrefixOf m || (`ProofWidgets).isPrefixOf m || (`ImportGraph).isPrefixOf m then continue
    out := out.push s!"{n} {m}"
  IO.FS.writeFile "scratch/flt-cqj2/clash/main_names.txt" (String.intercalate "\n" out.toList)

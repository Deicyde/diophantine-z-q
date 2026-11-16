import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut out : Array String := #[]
  for (n, idx) in env.const2ModIdx.toList do
    let m := mods[idx.toNat]!
    if (`ZInQKernel.Contrib.CloudB2X0Transitive.Vendor).isPrefixOf m then
      out := out.push s!"{n} {m}"
  IO.FS.writeFile "scratch/flt-cqj2/clash/flt_names.txt" (String.intercalate "\n" out.toList)

import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut out : Array String := #[]
  for (n, idx) in env.const2ModIdx.toList do
    let m := mods[idx.toNat]!
    if (`ZInQKernel.Contrib.OneProof.NeronFLT).isPrefixOf m then
      out := out.push s!"{n} {m}"
  IO.FS.writeFile "scratch/neron-flt/clash/flt_names.txt" (String.intercalate "\n" out.toList)

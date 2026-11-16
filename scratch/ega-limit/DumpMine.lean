import ZInQKernel.Contrib.OneProof.EGAIV_8_10_5_xii
open Lean Elab Command in
elab "#dumpNames " out:str pfx:str* : command => do
  let env ← getEnv
  let ps := pfx.toList.map (·.getString)
  let mut lines : Array String := #[]
  for (n, _) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := (env.header.moduleNames[idx.toNat]!).toString
      if ps.any (fun p => p.isPrefixOf m) then
        lines := lines.push s!"{n}\t{m}"
    | none => pure ()
  IO.FS.writeFile out.getString (String.intercalate "\n" lines.toList)
#dumpNames "/tmp/ega-limit/mine.tsv" "ZInQKernel.Contrib.OneProof.EGAProperLimit" "ZInQKernel.Contrib.OneProof.EGAIV_8_10_5_xii"

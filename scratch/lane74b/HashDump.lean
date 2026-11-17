import ZInQKernel
import ZInQKernel.OneProof.Main

/-! lane74b hash guard (item 2): `scratch/one-proof/DumpCompact.lean`'s record (name, module, universe parameters, hash
of the type, hash of the value) for every constant declared in a `ZInQKernel` module of the environment of
`ZInQKernel` + `ZInQKernel.OneProof.Main`, written to the file named by the environment variable `HASHDUMP_OUT`. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut out : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := mods[idx.toNat]!
      if (`ZInQKernel).isPrefixOf m then
        let vh := match ci.value? (allowOpaque := true) with | some v => v.hash | none => 0
        out := out.push s!"{n} {m} {ci.levelParams} {ci.type.hash} {vh}"
  out := out.qsort (· < ·)
  let some path ← IO.getEnv "HASHDUMP_OUT" | throwError "set HASHDUMP_OUT"
  IO.FS.writeFile path (String.intercalate "\n" out.toList ++ "\n")
  logInfo m!"{out.size} constants hashed to {path}"

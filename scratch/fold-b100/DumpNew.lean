import ZInQKernel.OneProof.Main
/-! fold-b100 hash guard: hash of every constant of the ZInQKernel.OneProof modules after the fold. -/
set_option pp.all true in
#check @ZInQ.OneProof.frozenTarget
#print axioms ZInQ.OneProof.frozenTarget

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut out : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := mods[idx.toNat]!
      if (`ZInQKernel.OneProof).isPrefixOf m then
        let vh := match ci.value? (allowOpaque := true) with | some v => v.hash | none => 0
        out := out.push s!"{n} {m} {ci.levelParams} {ci.type.hash} {vh}"
  out := out.qsort (· < ·)
  IO.FS.writeFile "scratch/fold-b100/hashes_after.txt" (String.intercalate "\n" out.toList ++ "\n")
  logInfo m!"{out.size} constants hashed"


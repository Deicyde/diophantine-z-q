import ZInQKernel.OneProof.Main
/-! leaf-fold7 check (copy of op-compact's DumpCompact): frozenTarget's type (pp.all), its axioms, and a hash of the type and value of every
constant declared in the `ZInQKernel.OneProof` modules, written to `scratch/leaf-fold7/hashes.txt`. -/
open Lean Elab Command

set_option pp.all true in
#check @ZInQ.OneProof.frozenTarget

#print axioms ZInQ.OneProof.frozenTarget

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
  IO.FS.writeFile "scratch/leaf-fold7/hashes.txt" (String.intercalate "\n" out.toList ++ "\n")
  logInfo m!"{out.size} constants hashed"

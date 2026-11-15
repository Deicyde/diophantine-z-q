import ZInQKernel.OneProof.H.TailZ31
/-! op-compact check: frozenTarget's type (pp.all), its axioms, and a hash of the type and value of every
constant declared in the `ZInQKernel.OneProof` modules, written to `scratch/yu-prune/compact_hashes31.txt`. -/
open Lean Elab Command

set_option pp.all true in
#check @HDec.HSyn.sixContactMin_of_open25

#print axioms HDec.HSyn.sixContactMin_of_open25

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut out : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := mods[idx.toNat]!
      if (`ZInQKernel.OneProof).isPrefixOf m || m == `ZInQKernel.Contrib.OneProof.QMLattice then
        let vh := match ci.value? (allowOpaque := true) with | some v => v.hash | none => 0
        out := out.push s!"{n} {m} {ci.levelParams} {ci.type.hash} {vh}"
  out := out.qsort (· < ·)
  IO.FS.writeFile "scratch/yu-prune/compact_hashes31.txt" (String.intercalate "\n" out.toList ++ "\n")
  logInfo m!"{out.size} constants hashed"

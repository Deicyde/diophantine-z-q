import ZInQKernel.OneProof.Main
import Lean
/-! sga735-narrow: which consumers of `UnipSq` (r6's conclusion) are in the closure of `sixContactMin_of_open41`,
and which closure constants use them directly. -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[`HDec.HSyn.sixContactMin_of_open41]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ccValue? ci then todo := todo ++ v.getUsedConstants
  let targets : List Name := [`PkgI2.UnipSq, `PkgI2.fixed_of_unipSq_of_iterate, `PkgI2.D2_fixed_of_raynaud,
    `HDec.PkgI2.quatUnipotentTrivial, `HDec.PkgI2.QuatUnipotentTrivial, `PkgI2.RaynaudCriterion,
    `HDec.PkgI2.RaynaudCriterionNF, `GapNeron.RaynaudCriterionNF, `PkgI2.quatUnipotentTrivial]
  for t in targets do
    IO.println s!"{t} in closure: {seen.contains t}"
  -- direct users (value) of UnipSq-consuming lemmas within the closure
  for c in seen.toList do
    if let some ci := env.find? c then
      if let some v := ccValue? ci then
        let us := v.getUsedConstants
        if us.any (fun u => u == `HDec.PkgI2.quatUnipotentTrivial || u == `PkgI2.quatUnipotentTrivial ||
            u == `PkgI2.fixed_of_unipSq_of_iterate || u == `PkgI2.D2_fixed_of_raynaud) then
          IO.println s!"USER {c}"

run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[`HDec.HSyn.sixContactMin_of_open41]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ccValue? ci then todo := todo ++ v.getUsedConstants
  let keys : List Name := [`PkgI2.UnipSq, `HDec.PkgI2.RaynaudCriterionNF, `GapNeron.RaynaudCriterionNF]
  let mut n := 0
  for c in seen.toList do
    if let some ci := env.find? c then
      if ci.type.getUsedConstants.any (keys.contains ·) then
        n := n + 1
        IO.println s!"TYPE {c}"
  IO.println s!"constants whose type mentions UnipSq/RaynaudCriterionNF: {n}"

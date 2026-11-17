import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.HomFreeFiniteAlgClosedReroute
import Lean
/-! homfree-noemb: the closure of `sixContactMin_of_open38_hf` (values and types) must not contain
`HomFreeFiniteAlgClosed`, `PkgI3.HomFreeFinite`, `HomFreeFiniteAlgClosedNoEmb` or `sorryAx`. -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

run_cmd do
  let env ← getEnv
  let bad : List Name := [`ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed, `PkgI3.HomFreeFinite,
    `ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteAlgClosedNoEmb, `sorryAx, `HDec.HSyn.t6_of_algClosed5]
  for top in [`HDec.HSyn.sixContactMin_of_open38_hf] do
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[top]
    while !todo.isEmpty do
      let c := todo.back!
      todo := todo.pop
      if seen.contains c then continue
      seen := seen.insert c
      if let some ci := env.find? c then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := ccValue? ci then todo := todo ++ v.getUsedConstants
    IO.println s!"{top}: closure {seen.size}"
    for b in bad do
      IO.println s!"  contains {b}: {seen.contains b}"
    IO.println s!"  contains HomFreeFiniteC: {seen.contains `ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC}"

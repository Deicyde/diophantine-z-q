import ZInQKernel.OneProof.Main
/-! fold-chev: closure check of the folded frozen target. The removed Prop `ZInQ.SemiAbDescend.ChevalleyPerfect`
must not occur in the closure (types and values) of `ZInQ.OneProof.frozenTarget`, nor `sorryAx`; the old top
bundle `OpenResearchLeaves45` and Chevalley's readers must be gone. -/

#print axioms ZInQ.OneProof.frozenTarget
#print axioms HDec.HSyn.sixContactMin_of_open65
#check @HDec.HSyn.sixContactMin_of_open65

open Lean in
def fcValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

open Lean in
run_cmd do
  let env ← getEnv
  let closure : Name → NameSet := fun root => Id.run do
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[root]
    while !todo.isEmpty do
      let c := todo.back!
      todo := todo.pop
      if seen.contains c then continue
      seen := seen.insert c
      if let some ci := env.find? c then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := fcValue? ci then todo := todo ++ v.getUsedConstants
    return seen
  let checked : List Name := [`ZInQ.SemiAbDescend.ChevalleyPerfect,
    `ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley,
    `ZInQ.SemiAbDescend.bostLowerBound_of_printed_chevalley,
    `ZInQ.SemiAbDescend.gaudronRemondThm14_of_printed_chevalley, `sorryAx,
    `HDec.HSyn.OpenResearchLeaves45, `HDec.HSyn.sixContactMin_of_open64,
    `ZInQ.HeightFix.SemiAbelianDescendsPerfect, `ZInQ.ChevFree.semiAbelianDescendsPerfect_proof]
  for root in [`ZInQ.OneProof.frozenTarget] do
    let s := closure root
    IO.println s!"{root}: closure {s.size}"
    for b in checked do
      IO.println s!"  contains {b}: {s.contains b}"

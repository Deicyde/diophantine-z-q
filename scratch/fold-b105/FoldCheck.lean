import ZInQKernel.OneProof.Main
/-! fold-b105: closure check of the folded frozen target (after each fold). The removed Props must not occur in
the closure (types and values) of `ZInQ.OneProof.frozenTarget`, nor `sorryAx`; the hypotheses of frozenTarget are
printed by `#check`. Edit `checked` per fold. -/

#print axioms ZInQ.OneProof.frozenTarget
#check @ZInQ.OneProof.frozenTarget

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
  let checked : List Name := [`sorryAx,
    -- fold 1 (chevalleyPerfect)
    `ZInQ.SemiAbDescend.ChevalleyPerfect, `ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley,
    `ZInQ.SemiAbDescend.bostLowerBound_of_printed_chevalley,
    `ZInQ.SemiAbDescend.gaudronRemondThm14_of_printed_chevalley,
    `HDec.HSyn.OpenResearchLeaves48, `HDec.HSyn.sixContactMin_of_open67,
    `ZInQ.ChevFree.semiAbelianDescendsPerfect_proof,
    -- fold 2 (semistab-assembly)
    `ZInQ.SemistabAssembly.BostLowerBoundAnSS, `ZInQ.SemistabAssembly.GaudronRemondThm14AnSS,
    `ZInQ.SemistabAssembly.bostLowerBoundAn_of_ss, `ZInQ.SemistabAssembly.gaudronRemondThm14An_of_ss,
    -- fold 3 (pb-p1)
    `HDec.PkgI4.PanDict.PanPrintedP, `HDec.PkgI4.PanDict.BergerPrintedVT, `HDec.PkgI4.PanDict.BergerPrintedV,
    `HDec.PkgI4.PanDict.PanPrintedF, `HDec.PkgI4.PanDict.BergerSurveyF, `HDec.PkgI4.PanDict.panBerger_of_F]
  for root in [`ZInQ.OneProof.frozenTarget] do
    let s := closure root
    IO.println s!"{root}: closure {s.size}"
    for b in checked do
      IO.println s!"  contains {b}: {s.contains b}"

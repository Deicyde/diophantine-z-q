import ZInQKernel.OneProof.Main
/-! fold-c8: closure check of the folded frozen target (copied from fold-b116). The removed Props must not occur in
the closure (types and values) of `ZInQ.OneProof.frozenTarget`, nor `sorryAx`; the hypotheses of frozenTarget are
printed by `#check`. -/

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
    -- removed by fold-c8 (must be false): the Picard rows, the old top bundles, Tate 1967, the Weil-pairing C8 route
    `T09Pic.PicRepresentableAbVar, `KleimanSite.KleimanPicZeroProper954SiteQ,
    `HDec.HSyn.OpenAddedLeaves27, `HDec.HSyn.OpenResearchLeaves60, `HDec.HSyn.sixContactMin_of_open79,
    `HDec.G0Galois.C8Conrad.TateTwistInvariantsInertia,
    `HDec.HSyn.detTate_of_leaves4_pz, `HDec.HSyn.GR9.sixContactMin_of_open45_pz_eb_sf_u,
    `HDec.HSyn.hodgeTateDecompAbVar_of_open_k954,
    -- the new route (must be true)
    `HDec.G0Galois.C8Conrad.ConradAppB, `HDec.G0Galois.C8Conrad.ConradPropB3Qp, `HDec.G0Galois.C8Conrad.ConradAppBQp,
    `HDec.G0Galois.C8Conrad.g12DetPZ_of_inputs, `HDec.G0Galois.C8Conrad.twistCharHTWt0_proof,
    `DeRhamScholze.HTMerge.ScholzeH1AbVar, `T10Etale.T10_TateDuality,
    `ZInQ.Contrib.CloudR2Poincare.poincareComplement_proof, `HDec.HSyn.sixContactMin_of_open79_hm,
    `HDec.HSyn.OpenResearchLeaves61, `HDec.HSyn.OpenAddedLeaves28, `HDec.HSyn.sixContactMin_of_open80,
    -- read only inside the conversion (filled from the Scholze leaf): true, but not a hypothesis
    `ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr]
  for root in [`ZInQ.OneProof.frozenTarget] do
    let s := closure root
    IO.println s!"{root}: closure {s.size}"
    for b in checked do
      IO.println s!"  contains {b}: {s.contains b}"
    -- every Picard-named constant left in the closure
    let pic := s.toList.filter (fun n => let x := n.toString; (x.splitOn "PicRepresentable").length > 1 || (x.splitOn "KleimanPicZeroProper").length > 1)
    IO.println s!"  PicRepresentable/KleimanPicZeroProper-named constants in the closure: {pic.length} {pic.take 40}"

/-! Field check (edit the two bundle names per fold): fold-c8, `OpenResearchLeaves61` has `OpenResearchLeaves60`'s fields
without `hodgeTateDecompOr`, every other field with the same type. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let o := `HDec.HSyn.OpenResearchLeaves60
  let n := `HDec.HSyn.OpenResearchLeaves61
  let fo := getStructureFields env o
  let fn := getStructureFields env n
  logInfo m!"field check: {o} {fo.size} fields, {n} {fn.size} fields; only in old: {fo.filter (!fn.contains ·)}; only in new: {fn.filter (!fo.contains ·)}"
  for f in fo do
    if fn.contains f then
      let tyO := (env.find? (o ++ f)).get!.type.bindingBody!
      let tn := (env.find? (n ++ f)).get!.type.bindingBody!
      unless tyO == tn do logInfo m!"type differs: {f}"

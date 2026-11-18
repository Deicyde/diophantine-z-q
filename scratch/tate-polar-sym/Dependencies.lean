import ZInQKernel.Contrib.OneProof.TatePolarSym

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  if env.header.modules.any (fun entry => entry.module == `ZInQKernel.OneProof.Main) then
    throwError "contribution imports the headline"
  let excluded := ["PicRepresentableAbVar", "PicZeroAbVar0", "KleimanPicZeroProper954SiteQ",
    "PicZeroAbVar", "IsPicZero", "T09_SymmIsogenyExists0", "mumfordSquareAC0_of_open",
    "mumfordMulNPicZeroAC0_of_open", "phiAmpleIsogeny0_of_open", "weilNondegRight0_of_open",
    "weilPairingMumford0_of_open", "t09SymmIsogenyExists0_of_four0"]
  let consumesClause := fun (name : Name) =>
    ((`DeRhamScholze.HTMerge).isPrefixOf name &&
      name != `DeRhamScholze.HTMerge.ScholzeH1AbVar._proof_1) ||
    (`DeRhamScholze.HTAbVar.HodgeNumberH1AbVar).isPrefixOf name ||
    (`DeRhamScholze.HTAbVar.hodgeTate01_dims).isPrefixOf name ||
    (`DeRhamScholze.HTAbVar.finrank_filD_dual).isPrefixOf name ||
    (`DeRhamScholze.HTAbVar.hodgeTateDecompAbVar_of_scholze).isPrefixOf name ||
    (`ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar).isPrefixOf name
  let collectInputs (ty : Expr) : CommandElabM (Array Name) := do
    let mut ty := ty
    let mut inputs := #[]
    while let .forallE _ domain body _ := ty do
      inputs := inputs ++ domain.getUsedConstants
      ty := body
    unless ty.isConstOf `DeRhamScholze.HTMerge.ScholzeH1AbVar do
      throwError "unexpected conclusion {ty}"
    return inputs
  for (root, withType) in [(`HodgeFil1.tatePolarizationSymmetry_proof, true),
      (`HodgeFil1.scholzeH1AbVar_of_dR, false)] do
    let some ci := env.find? root | throwError "missing {root}"
    let some value := ci.value? (allowOpaque := true) | throwError "missing proof of {root}"
    let mut todo := value.getUsedConstants
    if withType then
      todo := todo ++ ci.type.getUsedConstants
    else
      todo := todo ++ (← collectInputs ci.type)
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let name := todo.back!
      todo := todo.pop
      if seen.contains name then continue
      seen := seen.insert name
      if (name.toString.splitOn ".").any (fun part => excluded.contains part) then
        throwError "{root} depends on excluded declaration {name}"
      if consumesClause name || (withType && name == `HodgeFil1.ScholzeH1AbVarDR) then
        throwError "{root} depends on excluded Hodge input {name}"
      let some decl := env.find? name | throwError "missing dependency {name}"
      -- These two assemblers conclude the old row. Inspect their inputs and
      -- proof bodies without treating the stated conclusion as a premise.
      if name == `HodgeFil1.fil1_of_dR then
        todo := todo ++ (← collectInputs decl.type)
      else
        todo := todo ++ decl.type.getUsedConstants
      if let some value := decl.value? (allowOpaque := true) then
        todo := todo ++ value.getUsedConstants
    logInfo m!"{root}: checked {seen.size} transitive dependencies; no removed Picard hypothesis or Fil¹ input"

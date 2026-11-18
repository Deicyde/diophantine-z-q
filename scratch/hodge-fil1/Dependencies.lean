import ZInQKernel.Contrib.OneProof.HodgeFil1

open Lean Elab Command

/- For the two row assemblers, omit the root's type: its conclusion intentionally names
the original row. Inspect their proof values and both type and proof for every dependency.
For the pointwise Fil¹ proof, include the root type as well. -/
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  -- The proof terms of the assemblers can mention generated instance proofs from
  -- elaborating the row statements. Inspect their types and values like all other terms.
  let rowAuxiliary := fun (n : Name) =>
    n == `DeRhamScholze.HTMerge.ScholzeH1AbVar._proof_1 ||
    n == `DeRhamScholze.HTMerge.ScholzeH1AbSurf._proof_1
  let banned := fun (n : Name) =>
    ((`DeRhamScholze.HTMerge).isPrefixOf n && !rowAuxiliary n) ||
    (`DeRhamScholze.HTAbVar.HodgeNumberH1AbVar).isPrefixOf n ||
    (`DeRhamScholze.HTAbVar.hodgeTate01_dims).isPrefixOf n ||
    (`DeRhamScholze.HTAbVar.finrank_filD_dual).isPrefixOf n ||
    (`DeRhamScholze.HTAbVar.hodgeTateDecompAbVar_of_scholze).isPrefixOf n ||
    (`ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar).isPrefixOf n
  for (root, withType) in [
      (`HodgeFil1.finrank_fil1_of_dR_of_pairing, true),
      (`HodgeFil1.fil1_of_dR, false),
      (`HodgeFil1.fil1_surf_of_dR, false)] do
    let some ci := env.find? root | throwError "missing {root}"
    let some value := ci.value? (allowOpaque := true) | throwError "missing proof of {root}"
    let mut todo := value.getUsedConstants
    if withType then todo := todo ++ ci.type.getUsedConstants
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      if banned n then throwError "{root} depends on excluded declaration {n}"
      let some d := env.find? n | throwError "missing dependency {n}"
      if rowAuxiliary n then
        logInfo m!"{root}: inspected generated auxiliary {n} : {d.type}"
      todo := todo ++ d.type.getUsedConstants
      if let some v := d.value? (allowOpaque := true) then
        todo := todo ++ v.getUsedConstants
    logInfo m!"{root}: checked {seen.size} transitive dependencies; no clause-3 declaration"

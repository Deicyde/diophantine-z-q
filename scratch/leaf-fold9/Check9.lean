import ZInQKernel.OneProof.Main
/-! leaf-fold9 check: the conclusion is the kernel's `ZInQ.SixContactMin`, no `sorryAx` in the closure, and for
every field of the four bundles its head constant and the module that declares it. -/
open Lean Elab Command Meta

example : ∀ (r : HDec.HSyn.OpenResearchLeaves9) (t : HDec.HSyn.OpenTextbookLeaves9) (l : HDec.HSyn.OpenAddedLeaves8)
    (g : HDec.HSyn.OpenGlue7), _root_.ZInQ.SixContactMin := HDec.HSyn.sixContactMin_of_open9

#print axioms HDec.HSyn.sixContactMin_of_open9

run_cmd do
  let env ← getEnv
  -- closure
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[`HDec.HSyn.sixContactMin_of_open9]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in ci.type.getUsedConstants do todo := todo.push c
      if let some v := ci.value? (allowOpaque := true) then
        for c in v.getUsedConstants do todo := todo.push c
  logInfo m!"closure: {seen.size} constants; sorryAx in closure: {seen.contains ``sorryAx}"
  let mods := env.header.moduleNames
  let mut kcount : Nat := 0
  let mut total : Nat := 0
  for s in [`HDec.HSyn.OpenResearchLeaves9, `HDec.HSyn.OpenTextbookLeaves9, `HDec.HSyn.OpenAddedLeaves8,
      `HDec.HSyn.OpenGlue7] do
    let some info := getStructureInfo? env s | throwError "no structure {s}"
    let mut lines : Array String := #[]
    for f in info.fieldNames do
      let some proj := env.find? (s ++ f) | throwError "no projection {f}"
      -- field type: strip the structure argument
      let ty ← liftTermElabM <| forallTelescope proj.type fun _ b => pure b
      let head := (ty.getForallBody.getAppFn.constName?).getD (ty.getAppFn.constName?.getD `none)
      let hd := match ty.getAppFn.constName? with
        | some c => c
        | none => (ty.find? (fun e => e.isConst)).map (·.constName!) |>.getD `none
      let _ := head
      let m := match env.getModuleIdxFor? hd with
        | some i => mods[i.toNat]!
        | none => `none
      let isK := !((`ZInQKernel.OneProof).isPrefixOf m)
      if isK then kcount := kcount + 1
      total := total + 1
      lines := lines.push s!"{f} : {hd} [{m}]{if isK then " K" else ""}"
    logInfo m!"{s} ({info.fieldNames.size} fields)\n{String.intercalate "\n" lines.toList}"
  logInfo m!"fields: {total}; head constant declared outside ZInQKernel.OneProof: {kcount}"

-- the two Contrib proofs (cloud PR #11) and leaf-fold9's bridge theorems
#print axioms ZInQ.Contrib.CloudW07JacobiansCurves.JacobianExists_proof
#print axioms ZInQ.Contrib.CloudW07JacobiansCurves.NormalModelOfFunctionFieldQ_proof
#print axioms HDec.HSyn.r1rec_of_rep
#print axioms HDec.HSyn.r5fp_of_rep
#print axioms ModularSplit.deligneSerreConseq_of_ds
#print axioms ReductSplit.serreTatePotentialGood_final
#print axioms ReductSplit.grothendieckMonodromy_final'
#print axioms ZInQ.LeafFold9.fieldOfModuli3_le
#print axioms ZInQ.LeafFold9.residueImage_eq_fieldOfModuliPair
#print axioms ZInQ.LeafFold9.qmIso_of_isBaseChangeOfPair
-- the statements of the two derivations, in full
set_option pp.fullNames true in
#check @HDec.HSyn.r1rec_of_rep
set_option pp.fullNames true in
#check @HDec.HSyn.r5fp_of_rep

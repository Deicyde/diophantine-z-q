import ZInQKernel.OneProof.Main
import Lean
open Lean

def hfNames : List Name := [`HDec.FS5NoCM.comIntOrQuadOrder_of, `HDec.FS5NoCM.comIntOrQuadOrder_of_leaves, `HDec.FS5NoCM.comOfMatrixEnd0_of_homFree, `HDec.FS5NoCM.com_int_of_end0_quat, `HDec.FS5NoCM.fibreComTrivialFull_of_leaves', `HDec.FS5NoCM.fibreComTrivialFull_of_leaves'', `HDec.G0FibreSimple.centralizerOfMatrixEnd0_of_homFree, `HDec.G0FibreSimple.end0Division_of_homFree, `HDec.G0FibreSimple.fibreSimple_of_pieces', `HDec.G0FibreSimple.fibreSimple_of_pieces'', `HDec.G0Galois.g8, `HDec.G0Galois.g8_g11, `HDec.G0Galois.g8_g12, `HDec.G0ModField.KernelField.endEqOFibre_of, `HDec.G0ModField.KernelField.kernelFieldExists_of_leaves, `HDec.G0ModField.KernelField.kernelFieldExists_of_leaves_FS5, `HDec.G0ModField.KernelField.kernelFieldExists_of_pieces, `HDec.G0ModField.KernelField.kernelFieldExists_of_split, `HDec.G0ModField.KernelField.kernelFieldExists_of_split', `HDec.G0ModField.KernelField.kernelFieldExists_of_split'', `HDec.G0ModField.KernelField.kernelField_of_model, `HDec.G4WeilRes.homLattice_free, `HDec.G4WeilRes.inertiaFixesHomsMon, `HDec.G4WeilRes.inertiaFixesHomsMon_of_leaves, `HDec.G4WeilRes.tateHom_injective, `HDec.HSyn.OpenTextbookLeaves10.homFreeFiniteAlgClosed, `HDec.HSyn.OpenTextbookLeaves10.mk, `HDec.HSyn.OpenTextbookLeaves11.homFreeFiniteAlgClosed, `HDec.HSyn.OpenTextbookLeaves11.mk, `HDec.HSyn.OpenTextbookLeaves12.homFreeFiniteAlgClosed, `HDec.HSyn.OpenTextbookLeaves2.mk, `HDec.HSyn.OpenTextbookLeaves2.t6, `HDec.HSyn.OpenTextbookLeaves3.mk, `HDec.HSyn.OpenTextbookLeaves3.t6, `HDec.HSyn.OpenTextbookLeaves4.mk, `HDec.HSyn.OpenTextbookLeaves4.t6, `HDec.HSyn.OpenTextbookLeaves6.homFreeFiniteAlgClosed, `HDec.HSyn.OpenTextbookLeaves6.mk, `HDec.HSyn.OpenTextbookLeaves7.homFreeFiniteAlgClosed, `HDec.HSyn.OpenTextbookLeaves7.mk, `HDec.HSyn.OpenTextbookLeaves8.homFreeFiniteAlgClosed, `HDec.HSyn.OpenTextbookLeaves8.mk, `HDec.HSyn.OpenTextbookLeaves9.homFreeFiniteAlgClosed, `HDec.HSyn.OpenTextbookLeaves9.mk, `HDec.HSyn.TextbookLeaves.mk, `HDec.HSyn.TextbookLeaves.t6, `HDec.HSyn.linkedTateLocal_of_leaves3, `HDec.HSyn.qmEndRank_of_leaves3, `HDec.HSyn.t6_of_algClosed5, `HDec.LTGoodRed.QM.finrank_end0, `HDec.LTGoodRed.QM.finrank_le_baseChange, `HDec.LTGoodRed.QM.four_le_finrank, `HDec.LTGoodRed.QM.qmEndRank_of, `HDec.LTGoodRed.QM.qmEndRank_of_leaves, `HDec.LTGoodRed.QM.qmSplitCaseRank, `PkgI3.C2_absolutelyIrreducible, `PkgI3.finrank_equivEnd, `ZInQ.Contrib.AVB1.homFreeFinite_of_algClosed]

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[`ZInQ.OneProof.frozenTarget]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ccValue? ci then todo := todo ++ v.getUsedConstants
  for c in seen.toList do
    if let some ci := env.find? c then
      if let some v := ccValue? ci then
        let used := v.getUsedConstants
        let hits := hfNames.filter (fun n => used.contains n)
        if !hits.isEmpty then
          IO.println s!"CALLER {c} USES {hits}"

#check @HDec.FS5NoCM.comIntOrQuadOrder_of
#check @HDec.FS5NoCM.comIntOrQuadOrder_of_leaves
#check @HDec.FS5NoCM.comOfMatrixEnd0_of_homFree
#check @HDec.FS5NoCM.com_int_of_end0_quat
#check @HDec.FS5NoCM.fibreComTrivialFull_of_leaves'
#check @HDec.FS5NoCM.fibreComTrivialFull_of_leaves''
#check @HDec.G0FibreSimple.centralizerOfMatrixEnd0_of_homFree
#check @HDec.G0FibreSimple.end0Division_of_homFree
#check @HDec.G0FibreSimple.fibreSimple_of_pieces'
#check @HDec.G0FibreSimple.fibreSimple_of_pieces''
#check @HDec.G0Galois.g8
#check @HDec.G0Galois.g8_g11
#check @HDec.G0Galois.g8_g12
#check @HDec.G0ModField.KernelField.endEqOFibre_of
#check @HDec.G0ModField.KernelField.kernelFieldExists_of_leaves
#check @HDec.G0ModField.KernelField.kernelFieldExists_of_leaves_FS5
#check @HDec.G0ModField.KernelField.kernelFieldExists_of_pieces
#check @HDec.G0ModField.KernelField.kernelFieldExists_of_split
#check @HDec.G0ModField.KernelField.kernelFieldExists_of_split'
#check @HDec.G0ModField.KernelField.kernelFieldExists_of_split''
#check @HDec.G0ModField.KernelField.kernelField_of_model
#check @HDec.G4WeilRes.homLattice_free
#check @HDec.G4WeilRes.inertiaFixesHomsMon
#check @HDec.G4WeilRes.inertiaFixesHomsMon_of_leaves
#check @HDec.G4WeilRes.tateHom_injective
#check @HDec.HSyn.linkedTateLocal_of_leaves3
#check @HDec.HSyn.qmEndRank_of_leaves3
#check @HDec.HSyn.t6_of_algClosed5
#check @HDec.LTGoodRed.QM.finrank_end0
#check @HDec.LTGoodRed.QM.finrank_le_baseChange
#check @HDec.LTGoodRed.QM.four_le_finrank
#check @HDec.LTGoodRed.QM.qmEndRank_of
#check @HDec.LTGoodRed.QM.qmEndRank_of_leaves
#check @HDec.LTGoodRed.QM.qmSplitCaseRank
#check @PkgI3.C2_absolutelyIrreducible
#check @PkgI3.finrank_equivEnd
#check @ZInQ.Contrib.AVB1.homFreeFinite_of_algClosed

import ZInQKernel.OneProof.Main
import Lean
/-! charpoly-hf fold check. Run in a copy of the tree after `python3 scratch/charpoly-hf/fold_edit.py --tree <copy>`
and `lake build ZInQKernel.OneProof.Main` there. Against the unfolded tree the first `run_cmd` fails by design (the
field is still there).

1. `HDec.HSyn.OpenTextbookLeaves15` (the textbook bundle of `ZInQ.OneProof.frozenTarget`) has no field
   `charPolyIndepOfEllAlgClosed`, and has `homFreeFiniteAlgClosedCharP`;
2. the closure of `ZInQ.OneProof.frozenTarget` contains none of `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed`,
   `PkgI3.CharPolyIndepOfEll`, `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed`, `PkgI3.HomFreeFinite`,
   `HomFreeFiniteAlgClosedNoEmb`, `sorryAx`, nor any constant whose last component is `CharPolyIndepOfEll` or
   `CharPolyIndepOfEllAlgClosed`; it contains `CharpolyHF.HomFreeFiniteAlgClosedCharP` and
   `CharpolyHF.MinpolyIndepOfEllCharP`;
3. the blueprint target `HDec.HSyn.OpenTextbookLeaves13.charPolyIndepOfEllAlgClosed` still exists (off the route);
4. `frozenTarget` depends only on `propext`, `Classical.choice`, `Quot.sound`. -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

def isTgt (n : Name) : Bool :=
  match n with
  | .str _ s => s == "CharPolyIndepOfEll" || s == "CharPolyIndepOfEllAlgClosed"
  | _ => false

run_cmd do
  let env ← getEnv
  if env.contains `HDec.HSyn.OpenTextbookLeaves15.charPolyIndepOfEllAlgClosed then
    throwError "the field charPolyIndepOfEllAlgClosed is still present"
  unless env.contains `HDec.HSyn.OpenTextbookLeaves15.homFreeFiniteAlgClosedCharP do
    throwError "the field homFreeFiniteAlgClosedCharP is missing"
  logInfo "OpenTextbookLeaves15: no field charPolyIndepOfEllAlgClosed; field homFreeFiniteAlgClosedCharP present"
  unless env.contains `HDec.HSyn.OpenTextbookLeaves13.charPolyIndepOfEllAlgClosed do
    throwError "the blueprint target OpenTextbookLeaves13.charPolyIndepOfEllAlgClosed was deleted"
  logInfo "blueprint target HDec.HSyn.OpenTextbookLeaves13.charPolyIndepOfEllAlgClosed still exists"
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
  let banned : List Name := [`ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed, `PkgI3.CharPolyIndepOfEll,
    `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed, `PkgI3.HomFreeFinite,
    `ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteAlgClosedNoEmb, `sorryAx,
    `HDec.HSyn.OpenTextbookLeaves13.charPolyIndepOfEllAlgClosed, `HDec.HSyn.t7_of_algClosed5]
  let hitsB := banned.filter seen.contains
  let hits := seen.toList.filter isTgt
  logInfo s!"closure size {seen.size}; banned constants in the closure: {hitsB}; T7-named constants: {hits}"
  unless hits.isEmpty && hitsB.isEmpty do throwError "T7, T6 or the field is still in the closure"
  let want : List Name := [`ZInQ.Contrib.OneProof.CharpolyHF.HomFreeFiniteAlgClosedCharP,
    `ZInQ.Contrib.OneProof.CharpolyHF.MinpolyIndepOfEllCharP,
    `HDec.HSyn.G0AssembleMod.linkedTateData_of_local_minpolyCharP, `R16Split.r16_of_printedC]
  logInfo s!"present in the closure: {want.filter seen.contains}"

#print HDec.HSyn.OpenTextbookLeaves15
#check @ZInQ.OneProof.frozenTarget
#print axioms ZInQ.OneProof.frozenTarget

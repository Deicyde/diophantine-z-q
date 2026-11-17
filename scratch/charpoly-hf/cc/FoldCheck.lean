import ZInQKernel.OneProof.Main
import Lean
/-! charpoly-charp fold check. Run in a copy of the tree after `scratch/charpoly-charp/fold_edit.py --tree <copy>`
and `lake build ZInQKernel.OneProof.Main` there (this file does not compile against the unfolded tree: the
`run_cmd` below fails while the field exists).

1. `HDec.HSyn.OpenTextbookLeaves13` (the top textbook bundle of `ZInQ.OneProof.frozenTarget`) has no field
   `charPolyIndepOfEllAlgClosed`;
2. the closure of `ZInQ.OneProof.frozenTarget` contains no constant named `CharPolyIndepOfEll` or
   `CharPolyIndepOfEllAlgClosed` (neither T7 nor the field is used anywhere in the proof);
3. `frozenTarget` depends only on `propext`, `Classical.choice`, `Quot.sound`. -/
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
  if env.contains `HDec.HSyn.OpenTextbookLeaves13.charPolyIndepOfEllAlgClosed then
    throwError "the field charPolyIndepOfEllAlgClosed is still present"
  logInfo "OpenTextbookLeaves13 has no field charPolyIndepOfEllAlgClosed"
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
  let hits := seen.toList.filter isTgt
  logInfo s!"closure size {seen.size}; T7 / field constants in the closure: {hits}"
  unless hits.isEmpty do throwError "T7 or the field is still in the closure"

#print HDec.HSyn.OpenTextbookLeaves13
#print axioms ZInQ.OneProof.frozenTarget

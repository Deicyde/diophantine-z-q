import ZInQKernel.OneProof.Main
import Lean
/-! theta-fold: declarations of `ZInQKernel.Contrib.OneProof.LinYang*` outside the dependency closure of the roots
(frozenTarget and the Route 1 theorems kept for reference). A declaration counts as used if it, or a used constant
having it as a name prefix, is reached. Writes `MODULE START END NAME` lines (docstring included) to
scratch/theta-fold/dead.txt. -/
open Lean Elab Command

def roots : List Name := [`ZInQ.OneProof.frozenTarget,
  `HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal.thetaPointOfFibre_of_printedAll,
  `HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal.thetaPointOfFibre_of_printed,
  `HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal.thetaRatiosAtQM_of_printed,
  `HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal.qmThetaSymmetricCurve_iff,
  `HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal.thetaEightSquare_iff]

def modOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.modules[i.toNat]!.module

def isNewMod (m : Name) : Bool := (`ZInQKernel.Contrib.OneProof).isPrefixOf m && (m.toString.splitOn "LinYang").length > 1

run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := roots.toArray
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then todo := todo ++ v.getUsedConstants
      if let .inductInfo iv := ci then todo := todo ++ iv.ctors.toArray
  let mut out : Array String := #[]
  for (n, _) in env.constants.map₁.toList do
    let some m := modOf env n | continue
    if !isNewMod m then continue
    if n.isInternalDetail then continue
    if seen.contains n then continue
    -- used if some used constant has n as a prefix (auxiliary/equation lemmas, structure projections)
    if seen.toList.any (fun s => n.isPrefixOf s) then continue
    let r? ← liftTermElabM <| findDeclarationRanges? n
    match r? with
    | some r => out := out.push s!"{m} {r.range.pos.line} {r.range.endPos.line} {n}"
    | none => out := out.push s!"{m} ? ? {n}"
  IO.FS.writeFile "scratch/theta-fold/dead.txt" ("\n".intercalate (out.qsort (· < ·)).toList ++ "\n")
  logInfo m!"DEAD {out.size} of closure {seen.size}"

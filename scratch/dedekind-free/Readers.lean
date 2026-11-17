import ZInQKernel.OneProof.Main
import Lean
/-! dedekind-free: readers of the Néron existence statements in the closure of `ZInQ.OneProof.frozenTarget`.
Prints every declaration of the closure whose *type* mentions one of the watched statements (a consumer that
takes it as a hypothesis, or a producer that concludes it). -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

run_cmd do
  let env ← getEnv
  let watch : List Name := [
    `ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind,
    `ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDVR,
    `ZInQ.Contrib.GroupLawNeron.NeronGoodModelIso,
    `ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR,
    `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists,
    `ZInQ.H5Neron.NeronModelExists,
    `GapNeron.NeronSchemeModelExistsDVRNF,
    `ReductSplit.NeronSchemeModelExistsDVR]
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
  IO.println s!"frozenTarget: closure {seen.size}"
  for w in watch do
    IO.println s!"== {w} in closure: {seen.contains w}"
    for c in seen.toList do
      if let some ci := env.find? c then
        if !(c.isInternal) && ci.type.getUsedConstants.contains w then
          IO.println s!"   {c}"

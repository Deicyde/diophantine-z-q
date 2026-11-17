import ZInQKernel.OneProof.Main
import Lean
/-! group-law: who in `frozenTarget`'s closure uses the group-law leaf, and are the sites N1/N2 still there. -/
open Lean

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
  let targets : List Name := [`ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw,
      `LeafQM.AV.R1UnivRigid.QMFamilyGroupLaw, `LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw,
      `LeafQM.AV.R1UnivRigid.r1fpProps_eq_ab_gl, `LeafQM.AV.R1UnivRigid.r1univProps_of_ab_gl,
      `LeafQM.AV.R1UnivRigid.exists_qmAbScheme_gl]
  for n in targets ++ [`HDec.ModelGlue.exists_genFib_to_Y, `MCRGlue.QuotientP1Coordinate,
      `MCRGlue.modelCoordinateResidue_of_quotient', `HDec.ModelGlue.heckeVertWitness_of_curveBijIso] do
    logInfo m!"{n}: {if seen.contains n then "IN closure" else "not in closure"}"
  -- direct users of the targets inside the closure
  for c in seen.toList do
    if let some ci := env.find? c then
      let used := ci.type.getUsedConstants ++ ((ccValue? ci).map (·.getUsedConstants)).getD #[]
      let hits := targets.filter (fun t => used.contains t)
      if !hits.isEmpty && !targets.contains c then
        logInfo m!"USER {c} uses {hits}"

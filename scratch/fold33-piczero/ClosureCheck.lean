import ZInQKernel.OneProof.Main
import Lean
/-! fold33-piczero: the closure (types and values) of `ZInQ.OneProof.frozenTarget` must not contain the general-field
statements `T09Pic.PicZeroAbVar`, `PicDict.PicZeroSmooth`, `PicFix.MumfordKLFiniteSectionAC`, `T09Pic.PhiAmpleIsogeny`,
the old `HDec.WeilPairing.T09_SymmIsogenyExists` / `LeafPush.T09_WeilPairing` hypotheses, `G12Det`, the originals of the
added chain, or `sorryAx`; it must contain the characteristic-`0` forms and the GM copies (from piczero-char0's and
fold33-copy's ClosureCheck.lean). Also lists the fields of frozenTarget's bundle binders. -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

run_cmd do
  let env ← getEnv
  let names : List Name := [
    -- must be absent
    `T09Pic.PicZeroAbVar, `PicDict.PicZeroSmooth, `PicFix.MumfordKLFiniteSectionAC,
    `T09Pic.PhiAmpleIsogeny, `HDec.WeilPairing.T09_SymmIsogenyExists, `LeafPush.T09_WeilPairing,
    `HDec.LeafPush.T09_WeilPairing, `HDec.G0Galois.G12Det, `sorryAx,
    `HDec.HSyn.OpenAddedLeaves20, `HDec.HSyn.sixContactMin_of_open43, `HDec.HSyn.sixContactMin_of_open41,
    `HDec.HSyn.OpenResearchLeaves29, `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed, `PkgI3.HomFreeFinite,
    `DictModels.MumfordConn.MumfordGroupLawConn, `CToPrinted.SGA3_VIB_3_10, `SGA3IdComp.SGA3_VIB_3_10_Nbhd,
    -- must be present
    `PicZeroChar0.PicZeroAbVar0, `PicZeroChar0.picZeroAbVar0_of_leaves, `PicZeroChar0.T09_SymmIsogenyExists0,
    `PicZeroChar0.PhiAmpleIsogeny0, `PicZeroChar0.MumfordKLFiniteSectionAC0,
    `PicDict.PicLocFinType, `PicDict.IdentityComponentLFT, `PicFix.KleimanPicZeroProper,
    `ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof,
    `HDec.HSyn.OpenAddedLeaves20PZ, `HDec.HSyn.sixContactMin_of_open43_pz, `HDec.HSyn.sixContactMin_of_open44,
    `HDec.HSyn.OpenResearchLeaves29GM, `HDec.HSyn.OpenAddedLeaves21]
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
  for b in names do
    IO.println s!"  contains {b}: {seen.contains b}"
  if let some ci := env.find? `ZInQ.OneProof.frozenTarget then
    let bs := ci.type.getUsedConstants.filter fun n =>
      (isStructure env n) && (n.toString.startsWith "HDec.HSyn.Open")
    for b in bs do
      let fs := getStructureFields env b
      IO.println s!"  bundle {b}: {fs.size} fields: {fs.toList}"

import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.PicZeroAbVarCharZeroReroute
import Lean
/-! piczero-char0: the closure (values and types) of `sixContactMin_of_open41_pz` must not contain the general-field
statements `T09Pic.PicZeroAbVar`, `PicDict.PicZeroSmooth`, `PicFix.MumfordKLFiniteSectionAC`, the old
`HDec.WeilPairing.T09_SymmIsogenyExists` / `LeafPush.T09_WeilPairing` hypotheses, or `sorryAx`; it should contain
`PicZeroChar0.PicZeroAbVar0`. (adapted from homfree-noemb's ClosureCheck.lean) -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

run_cmd do
  let env ← getEnv
  let bad : List Name := [`T09Pic.PicZeroAbVar, `PicDict.PicZeroSmooth, `PicFix.MumfordKLFiniteSectionAC,
    `T09Pic.PhiAmpleIsogeny, `HDec.WeilPairing.T09_SymmIsogenyExists, `LeafPush.T09_WeilPairing, `HDec.LeafPush.T09_WeilPairing, `sorryAx,
    `HDec.G0Galois.G12Det, `PicZeroChar0.PicZeroAbVar0, `PicZeroChar0.T09_SymmIsogenyExists0,
    `PicZeroChar0.PhiAmpleIsogeny0, `PicZeroChar0.MumfordKLFiniteSectionAC0]
  for top in [`HDec.HSyn.sixContactMin_of_open41_pz, `HDec.HSyn.sixContactMin_of_open41] do
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[top]
    while !todo.isEmpty do
      let c := todo.back!
      todo := todo.pop
      if seen.contains c then continue
      seen := seen.insert c
      if let some ci := env.find? c then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := ccValue? ci then todo := todo ++ v.getUsedConstants
    IO.println s!"{top}: closure {seen.size}"
    for b in bad do
      IO.println s!"  contains {b}: {seen.contains b}"

import ZInQKernel.OneProof.Main
/-! igusa-drop: closure check of the folded frozen target (copied from fold-b105). The removed Props must not occur in
the closure (types and values) of `ZInQ.OneProof.frozenTarget`, nor `sorryAx`; the hypotheses of frozenTarget are
printed by `#check`. -/

#print axioms ZInQ.OneProof.frozenTarget
#check @ZInQ.OneProof.frozenTarget

open Lean in
def fcValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

open Lean in
run_cmd do
  let env ← getEnv
  let closure : Name → NameSet := fun root => Id.run do
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[root]
    while !todo.isEmpty do
      let c := todo.back!
      todo := todo.pop
      if seen.contains c then continue
      seen := seen.insert c
      if let some ci := env.find? c then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := fcValue? ci then todo := todo ++ v.getUsedConstants
    return seen
  let checked : List Name := [`sorryAx,
    -- removed (must be false)
    `X1Igusa.IgusaGL2DSGalSome, `X1Igusa.igusaGL2DS_of_igusaGL2DSGalSome, `X1Igusa.IgusaGL2DS,
    `X1Igusa.x1PointsConjugate_of_igusaGL2DS, `AfTateLam.r16CoreY_of_ds965, `AfTateLam.r16CoreY_of_printed,
    `HDec.HSyn.OpenResearchLeaves52, `HDec.HSyn.sixContactMin_of_open71,
    -- the replacement route (must be true)
    `AfTateLam.r16CoreY_of_ds965_x0, `AfTateLam.x1PointsConjugate_proof, `FltCqj2.x0Transitive_proof,
    `ZInQ.RLeaf.igusaTransitive_iff_x0Transitive, `HDec.HSyn.OpenResearchLeaves53, `HDec.HSyn.sixContactMin_of_open72]
  for root in [`ZInQ.OneProof.frozenTarget] do
    let s := closure root
    IO.println s!"{root}: closure {s.size}"
    for b in checked do
      IO.println s!"  contains {b}: {s.contains b}"

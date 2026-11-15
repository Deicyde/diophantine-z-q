import ZInQKernel.Contrib.OneProof.CMStab
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut n := 0
  for (c, _) in env.constants.toList do
    if (`HDec.LeafQM).isPrefixOf c || (`HDec.QML3).isPrefixOf c || (`HDec.M3).isPrefixOf c || (`HDec.Qbar).isPrefixOf c
       || (`HDec.HasCM4).isPrefixOf c || (`HDec.HasCM3).isPrefixOf c || (`HDec.HasCM24).isPrefixOf c
       || (`HDec.MCRQuot.QML3).isPrefixOf c || (`HDec.MCRQuot.M3).isPrefixOf c || (`HDec.MCRQuot.Qbar).isPrefixOf c then
      n := n + 1
      if n < 20 then IO.println c
  IO.println s!"count {n}"
set_option linter.ambiguousOpen false
namespace HDec
namespace MCRQuot
open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3
def CMStabObjWeakT : Prop :=
  ∀ P : QML3 Qbar, (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) →
    ∃ (α : LeafQM.O ≃+* LeafQM.O) (u : (LeafQM.O)ˣ),
      M3.twist α (M3.rightMul u (M3.mk P)) = M3.mk P ∧
      ∃ m : M3 Qbar, M3.twist α (M3.rightMul u m) ≠ m
set_option pp.fullNames true in
#print CMStabObjWeakT
set_option pp.fullNames true in
#print GapGlue.CMStabObjWeak
example : CMStabObjWeakT = GapGlue.CMStabObjWeak := rfl
example : CMStabObjWeakT = GapGlue.CMStabObjWeak := by unfold CMStabObjWeakT GapGlue.CMStabObjWeak; rfl
end MCRQuot
end HDec

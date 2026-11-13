/-! # lt-local, part 6 (GluePieces4 variant): `LinkedTateLocal` itself, over g0-assemble3's `G7Data`

Compiled only in the variant `LtLocal4.lean` (`build4.sh`), whose base `Base4.lean` is
`Base.lean` with g0-assemble3's fix of `G0ModField.G7Data` (the clause `[L:ℚ] ≤ D` appended,
`scratch/g0-assemble3/parts/75_modfield.lean`) and its three proof adjustments, ported by
`mk_base4.py`. Over that `G7Data`, `G7DegreeBound` is a projection, and g0-assemble2's
`LinkedTateLocal` (GLUE field 39, statement unchanged) is proved. -/

noncomputable section

namespace LTLocal

open CategoryTheory AlgebraicGeometry
open G0ModField

/-- **`G7DegreeBound` over g0-assemble3's `G7Data` (proved: its last clause).** -/
theorem g7DegreeBound_gp4 : G7DegreeBound := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD
  exact hD.2.2.2.2.2.2.2.2.2.2.2.2

/-- **g0-assemble2's `LinkedTateLocal` (GLUE field 39), over g0-assemble3's `G7Data` (proved)**
from the leaves R6 and I2-Tors, local-glue's textbook Prop `UnramRoots` at `p = 2` for `ℓ = 5, 3`,
g14-trace's glue `TateBridge35`, g0-split's `FibreSimple` and linked-tate's `QMEndRank`. -/
theorem linkedTateLocal_of_tateBridge35 (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU5 : G15Ram.UnramRoots 2 5)
    (hU3 : G15Ram.UnramRoots 2 3) (hB : G14Bridge.TateBridge35)
    (hFS : HSyn.G0Split.FibreSimple) (hR : HSyn.LinkedTate.QMEndRank) :
    HSyn.G0AssembleMod.LinkedTateLocal :=
  linkedTateLocal_of_D (linkedTateLocalD_of_tateBridge35' hR6 hTors hU5 hU3 hB hFS hR)
    g7DegreeBound_gp4

/-- The same with `TateBridge35` from frob-trace's reduction (`FrobTrace.tateBridge35_of_algFrobRed`:
the leaf I3.M0 `PkgI3.TateModuleFree` and the glue `FrobTrace.AlgFrobRed`). -/
theorem linkedTateLocal_of_algFrobRed (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU5 : G15Ram.UnramRoots 2 5)
    (hU3 : G15Ram.UnramRoots 2 3) (hT : PkgI3.TateModuleFree) (hA : FrobTrace.AlgFrobRed)
    (hFS : HSyn.G0Split.FibreSimple) (hR : HSyn.LinkedTate.QMEndRank) :
    HSyn.G0AssembleMod.LinkedTateLocal :=
  linkedTateLocal_of_tateBridge35 hR6 hTors hU5 hU3 (FrobTrace.tateBridge35_of_algFrobRed hT hA)
    hFS hR

end LTLocal

end

#print axioms LTLocal.g7DegreeBound_gp4
#print axioms LTLocal.linkedTateLocal_of_tateBridge35
#print axioms LTLocal.linkedTateLocal_of_algFrobRed

import ZInQKernel.Contrib.CloudB3W13.Dictionary.D5.Transport

/-! A faithful regression check of Assembly's explicit transport. The genuine
abelian variety has carrier `Over.mk P.A.X.hom` behind a definition, exactly as
`abVarOfFakeEC` does. This file is not imported by production. -/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.TransportCheck

open CategoryTheory AlgebraicGeometry PkgI3 LeafQM
open ZInQ.Contrib.CloudB2Shimura.Dictionary.D5

variable {K : Type} [Field K]

/-- A genuine kernel abelian variety with the hidden carrier used by Assembly. -/
def hiddenCarrier (P : AV.QML3 K) (g : GrpObj (Over.mk P.A.X.hom)) : AbVar K where
  X := Over.mk P.A.X.hom
  grp := g
  proper := P.A.proper
  smooth := P.A.smooth
  geomInt := P.A.geomInt

/-- The full dependent packaging shape on Assembly's actual hidden carrier. -/
theorem fixed_carrier (P : AV.QML3 K) (g : GrpObj (Over.mk P.A.X.hom))
    (hg : g = (show GrpObj (Over.mk P.A.X.hom) from P.A.grp)) :
    let B : AbVar K := hiddenCarrier P g
    ∃ (hs : B.dim = 2) (q : AV.QMStr B) (e : AV.Level3 q),
      (∀ a : O, (q.iota a).hom.left = (P.q.iota a).hom.left) ∧
      (∀ a : O, (Additive.toMul (e.eta a)).left = (Additive.toMul (P.e.eta a)).left) ∧
      Nonempty (AV.QML3.Iso ⟨B, hs, q, e⟩ P) := by
  let B : AbVar K := hiddenCarrier P g
  have hA : B = P.A := by
    cases hg
    rfl
  refine ⟨surfaceOfEq P B hA, qmOfEq P B hA, levelOfEq P B hA, ?_, ?_, ?_⟩
  · intro a
    have hi : ((qmOfEq P B hA).iota a).hom = (P.q.iota a).hom := by
      refine (qmOfEq_hom P B hA (show B.X = P.A.X from rfl) a).trans ?_
      erw [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact congrArg CommaMorphism.left hi
  · intro a
    have he : Additive.toMul ((levelOfEq P B hA).eta a) =
        Additive.toMul (P.e.eta a) := by
      refine (levelOfEq_pt P B hA (show B.X = P.A.X from rfl) a).trans ?_
      erw [eqToHom_refl, Category.comp_id]
    exact congrArg CommaMorphism.left he
  · exact ⟨objectOfEq_iso P B hA⟩

#print axioms fixed_carrier

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.TransportCheck

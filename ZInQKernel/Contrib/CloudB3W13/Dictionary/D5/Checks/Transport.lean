import ZInQKernel.Contrib.CloudB3W13.Dictionary.D5.Transport

/-! A regression check of the Assembly's explicit transport on genuine kernel
abelian varieties with the same carrier. This file is not imported by production. -/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.TransportCheck

open CategoryTheory AlgebraicGeometry PkgI3 LeafQM
open ZInQ.Contrib.CloudB2Shimura.Dictionary.D5

variable {K : Type} [Field K]

/-- The full carrier-dependent packaging shape, with no goal-wide rewrite. -/
theorem fixed_carrier (P : AV.QML3 K) (g : GrpObj P.A.X) (hg : g = P.A.grp) :
    let B : AbVar K :=
      { X := P.A.X
        grp := g
        proper := P.A.proper
        smooth := P.A.smooth
        geomInt := P.A.geomInt }
    ∃ (hs : B.dim = 2) (q : AV.QMStr B) (e : AV.Level3 q),
      (∀ a : O, (q.iota a).hom.left = (P.q.iota a).hom.left) ∧
      (∀ a : O, (Additive.toMul (e.eta a)).left = (Additive.toMul (P.e.eta a)).left) ∧
      Nonempty (AV.QML3.Iso ⟨B, hs, q, e⟩ P) := by
  let B : AbVar K :=
    { X := P.A.X
      grp := g
      proper := P.A.proper
      smooth := P.A.smooth
      geomInt := P.A.geomInt }
  have hA : B = P.A := by
    cases hg
    rfl
  refine ⟨surfaceOfEq P B hA, qmOfEq P B hA, levelOfEq P B hA, ?_, ?_, ?_⟩
  · intro a
    have hi : ((qmOfEq P B hA).iota a).hom = (P.q.iota a).hom := by
      simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
        (qmOfEq_hom P B hA (show B.X = P.A.X from rfl) a)
    exact congrArg CommaMorphism.left hi
  · intro a
    have he : Additive.toMul ((levelOfEq P B hA).eta a) =
        Additive.toMul (P.e.eta a) := by
      simpa only [eqToHom_refl, Category.comp_id] using
        (levelOfEq_pt P B hA (show B.X = P.A.X from rfl) a)
    exact congrArg CommaMorphism.left he
  · exact ⟨objectOfEq_iso P B hA⟩

#print axioms fixed_carrier

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.TransportCheck

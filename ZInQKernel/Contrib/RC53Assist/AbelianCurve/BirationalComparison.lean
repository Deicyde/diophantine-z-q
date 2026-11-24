import ZInQKernel.Contrib.RC53Assist.AbelianCurve.DifferentialLine
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-!
# Comparing proper regular curves through their function fields

The extension of a rational map is proved from the valuative criterion, not
assumed as a printed input. An integral source whose local rings are valuation
rings and a proper target suffice. Applying this in both directions extends
a rational function-field isomorphism to an isomorphism of schemes over the
rationals. On the generic point the isomorphism induces the specified map,
not merely some isomorphism of abstract schemes.

The local extension argument follows
`ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/AlgebraicGeometry/Birational/ValuativeExtension.lean`.
Mathematical locator: Milne, manuscript bibitem `milne-av`, I, Theorem 3.1,
printed pp. 16–17, including its valuative-criterion proof; the paragraph on
birational equivalence on printed p. 19. No printed proposition is assumed.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AbelianCurve

open AlgebraicGeometry CategoryTheory Limits

/-- DEFINITION. The canonical map from the spectrum of the actual function field to the
integral scheme. Locator: Mathlib, `Scheme.fromSpecStalk` at `genericPoint`. -/
abbrev fromFunctionField (X : Scheme.{0}) [IsIntegral X] : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

/-- THEOREM (proved). The structure morphism of the spectrum of the function field is the
spectrum of its ground-field algebra map.
Locator: `TauCeti/AlgebraicGeometry/Scheme/BaseAlgebra.lean`,
`Scheme.fromSpecStalk_genericPoint_comp_over`, and naturality of `Scheme.toSpecΓ`. -/
theorem fromFunctionField_structure {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) :
    letI := functionFieldAlgebra f
    fromFunctionField X ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℚ X.functionField)) := by
  letI := functionFieldAlgebra f
  have hbase : f = X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (globalFunctionsMap f)) := by
    have hring : CommRingCat.ofHom (globalFunctionsMap f) =
        (Scheme.ΓSpecIso (.of ℚ)).inv ≫ f.appTop := rfl
    rw [hring, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
      ← SpecMap_ΓSpecIso_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.comp_id]
  rw [hbase, ← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext_rat _ _)

/-- THEOREM (proved). A homomorphism of the actual function fields gives a generic-point map
over the rational base: every ring homomorphism preserves the rational scalars.
Locator: `fromFunctionField_structure` and Mathlib, `RingHom.ext_rat`. -/
theorem functionFieldMap_over {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of ℚ)) (g : Y ⟶ Spec (.of ℚ)) (e : Y.functionField →+* X.functionField) :
    (Spec.map (CommRingCat.ofHom e) ≫ fromFunctionField Y) ≫ g =
      fromFunctionField X ≫ f := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  rw [Category.assoc, fromFunctionField_structure, fromFunctionField_structure, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext_rat _ _)

/-- THEOREM (proved). An integral scheme with valuation local rings admits extension of every
generic-point map to a proper rational scheme, with the base and generic-point squares intact.
Locator: Milne I.3.1, pp. 16–17; the vendored Jacobian library,
`AlgebraicGeometry/Birational/ValuativeExtension.lean`, `Scheme.exists_hom_of_valuationRing_stalk`.
Only Mathlib's valuative criterion and spreading out are used. -/
theorem extend_from_valuation_stalks {X Y : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) (g : Y ⟶ Spec (.of ℚ)) [IsProper g]
    (hv : ∀ x : X, ValuationRing (X.presheaf.stalk x))
    (a : Spec X.functionField ⟶ Y) (ha : a ≫ g = fromFunctionField X ≫ f) :
    ∃ b : X ⟶ Y, b ≫ g = f ∧ fromFunctionField X ≫ b = a := by
  letI : X.Over (Spec (.of ℚ)) := ⟨f⟩
  letI : Y.Over (Spec (.of ℚ)) := ⟨g⟩
  haveI : IsSeparated (Y ↘ Spec (.of ℚ)) := inferInstanceAs (IsSeparated g)
  haveI : Y.IsSeparated := ⟨by rw [← terminal.comp_from g]; infer_instance⟩
  let r : X.RationalMap Y := Scheme.RationalMap.ofFunctionField f g a ha
  have hr : r.fromFunctionField = a := Scheme.RationalMap.fromFunctionField_ofFunctionField _ _ _ _
  have hfull : r.domain = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    haveI : IsDomain (X.presheaf.stalk x) := inferInstance
    haveI := hv x
    have hsquare : CommSq a
        (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)))
        g (X.fromSpecStalk x ≫ f) := ⟨by
      rw [ha, ← Category.assoc]
      congr 1
      exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)).symm⟩
    have hex : ValuativeCriterion.Existence g :=
      (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed g)).1
    obtain ⟨⟨l, hl, hlg⟩⟩ := hex
      { R := X.presheaf.stalk x, domain := inferInstance, K := X.functionField,
        i₁ := a, i₂ := X.fromSpecStalk x ≫ f, commSq := hsquare }
    let p := Scheme.PartialMap.ofFromSpecStalk f g l (by rw [hlg])
    have hx : x ∈ p.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
    refine Scheme.RationalMap.mem_domain.mpr
      ⟨p, hx, Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_⟩
    rw [hr, Scheme.RationalMap.fromFunctionField_toRationalMap]
    refine Eq.trans ?_ hl
    have hp : p.fromSpecStalkOfMem hx = l :=
      Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk f g l (by rw [hlg])
    change _ = _ ≫ l
    rw [← hp]
    simp only [Scheme.PartialMap.fromFunctionField, Scheme.PartialMap.fromSpecStalkOfMem,
      ← Category.assoc]
    congr 1
    rw [← cancel_mono p.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι]
    exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)).symm
  let p := r.toPartialMap
  have hp : p.domain = ⊤ := hfull
  haveI : IsIso p.domain.ι := by
    have htop {U : X.Opens} (h : U = ⊤) : IsIso U.ι := by
      subst h
      exact ⟨⟨X.topIso.inv, X.ι_toIso_inv, X.toIso_inv_ι⟩⟩
    exact htop hp
  haveI : r.IsOver (Spec (.of ℚ)) := by
    rw [Scheme.RationalMap.isOver_iff]
    exact ((Scheme.RationalMap.equivFunctionField f g) ⟨a, ha⟩).2
  have hpg : p.hom ≫ g = p.domain.ι ≫ f := Scheme.PartialMap.isOver_iff.mp inferInstance
  refine ⟨inv p.domain.ι ≫ p.hom, ?_, ?_⟩
  · rw [Category.assoc, hpg, IsIso.inv_hom_id_assoc]
  · have hη : genericPoint X ∈ p.domain := hp ▸ trivial
    have hηi : fromFunctionField X ≫ inv p.domain.ι =
        p.domain.fromSpecStalkOfMem (genericPoint X) hη := by
      rw [IsIso.comp_inv_eq, Scheme.Opens.fromSpecStalkOfMem_ι]
    rw [← Category.assoc, hηi, ← hr, ← r.toRationalMap_toPartialMap,
      Scheme.RationalMap.fromFunctionField_toRationalMap]
    rfl

/-- THEOREM (proved). Two maps over the rationals into a separated scheme agree if they agree
on the actual generic point. Locator: Mathlib, `ext_of_isDominant_of_isSeparated'`;
Tau Ceti, `isDominant_fromSpecStalk_genericPoint`. -/
theorem eq_of_generic_agreement {X Y : Scheme.{0}} [IsIntegral X]
    (sX : X ⟶ Spec (.of ℚ)) (sY : Y ⟶ Spec (.of ℚ)) [IsSeparated sY]
    (f g : X ⟶ Y) (hf : f ≫ sY = sX) (hg : g ≫ sY = sX)
    (h : fromFunctionField X ≫ f = fromFunctionField X ≫ g) : f = g := by
  letI : X.Over (Spec (.of ℚ)) := ⟨sX⟩
  letI : Y.Over (Spec (.of ℚ)) := ⟨sY⟩
  haveI : IsSeparated (Y ↘ Spec (.of ℚ)) := inferInstanceAs (IsSeparated sY)
  haveI : f.IsOver (Spec (.of ℚ)) := ⟨hf⟩
  haveI : g.IsOver (Spec (.of ℚ)) := ⟨hg⟩
  exact ext_of_isDominant_of_isSeparated' (Spec (.of ℚ)) (fromFunctionField X) h

/-- THEOREM (proved, comparison part of S2a). A specified ring isomorphism of function
fields of two proper integral rational schemes with valuation local rings extends to a scheme
isomorphism over the rationals. Rational scalar compatibility is automatic, and the
 generic-point restriction is the specified map.
Locator: Milne I.3.1, pp. 16–17, and p. 19 on birational equivalence;
`extend_from_valuation_stalks` and `eq_of_generic_agreement` above.
This theorem assumes no genus, group structure, or Weierstrass equation. -/
theorem isomorphism_of_functionField_equiv {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of ℚ)) (g : Y ⟶ Spec (.of ℚ)) [IsProper f] [IsProper g]
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x))
    (hY : ∀ y : Y, ValuationRing (Y.presheaf.stalk y))
    (e : Y.functionField ≃+* X.functionField) :
    ∃ i : X ≅ Y, i.hom ≫ g = f ∧
      fromFunctionField X ≫ i.hom =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫ fromFunctionField Y := by
  let er : Y.functionField ≅ X.functionField := e.toCommRingCatIso
  obtain ⟨a, hag, ha⟩ := extend_from_valuation_stalks f g hX
    (Spec.map er.hom ≫ fromFunctionField Y) (functionFieldMap_over f g e.toRingHom)
  obtain ⟨b, hbf, hb⟩ := extend_from_valuation_stalks g f hY
    (Spec.map er.inv ≫ fromFunctionField X) (functionFieldMap_over g f e.symm.toRingHom)
  have hab : a ≫ b = 𝟙 X := by
    apply eq_of_generic_agreement f f (a ≫ b) (𝟙 X)
      (by rw [Category.assoc, hbf, hag]) (by simp)
    rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc,
      ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp, Category.comp_id]
  have hba : b ≫ a = 𝟙 Y := by
    apply eq_of_generic_agreement g g (b ≫ a) (𝟙 Y)
      (by rw [Category.assoc, hag, hbf]) (by simp)
    rw [← Category.assoc, hb, Category.assoc, ha, ← Category.assoc,
      ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id, Category.id_comp, Category.comp_id]
  exact ⟨⟨a, b, hab, hba⟩, hag, ha⟩

/-- THEOREM (proved). The extended isomorphism induces exactly the specified pullback on
function fields. Locator: Tau Ceti, `Scheme.Hom.eq_functionFieldMap_iff`;
`isomorphism_of_functionField_equiv` above. -/
theorem isomorphism_functionFieldMap {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (e : Y.functionField ≃+* X.functionField) (i : X ≅ Y)
    (h : fromFunctionField X ≫ i.hom =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ fromFunctionField Y) :
    i.hom.functionFieldMap = CommRingCat.ofHom e.toRingHom := by
  exact ((i.hom.eq_functionFieldMap_iff (CommRingCat.ofHom e.toRingHom)).mpr h.symm).symm

end ZInQ.Contrib.RC53Assist.AbelianCurve

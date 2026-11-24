import ZInQKernel.Contrib.RC53Assist.AbelianCurve.BirationalComparison

/-!
# Comparing proper regular curves over an arbitrary field through their function fields

An integral scheme over a field `K` whose local rings are valuation rings admits an extension
of every generic-point map to a proper `K`-scheme (valuative criterion). Applying this in both
directions, a `K`-algebra isomorphism of function fields of two such proper integral
`K`-schemes extends to a `K`-isomorphism of schemes inducing that field isomorphism.

The statements and proofs are those of the rational version, module
`ZInQKernel.Contrib.RC53Assist.AbelianCurve.BirationalComparison` (same declaration names,
namespace `ZInQ.Contrib.RC53Assist.AbelianCurve`), with `ℚ` replaced by `K`. Over `ℚ` every
ring homomorphism of function fields is automatically `ℚ`-linear; here the field isomorphism is
assumed `K`-linear (`he`), which is exactly what the comparison needs.

Mathematical locator: Milne, *Abelian varieties*, version 2.00 (2008), I, Theorem 3.1, printed
pp. 16–17, with its valuative-criterion proof, and the paragraph on birational equivalence on
printed p. 19.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.S2aNumberField

open AlgebraicGeometry CategoryTheory Limits
open ZInQ.Contrib.RC53Assist.AbelianCurve (functionFieldAlgebra globalFunctionsMap
  fromFunctionField)

variable {K : Type} [Field K]

/-- THEOREM (proved). The structure morphism of the spectrum of the function field is the
spectrum of its ground-field algebra map. Locator: Mathlib, `Scheme.fromSpecStalk_toSpecΓ` and
naturality of `Scheme.toSpecΓ`; the rational version `AbelianCurve.fromFunctionField_structure`. -/
theorem fromFunctionField_structure {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) :
    letI := functionFieldAlgebra f
    fromFunctionField X ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K X.functionField)) := by
  letI := functionFieldAlgebra f
  have hbase : f = X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (globalFunctionsMap f)) := by
    have hring : CommRingCat.ofHom (globalFunctionsMap f) =
        (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop := rfl
    rw [hring, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
      ← SpecMap_ΓSpecIso_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.comp_id]
  conv_lhs => rw [hbase]
  rw [← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
  congr 1

/-- THEOREM (proved). A `K`-linear homomorphism of function fields gives a generic-point map
over the base. Locator: `fromFunctionField_structure` above. -/
theorem functionFieldMap_over {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K)) (e : Y.functionField →+* X.functionField)
    (he : letI := functionFieldAlgebra f
      letI := functionFieldAlgebra g
      ∀ c : K, e (algebraMap K Y.functionField c) = algebraMap K X.functionField c) :
    (Spec.map (CommRingCat.ofHom e) ≫ fromFunctionField Y) ≫ g =
      fromFunctionField X ≫ f := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  rw [Category.assoc, fromFunctionField_structure, fromFunctionField_structure, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext he)

/-- THEOREM (proved). An integral scheme with valuation local rings admits extension of every
generic-point map to a proper `K`-scheme, with the base and generic-point squares intact.
Locator: Milne I.3.1, pp. 16–17; Mathlib's valuative criterion and spreading out; the rational
version `AbelianCurve.extend_from_valuation_stalks`. -/
theorem extend_from_valuation_stalks {X Y : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K)) [IsProper g]
    (hv : ∀ x : X, ValuationRing (X.presheaf.stalk x))
    (a : Spec X.functionField ⟶ Y) (ha : a ≫ g = fromFunctionField X ≫ f) :
    ∃ b : X ⟶ Y, b ≫ g = f ∧ fromFunctionField X ≫ b = a := by
  letI : X.Over (Spec (.of K)) := ⟨f⟩
  letI : Y.Over (Spec (.of K)) := ⟨g⟩
  haveI : IsSeparated (Y ↘ Spec (.of K)) := inferInstanceAs (IsSeparated g)
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
  haveI : r.IsOver (Spec (.of K)) := by
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

/-- THEOREM (proved). Two maps over `Spec K` into a separated scheme agree if they agree on the
generic point. Locator: Mathlib, `ext_of_isDominant_of_isSeparated'`. -/
theorem eq_of_generic_agreement {X Y : Scheme.{0}} [IsIntegral X]
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsSeparated sY]
    (f g : X ⟶ Y) (hf : f ≫ sY = sX) (hg : g ≫ sY = sX)
    (h : fromFunctionField X ≫ f = fromFunctionField X ≫ g) : f = g := by
  letI : X.Over (Spec (.of K)) := ⟨sX⟩
  letI : Y.Over (Spec (.of K)) := ⟨sY⟩
  haveI : IsSeparated (Y ↘ Spec (.of K)) := inferInstanceAs (IsSeparated sY)
  haveI : f.IsOver (Spec (.of K)) := ⟨hf⟩
  haveI : g.IsOver (Spec (.of K)) := ⟨hg⟩
  exact ext_of_isDominant_of_isSeparated' (Spec (.of K)) (fromFunctionField X) h

/-- THEOREM (proved). A `K`-linear isomorphism of function fields of two proper integral
`K`-schemes with valuation local rings extends to a scheme isomorphism over `Spec K` whose
generic-point restriction is the specified map.
Locator: Milne I.3.1, pp. 16–17, and p. 19 on birational equivalence;
`extend_from_valuation_stalks` and `eq_of_generic_agreement` above. -/
theorem isomorphism_of_functionField_equiv {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K)) [IsProper f] [IsProper g]
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x))
    (hY : ∀ y : Y, ValuationRing (Y.presheaf.stalk y))
    (e : Y.functionField ≃+* X.functionField)
    (he : letI := functionFieldAlgebra f
      letI := functionFieldAlgebra g
      ∀ c : K, e (algebraMap K Y.functionField c) = algebraMap K X.functionField c) :
    ∃ i : X ≅ Y, i.hom ≫ g = f ∧
      fromFunctionField X ≫ i.hom =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫ fromFunctionField Y := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  have he' : ∀ c : K, e.symm (algebraMap K X.functionField c) =
      algebraMap K Y.functionField c := fun c => by
    rw [← he c, RingEquiv.symm_apply_apply]
  let er : Y.functionField ≅ X.functionField := e.toCommRingCatIso
  obtain ⟨a, hag, ha⟩ := extend_from_valuation_stalks f g hX
    (Spec.map er.hom ≫ fromFunctionField Y) (functionFieldMap_over f g e.toRingHom he)
  obtain ⟨b, hbf, hb⟩ := extend_from_valuation_stalks g f hY
    (Spec.map er.inv ≫ fromFunctionField X) (functionFieldMap_over g f e.symm.toRingHom he')
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

end ZInQ.Contrib.RC53Assist.S2aNumberField

import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.SeventhStalkConstruction.Prelude
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.SeventhStalkConstruction.CanonicalEndpointLaws

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory TensorProduct"
h77_open "TensorProduct"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped _root_.TensorProduct

universe u
theorem pullback_delta_translation_construction
    {R : Type u} [rBase : CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤))
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsIso e.1]
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (η : ↑(pullback z f))
    (T : ComponentReading R K gK d ω)
    (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀) (τ₀ : SchemeHomOver (U₀.ι ≫ pullback.fst z f ≫ z) T.f)
    (hτ₀ : (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K T.f (U₀.ι ≫ pullback.fst z f ≫ z) τ₀) T.e).1 =
            pullback.map (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U₀.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f) (hv₁ : v ≫ pullback.fst z T.f = U₀.ι ≫ pullback.fst z f)
    (hv₂ : v ≫ pullback.snd z T.f = τ₀.1)

    [aRP : Algebra R ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩))]
    [IsDomain (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))] [IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)]
    (ϖ : R) (hϖirr : Irreducible ϖ)
    [aRS : Algebra R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))))))
    [aRO : Algebra R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)]
    (halgO : (U₀ : Scheme.{u}).fromSpecStalk ⟨η, hηU⟩ ≫ (U₀.ι ≫ pullback.fst z f ≫ z) =
      Spec.map (CommRingCat.ofHom (algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))))
    [aR1 : Algebra R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))]
    (halg₁ : T.Y.fromSpecStalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)) ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))))))

        [aKKprime : Algebra K (FractionRing (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))))]
    [IsScalarTower R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) (FractionRing (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))))] [IsScalarTower R K (FractionRing (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))))]
       [aKF : Algebra K (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))] [aKprimeF : Algebra (FractionRing (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))] 
    [IsScalarTower R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))] [IsScalarTower R K (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))] [IsScalarTower K (FractionRing (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))]
    (hDeltaZ : letI : Algebra (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) :=
      ((pullback.fst z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom.toAlgebra;
      IsScalarTower R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)))
    (hDeltaA : letI : Algebra (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) :=
      ((pullback.snd z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom.toAlgebra;
      IsScalarTower R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩))) :
    letI : Algebra (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) :=
      ((v.stalkMap ⟨η, hηU⟩).hom.comp ((pullback.fst z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom).toAlgebra;
    letI : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := (v.stalkMap ⟨η, hηU⟩).hom.toAlgebra;
    letI : Algebra (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) := ((pullback.snd z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom.toAlgebra;
    letI : Algebra (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := ((algebraMap ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)).comp (algebraMap (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)))).toAlgebra;
    ∀ [IsScalarTower (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) (FractionRing (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))] [IsScalarTower R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))],
    (letI : Algebra (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) :=
      ((pullback.fst z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom.toAlgebra;
      letI : Algebra (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) :=
        ((pullback.snd z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom.toAlgebra;
      Function.Bijective
        ((KaehlerDifferential.map R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩))).restrictScalars ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ∘ₗ
          KaehlerDifferential.mapBaseChange R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)))) ∧
    ((LXK.mul (Spec.map (CommRingCat.ofHom (algebraMap K (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))))
        ⟨Spec.map (CommRingCat.ofHom (algebraMap (FractionRing (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))) ≫
            (NeronModelInfra.schemeHomOverComp
              (pointGenericFibre (K := K) (K' := (FractionRing (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))))
                (⟨Z.fromSpecStalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)), halgZ⟩ :
                  SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))))) z)) uK).1, by
          rw [Category.assoc, (NeronModelInfra.schemeHomOverComp _ uK).2, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← IsScalarTower.algebraMap_eq]⟩
        (NeronModelInfra.schemeHomOverComp
          (pointGenericFibre (K := K) (K' := (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))
            (⟨(U₀ : Scheme.{u}).fromSpecStalk ⟨η, hηU⟩, halgO⟩ :
              SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))) (U₀.ι ≫ pullback.fst z f ≫ z)))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U₀.ι ≫ pullback.fst z f ≫ z)
              ⟨U₀.ι ≫ pullback.snd z f, by rw [Category.assoc, ← pullback.condition]⟩) e))).1 =
      (NeronModelInfra.schemeHomOverComp
        (pointGenericFibre (K := K) (K' := (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))
          (⟨T.Y.fromSpecStalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)), halg₁⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))))) T.f))
        T.e).1)
 := by
  letI : Algebra (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) :=
    ((v.stalkMap ⟨η, hηU⟩).hom.comp ((pullback.fst z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom).toAlgebra
  letI : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := (v.stalkMap ⟨η, hηU⟩).hom.toAlgebra
  letI : Algebra (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) := ((pullback.snd z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom.toAlgebra
  letI : Algebra (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := ((algebraMap ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)).comp (algebraMap (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)))).toAlgebra
  intro towerSKprimeF towerRAuxF
  constructor
  · exact ConstructionInterface.pullback_stalk_delta_one_fixed T.f z (v.base ⟨η, hηU⟩)
      halgZ halg₁ hDeltaZ hDeltaA
  · have hCanonical := canonical_endpoint_scalar_tower_laws K LXK d ω X f e Z z uK η
      T U₀ hηU τ₀ hτ₀ v hv₁ hv₂ (rBase := rBase)
    exact ConstructionInterface.generic_fibre_translation_point_fixed K LXK d ω X f e Z z uK η
      T U₀ hηU τ₀ hτ₀ v hv₁ hv₂ (rBase := rBase) (aRS := aRS) (aRO := aRO)
      (aR1 := aR1) (aKKprime := aKKprime) (aKF := aKF) (aKprimeF := aKprimeF)
      halgZ halgO halg₁
      (FractionRing (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))))
      (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))
      hCanonical.1 hCanonical.2

end P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
end ZInQ.Contrib.CloudR2NeronExistence.Henselian

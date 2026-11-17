import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_exists_nhds_translation_extension_isOpenImmersion_of_formallySmooth_stalk_of_isOmegaMinimal.lean
Original Git blob: 6f2bdd20587db0d4e5e004aba5b3c147f3962dc8
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 1 old-version global performance-guard attribute lines (no proof or type).
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_OmegaMinimalComponentData
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_exists_nhds_translation_extension_isOpenImmersion_of_formallySmooth_stalk_of_isOmegaMinimal

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_nhds_translation_extension_isOpenImmersion_of_formallySmooth_stalk_of_isOmegaMinimal
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤))
    (D : MinimalComponentData R K gK d ω) (hD : D.IsOmegaMinimal)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    (V : ∀ c : D.ι, ((D.C c).Y).Opens) (j : ∀ c : D.ι, SchemeHomOver ((V c).ι ≫ (D.C c).f) f)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsIso e.1]
    (hyV : ∀ c, (D.C c).y ∈ V c)
    (hVK : ∀ c (y' : ↥(D.C c).Y), (D.C c).f.base y' ≠ IsLocalRing.closedPoint R → y' ∈ V c)
    (hjopen : ∀ c, IsOpenImmersion (j c).1)
    (hjchart : ∀ c, (genericFibreRestrict R K f ((V c).ι ≫ (D.C c).f) (j c)).1 ≫ e.1 =
      (genericFibreRestrict R K (D.C c).f ((V c).ι ≫ (D.C c).f) ⟨(V c).ι, rfl⟩).1 ≫ (D.C c).e.1)
    (hcover : ∀ x : ↥X, ∃ c, x ∈ Set.range (j c).1.base)
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (η : ↑(pullback z f)) (hη : (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R)
    (hmax : ∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η)
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
    (hgen : T.y ⤳ τ₀.1.base ⟨η, hηU⟩)
    (hn : ∃ c : D.ι, T.n = (D.C c).n)
    (hdom : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))
    (hdom' : IsDomain ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)))
    (hfrac : letI : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :=
        ((algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))).comp (v.stalkMap ⟨η, hηU⟩).hom).toAlgebra
      IsFractionRing ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))
    (hfs : letI : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := (v.stalkMap ⟨η, hηU⟩).hom.toAlgebra
      Algebra.FormallySmooth ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :
    ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
      IsOpenImmersion
        (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
          ((Category.assoc _ _ _).trans τ.2.symm)) ∧
      (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
        pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
            (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
          (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1 := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_nhds_translation_extension_isOpenImmersion_of_formallySmooth_stalk_of_isOmegaMinimal.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian

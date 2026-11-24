import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_mul_pointGenericFibre_eq_pointGenericFibre_comp_chart_of_genericFibreRestrict_comp_eq_mul.lean
Original Git blob: b65e6565535bf62b60ca22857620bbd7377f3859
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
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
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_mul_pointGenericFibre_eq_pointGenericFibre_comp_chart_of_genericFibreRestrict_comp_eq_mul

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

theorem NeronModelInfra.mul_pointGenericFibre_eq_pointGenericFibre_comp_chart_of_genericFibreRestrict_comp_eq_mul
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
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

    [Algebra R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))))))
    [Algebra R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)]
    (halgO : (U₀ : Scheme.{u}).fromSpecStalk ⟨η, hηU⟩ ≫ (U₀.ι ≫ pullback.fst z f ≫ z) =
      Spec.map (CommRingCat.ofHom (algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))))
    [Algebra R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))]
    (halg₁ : T.Y.fromSpecStalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)) ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))))))

    (K' F : Type u) [Field K'] [Algebra (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) K'] [IsFractionRing (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) K'] [Algebra R K'] [Algebra K K']
    [IsScalarTower R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) K'] [IsScalarTower R K K']
    [Field F] [Algebra ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F] [Algebra R F] [Algebra K F] [Algebra K' F] [Algebra (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) F]
    [IsScalarTower R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F] [IsScalarTower R K F] [IsScalarTower K K' F] [IsScalarTower (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) K' F]
    (hRO : (algebraMap (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) F) =
      (algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F).comp ((v.stalkMap ⟨η, hηU⟩).hom.comp
        ((pullback.fst z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom))
    [Algebra (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) F] [IsScalarTower R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) F]
    (hτF : (algebraMap (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) F) =
      (algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F).comp ((v.stalkMap ⟨η, hηU⟩).hom.comp
        ((pullback.snd z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom)) :
    (LXK.mul (Spec.map (CommRingCat.ofHom (algebraMap K F)))
        ⟨Spec.map (CommRingCat.ofHom (algebraMap K' F)) ≫
            (NeronModelInfra.schemeHomOverComp
              (pointGenericFibre (K := K) (K' := K')
                (⟨Z.fromSpecStalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)), halgZ⟩ :
                  SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))))) z)) uK).1, by
          rw [Category.assoc, (NeronModelInfra.schemeHomOverComp _ uK).2, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← IsScalarTower.algebraMap_eq]⟩
        (NeronModelInfra.schemeHomOverComp
          (pointGenericFibre (K := K) (K' := F)
            (⟨(U₀ : Scheme.{u}).fromSpecStalk ⟨η, hηU⟩, halgO⟩ :
              SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))) (U₀.ι ≫ pullback.fst z f ≫ z)))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U₀.ι ≫ pullback.fst z f ≫ z)
              ⟨U₀.ι ≫ pullback.snd z f, by rw [Category.assoc, ← pullback.condition]⟩) e))).1 =
      (NeronModelInfra.schemeHomOverComp
        (pointGenericFibre (K := K) (K' := F)
          (⟨T.Y.fromSpecStalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)), halg₁⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))))) T.f))
        T.e).1 := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_mul_pointGenericFibre_eq_pointGenericFibre_comp_chart_of_genericFibreRestrict_comp_eq_mul.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian

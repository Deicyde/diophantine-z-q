import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.lean
Original Git blob: 03278af2a21dc2a85c2da69ae89d3d1c7d6ddc4b
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 2 old-version global performance-guard attribute lines (no proof or type).
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
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul

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

theorem NeronModelInfra.exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤)) (hωframe : Scheme.Modules.IsFrameOn ω ⊤)
    (hleft : (∀ (L F : Type u) [Field L] [Field F] [Algebra K L] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
        (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) gK)
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) gK)
        (U' U'' : XK.Opens) (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'')
        [Algebra Γ(XK, U') F] [Algebra Γ(XK, U'') F],
        letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U'; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''
        ∀ [IsScalarTower K Γ(XK, U') F] [IsScalarTower K Γ(XK, U'') F],
        Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U') F)) ≫ hU'.fromSpec = x.1 →
        Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U'') F)) ≫ hU''.fromSpec =
          (LXK.mul (Spec.map (CommRingCat.ofHom (algebraMap K F)))
            ⟨Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫ a.1, by
              rw [Category.assoc, a.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                ← IsScalarTower.algebraMap_eq]⟩ x).1 →
        ∀ (ω' : ⋀[Γ(XK, U')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U')))
          (ω'' : ⋀[Γ(XK, U'')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U''))),
          (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gK) d U' ω' = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d).presheaf.map (homOfLE le_top).op ω →
          (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gK) d U'' ω'' = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d).presheaf.map (homOfLE le_top).op ω →
          TopFormOrder.topFormMap K L Γ(XK, U'') F d ω'' = TopFormOrder.topFormMap K L Γ(XK, U') F d ω'))
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
    (hgen : T.y ⤳ τ₀.1.base ⟨η, hηU⟩) :
    (∃ c : D.ι, T.n = (D.C c).n) ∧
      letI : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := (v.stalkMap ⟨η, hηU⟩).hom.toAlgebra
      Algebra.FormallySmooth ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian

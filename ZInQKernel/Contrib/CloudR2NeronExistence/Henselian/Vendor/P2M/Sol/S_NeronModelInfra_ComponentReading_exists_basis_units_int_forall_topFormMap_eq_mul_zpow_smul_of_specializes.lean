import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_NeronModelInfra_ComponentReading_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_specializes.lean
Original Git blob: 098671c0e6161cef7b70df6095923c7200d262a6
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 1 old-version global performance-guard attribute lines (no proof or type).
* Explicitly closed 2 scopes originally left open at EOF.
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
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixGenericFibreOpenImmersionDVR
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_TopFormOrder_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_topFormMap_eq_topFormMap_of_specMap_comp_fromSpec_eq
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Smooth_algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_smooth_of_genericFibre
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_topToSections_bijective_of_isAffineOpen
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_NeronModelInfra_ComponentReading_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_specializes
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace P2mSFGeom
h77_bridge_namespace

theorem topToSections_smul {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (d : ℕ) (U : X.Opens) (g : Γ(X, U)) (s : ⋀[Γ(X, U)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op U))) :
    (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections f) d U (g • s) = g • (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections f) d U s := by
  unfold Scheme.Hom.topToSections
  rw [LinearMap.map_smul]
  exact LinearMap.map_smul _ g _

noncomputable def basisKaehlerPresheaf {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (bU : Module.Basis (Fin d) Γ(X, U) Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), U)) :
    Module.Basis (Fin d) Γ(X, U) ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op U)) :=
  bU.map (LinearEquiv.ofBijective ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSectionsₗ f) U)
    (Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen f hU)).symm

theorem bijective_smul_of_isFrameOn {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials f) d, ⊤)) (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (ωU : ⋀[Γ(X, U)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op U)))
    (hωU : (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections f) d U ωU = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials f) d).presheaf.map (homOfLE le_top).op ω) :
    Function.Bijective fun g : Γ(X, U) => g • ωU := by
  have hbij := Scheme.Hom.topToSections_bijective_of_isAffineOpen f d hU
  have hfr := hω.bijective (W := U) le_top le_top
  have hcomp : ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections f) d U) ∘ (fun g : Γ(X, U) => g • ωU) =
      fun g : Γ(X, U) => g • (((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials f) d).presheaf.map (homOfLE le_top).op ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials f) d, U)) := by
    funext g
    simp only [Function.comp_apply, topToSections_smul, hωU]
  have h2 : Function.Bijective (((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections f) d U) ∘ (fun g : Γ(X, U) => g • ωU)) := by rw [hcomp]; exact hfr
  exact ⟨fun a b hab => h2.1 (by simp only [Function.comp_apply, hab]),
    fun s => by obtain ⟨g, hg⟩ := h2.2 ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections f) d U s); exact ⟨g, hbij.1 hg⟩⟩

theorem smoothOfRelativeDimension_genericFibre_of_chart
    {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ) [SmoothOfRelativeDimension d gK]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion e.1] :
    SmoothOfRelativeDimension d (pullback.snd f (specGenericFibreInclusion R K)) := by
  rw [← e.2]
  have : SmoothOfRelativeDimension (0 + d) (e.1 ≫ gK) := inferInstance
  simpa using this

theorem isDomain_stalk_of_smooth {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] (y : Y) : IsDomain (Y.presheaf.stalk y) := by
  let e : Γ(Spec (CommRingCat.of R), ⊤) ≃+* R := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  haveI : IsDomain Γ(Spec (CommRingCat.of R), ⊤) := MulEquiv.isDomain R e.toMulEquiv
  haveI : IsIntegrallyClosed Γ(Spec (CommRingCat.of R), ⊤) := IsIntegrallyClosed.of_equiv e.symm
  exact (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk f y).1

theorem exists_omegaU {K : Type u} [Field K] {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤)) (U : XK.Opens) (hU : IsAffineOpen U) :
    ∃ ωU : ⋀[Γ(XK, U)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U)),
      (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gK) d U ωU = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d).presheaf.map (homOfLE le_top).op ω :=
  (Scheme.Hom.topToSections_bijective_of_isAffineOpen gK d hU).2 _

theorem ringHom_ext_of_specMap_comp_fromSpec_eq {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {F : Type u} [CommRing F] (a b : Γ(X, U) →+* F)
    (h : Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec = Spec.map (CommRingCat.ofHom b) ≫ hU.fromSpec) : a = b := by
  have h1 : Spec.map (CommRingCat.ofHom a) = Spec.map (CommRingCat.ofHom b) := by
    rw [← cancel_mono hU.fromSpec]; exact h
  have h2 := Spec.map_injective h1
  exact congrArg CommRingCat.Hom.hom h2

theorem specMap_germ_comp_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    Spec.map (X.presheaf.germ U x hx) ≫ hU.fromSpec = X.fromSpecStalk x := by
  change hU.fromSpecStalk hx = _
  exact IsAffineOpen.fromSpecStalk_eq_fromSpecStalk hU hx

end P2mSFGeom

open P2mSFGeom in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    {d : ℕ} [SmoothOfRelativeDimension d gK]
    {ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤)} (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (T : ComponentReading R K gK d ω)
    (y₁ : ↥T.Y) (hy₁ : T.f.base y₁ = IsLocalRing.closedPoint R) (hgen : T.y ⤳ y₁)
    [Algebra R (T.Y.presheaf.stalk y₁)]
    (halg₁ : T.Y.fromSpecStalk y₁ ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁)))) :
    ∃ (b' : Module.Basis (Fin d) (T.Y.presheaf.stalk y₁) (Ω[(T.Y.presheaf.stalk y₁)⁄R]))
      (w : (T.Y.presheaf.stalk y₁)ˣ) (m : ℤ),
      ∀ (F : Type u) [Field F] [Algebra (T.Y.presheaf.stalk y₁) F] [Algebra R F] [Algebra K F]
        [IsScalarTower R (T.Y.presheaf.stalk y₁) F] [IsScalarTower R K F]
        (U : XK.Opens) (hU : IsAffineOpen U) [Algebra Γ(XK, U) F]
        (hKU : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U; IsScalarTower K Γ(XK, U) F)
        (hx : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) F)) ≫ hU.fromSpec =
          (schemeHomOverComp
            (pointGenericFibre (K := K) (K' := F)
              (⟨T.Y.fromSpecStalk y₁, halg₁⟩ :
                SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁)))) T.f))
            T.e).1)
        (ωU : ⋀[Γ(XK, U)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U)))
        (hωU : (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gK) d U ωU = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d).presheaf.map (homOfLE le_top).op ω),
        letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U
        TopFormOrder.topFormMap K K Γ(XK, U) F d ωU =
          (algebraMap (T.Y.presheaf.stalk y₁) F (w : (T.Y.presheaf.stalk y₁)) *
              algebraMap (T.Y.presheaf.stalk y₁) F (algebraMap R (T.Y.presheaf.stalk y₁) ϖ) ^ m) •
            TopFormOrder.topFormMap R K (T.Y.presheaf.stalk y₁) F d
              (exteriorPower.ιMulti (T.Y.presheaf.stalk y₁) d b') := by
  classical

  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  haveI : IsLocalization.Away ϖ K := NeronModelInfra.isLocalizationAway_of_irreducible K hirr
  haveI : IsOpenImmersion T.e.1 := T.isOpenImmersion
  haveI : Smooth T.f := T.smooth
  haveI : LocallyOfFiniteType T.f := T.locallyOfFiniteType
  haveI := smoothOfRelativeDimension_genericFibre_of_chart K gK d T.f T.e
  haveI : SmoothOfRelativeDimension d T.f := AlgebraicGeometry.smoothOfRelativeDimension_of_smooth_of_genericFibre K T.f d
  haveI : IsLocallyNoetherian T.Y := LocallyOfFiniteType.isLocallyNoetherian T.f
  haveI : IsDomain (T.Y.presheaf.stalk y₁) := isDomain_stalk_of_smooth T.f y₁
  obtain ⟨hϖ0, hϖp⟩ := AlgebraicGeometry.Smooth.algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint
    ϖ hϖ T.f y₁ hy₁ halg₁

  obtain ⟨U₀, hyU₀, eΩ, hbasis⟩ :=
    AlgebraicGeometry.Scheme.Hom.exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension T.f d y₁
  obtain ⟨W', hWaff, hyW, hWU₀⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.Y.isBasis_affineOpens) hyU₀
  let W : T.Y.Opens := W'
  have hW : IsAffineOpen W := hWaff
  change y₁ ∈ W at hyW
  change W ≤ U₀ at hWU₀
  have hβ₀ := hbasis W hWU₀ hW
  cases hβ₀ with
  | intro β₀ _ =>
  letI algRW : Algebra R Γ(T.Y, W) := ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra T.f W
  let β : Module.Basis (Fin d) Γ(T.Y, W) ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf T.f).obj (op W)) := basisKaehlerPresheaf T.f d hW β₀

  let fstT := pullback.fst T.f (specGenericFibreInclusion R K)
  let sndT := pullback.snd T.f (specGenericFibreInclusion R K)
  let WK : (pullback T.f (specGenericFibreInclusion R K)).Opens := fstT ⁻¹ᵁ W
  have hPB : IsPullback fstT sndT T.f (Spec.map (CommRingCat.ofHom (algebraMap R K))) := IsPullback.of_hasPullback _ _
  obtain ⟨hWK, hpush⟩ :=
    AlgebraicGeometry.Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback T.f sndT fstT hPB W hW

  let U₂ : XK.Opens := T.e.1 ''ᵁ WK
  have hU₂ : IsAffineOpen U₂ := hWK.image_of_isOpenImmersion T.e.1

  letI algKB' : Algebra K Γ(XK, U₂) := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U₂
  let eApp : Γ(XK, U₂) ≅ Γ(pullback T.f (specGenericFibreInclusion R K), WK) := T.e.1.appIso WK
  letI algBB' : Algebra Γ(T.Y, W) Γ(XK, U₂) := ((fstT.appLE W WK le_rfl) ≫ eApp.inv).hom.toAlgebra
  letI algRB' : Algebra R Γ(XK, U₂) := ((algebraMap K Γ(XK, U₂)).comp (algebraMap R K)).toAlgebra
  haveI towRKB' : IsScalarTower R K Γ(XK, U₂) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  letI algKWK : Algebra K Γ(pullback T.f (specGenericFibreInclusion R K), WK) := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra sndT) WK
  letI algBWK : Algebra Γ(T.Y, W) Γ(pullback T.f (specGenericFibreInclusion R K), WK) :=
    (fstT.appLE W WK le_rfl).hom.toAlgebra
  letI algRWK : Algebra R Γ(pullback T.f (specGenericFibreInclusion R K), WK) :=
    ((algebraMap K Γ(pullback T.f (specGenericFibreInclusion R K), WK)).comp (algebraMap R K)).toAlgebra
  haveI towRKWK : IsScalarTower R K Γ(pullback T.f (specGenericFibreInclusion R K), WK) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have hRW : algebraMap R Γ(T.Y, W) = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.f.appLE ⊤ W le_top).hom := rfl
  have hKWK : algebraMap K Γ(pullback T.f (specGenericFibreInclusion R K), WK) =
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ sndT.appLE ⊤ WK le_top).hom := rfl
  have hcompWK : (algebraMap Γ(T.Y, W) Γ(pullback T.f (specGenericFibreInclusion R K), WK)).comp
      (algebraMap R Γ(T.Y, W)) =
      (algebraMap K Γ(pullback T.f (specGenericFibreInclusion R K), WK)).comp (algebraMap R K) := by
    rw [hRW, hKWK]
    change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.f.appLE ⊤ W le_top ≫ fstT.appLE W WK le_rfl).hom =
      (CommRingCat.ofHom (algebraMap R K) ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ sndT.appLE ⊤ WK le_top).hom
    congr 1
    rw [Scheme.Hom.appLE_comp_appLE, ← Category.assoc (CommRingCat.ofHom (algebraMap R K)),
      Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    congr 1
    change (fstT ≫ T.f).appLE ⊤ WK _ = (Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop ≫ sndT.appLE ⊤ WK le_top
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    erw [Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact pullback.condition
  haveI towRBWK : IsScalarTower R Γ(T.Y, W) Γ(pullback T.f (specGenericFibreInclusion R K), WK) :=
    IsScalarTower.of_algebraMap_eq' hcompWK.symm

  have hKU₂ : algebraMap K Γ(XK, U₂) = ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ gK.appLE ⊤ U₂ le_top).hom := rfl
  have hgKapp : gK.appLE ⊤ U₂ le_top = sndT.appLE ⊤ WK le_top ≫ eApp.inv := by
    rw [Iso.eq_comp_inv]
    change gK.appLE ⊤ U₂ le_top ≫ (T.e.1.appIso WK).hom = sndT.appLE ⊤ WK le_top
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
    have h2 : T.e.1 ≫ gK = sndT := T.e.2
    simp only [h2]
  haveI towRBB' : IsScalarTower R Γ(T.Y, W) Γ(XK, U₂) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change (algebraMap K Γ(XK, U₂)).comp (algebraMap R K) =
      (eApp.inv.hom.comp (algebraMap Γ(T.Y, W) Γ(pullback T.f (specGenericFibreInclusion R K), WK))).comp
        (algebraMap R Γ(T.Y, W))
    rw [RingHom.comp_assoc, hcompWK, ← RingHom.comp_assoc]
    congr 1
    rw [hKU₂, hKWK, hgKapp]; rfl

  have hpo : Algebra.IsPushout R K Γ(T.Y, W) Γ(pullback T.f (specGenericFibreInclusion R K), WK) := hpush
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid Γ(T.Y, W) (Submonoid.powers ϖ))
      Γ(pullback T.f (specGenericFibreInclusion R K), WK) :=
    (Algebra.isLocalization_iff_isPushout (Submonoid.powers ϖ) K).mpr hpo.symm
  let eAlg : Γ(pullback T.f (specGenericFibreInclusion R K), WK) ≃ₐ[Γ(T.Y, W)] Γ(XK, U₂) :=
    AlgEquiv.ofRingEquiv (f := eApp.symm.commRingCatIsoToRingEquiv) (fun x => rfl)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid Γ(T.Y, W) (Submonoid.powers ϖ)) Γ(XK, U₂) :=
    IsLocalization.isLocalization_of_algEquiv _ eAlg
  haveI hAway : IsLocalization.Away (algebraMap R Γ(T.Y, W) ϖ) Γ(XK, U₂) := by
    have hsub : Algebra.algebraMapSubmonoid Γ(T.Y, W) (Submonoid.powers ϖ) =
        Submonoid.powers (algebraMap R Γ(T.Y, W) ϖ) := Submonoid.map_powers _ _
    unfold IsLocalization.Away
    rw [← hsub]; infer_instance

  have hωU₂' := exists_omegaU gK d ω U₂ hU₂
  cases hωU₂' with
  | intro ωU₂ hωU₂ =>
  have hbij := bijective_smul_of_isFrameOn gK d hU₂ ω hω ωU₂ hωU₂
  have hspan : Submodule.span Γ(XK, U₂) {ωU₂} = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro s
    obtain ⟨g, hg⟩ := hbij.2 s
    rw [Submodule.mem_span_singleton]
    exact ⟨g, hg⟩

  letI algWO : Algebra Γ(T.Y, W) (T.Y.presheaf.stalk y₁) := (T.Y.presheaf.germ W y₁ hyW).hom.toAlgebra
  haveI hlocO : IsLocalization.AtPrime (T.Y.presheaf.stalk y₁) (hW.primeIdealOf ⟨y₁, hyW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨y₁, hyW⟩
  have htowO : (algebraMap Γ(T.Y, W) (T.Y.presheaf.stalk y₁)).comp (algebraMap R Γ(T.Y, W)) =
      algebraMap R (T.Y.presheaf.stalk y₁) := by
    have h1 : Spec.map (CommRingCat.ofHom ((algebraMap Γ(T.Y, W) (T.Y.presheaf.stalk y₁)).comp
        (algebraMap R Γ(T.Y, W)))) = Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁))) := by
      rw [← halg₁]
      change Spec.map (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.f.appLE ⊤ W le_top) ≫
        T.Y.presheaf.germ W y₁ hyW) = _
      rw [Spec.map_comp, Spec.map_comp]
      have h2 : Spec.map (T.f.appLE ⊤ W le_top) ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv =
          hW.fromSpec ≫ T.f := by
        rw [← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
        exact IsAffineOpen.SpecMap_appLE_fromSpec T.f (isAffineOpen_top _) hW le_top
      rw [h2, ← Category.assoc, specMap_germ_comp_fromSpec hW y₁ hyW]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  haveI : IsScalarTower R Γ(T.Y, W) (T.Y.presheaf.stalk y₁) := IsScalarTower.of_algebraMap_eq' htowO.symm

  have hcore := NeronModelInfra.TopFormOrder.exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top
    R K Γ(T.Y, W) Γ(XK, U₂) (T.Y.presheaf.stalk y₁) ϖ d β ωU₂ hspan
    (hW.primeIdealOf ⟨y₁, hyW⟩).asIdeal.primeCompl hϖ0 hϖp
  rcases hcore with ⟨b', w, m, -, hF⟩
  refine ⟨b', w, m, ?_⟩
  intro F _ _ _ _ _ _ U hU _ hKU hx ωU hωU

  let pG := NeronModelInfra.pointGenericFibre (K := K) (K' := F)
    (⟨T.Y.fromSpecStalk y₁, halg₁⟩ :
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁)))) T.f)
  have hpG_fst : pG.1 ≫ fstT = Spec.map (CommRingCat.ofHom (algebraMap (T.Y.presheaf.stalk y₁) F)) ≫
      T.Y.fromSpecStalk y₁ := NeronModelInfra.pointGenericFibre_coe_comp_fst _
  have hrangeW : ∀ z, fstT.base (pG.1.base z) ∈ W := by
    intro z
    rw [← Scheme.Hom.comp_apply, hpG_fst, Scheme.Hom.comp_apply]
    have hz : (T.Y.fromSpecStalk y₁).base
        ((Spec.map (CommRingCat.ofHom (algebraMap (T.Y.presheaf.stalk y₁) F))).base z) ∈
        Set.range (T.Y.fromSpecStalk y₁).base := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hz
    exact hz.mem_open W.2 hyW
  have hrange : Set.range (pG.1 ≫ T.e.1).base ⊆ Set.range U₂.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact ⟨pG.1.base z, hrangeW z, rfl⟩
  let xU := IsOpenImmersion.lift U₂.ι (pG.1 ≫ T.e.1) hrange
  have hxU_fac : xU ≫ U₂.ι = pG.1 ≫ T.e.1 := IsOpenImmersion.lift_fac _ _ _
  let φ : Γ(XK, U₂) ⟶ CommRingCat.of F := Spec.homEquiv (xU ≫ hU₂.isoSpec.hom)
  have hφ : Spec.map φ = xU ≫ hU₂.isoSpec.hom := Spec.homEquiv.symm_apply_apply (xU ≫ hU₂.isoSpec.hom)
  letI algB'F : Algebra Γ(XK, U₂) F := φ.hom.toAlgebra
  have hφ' : CommRingCat.ofHom (algebraMap Γ(XK, U₂) F) = φ := rfl
  have hx₂ : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U₂) F)) ≫ hU₂.fromSpec = pG.1 ≫ T.e.1 := by
    rw [hφ', hφ, Category.assoc, ← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc, hxU_fac]
  have hxF2 : (pG.1 ≫ T.e.1) ≫ gK = Spec.map (CommRingCat.ofHom (algebraMap K F)) :=
    (NeronModelInfra.schemeHomOverComp pG T.e).2

  have keyK : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ gK.appLE ⊤ U₂ le_top ≫ φ =
      CommRingCat.ofHom (algebraMap K F) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ← hxF2, ← hx₂, hφ']
    simp only [Category.assoc]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec gK (isAffineOpen_top _) hU₂ le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have ecompK : (algebraMap Γ(XK, U₂) F).comp (algebraMap K Γ(XK, U₂)) = algebraMap K F := by
    have h := congrArg CommRingCat.Hom.hom keyK
    rw [hKU₂]
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h
    exact h
  haveI towKB'F : IsScalarTower K Γ(XK, U₂) F := IsScalarTower.of_algebraMap_eq' ecompK.symm

  letI algWF : Algebra Γ(T.Y, W) F :=
    ((algebraMap (T.Y.presheaf.stalk y₁) F).comp (algebraMap Γ(T.Y, W) (T.Y.presheaf.stalk y₁))).toAlgebra
  haveI : IsScalarTower Γ(T.Y, W) (T.Y.presheaf.stalk y₁) F := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R Γ(T.Y, W) F := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change algebraMap R F = ((algebraMap (T.Y.presheaf.stalk y₁) F).comp
      (algebraMap Γ(T.Y, W) (T.Y.presheaf.stalk y₁))).comp (algebraMap R Γ(T.Y, W))
    rw [RingHom.comp_assoc, htowO, ← IsScalarTower.algebraMap_eq]

  have hSpecApp : Spec.map eApp.inv ≫ hWK.fromSpec ≫ T.e.1 = hU₂.fromSpec := by
    have h1 : Spec.map eApp.hom ≫ hU₂.fromSpec = hWK.fromSpec ≫ T.e.1 := by
      change Spec.map (T.e.1.appIso WK).hom ≫ hU₂.fromSpec = _
      rw [Scheme.Hom.appIso_hom']
      exact IsAffineOpen.SpecMap_appLE_fromSpec T.e.1 hU₂ hWK _
    rw [← h1, ← Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  have keyW : (algebraMap Γ(XK, U₂) F).comp (algebraMap Γ(T.Y, W) Γ(XK, U₂)) = algebraMap Γ(T.Y, W) F := by
    apply ringHom_ext_of_specMap_comp_fromSpec_eq hW
    change Spec.map ((fstT.appLE W WK le_rfl ≫ eApp.inv) ≫ φ) ≫ hW.fromSpec =
      Spec.map (T.Y.presheaf.germ W y₁ hyW ≫ CommRingCat.ofHom (algebraMap (T.Y.presheaf.stalk y₁) F)) ≫ hW.fromSpec
    rw [Spec.map_comp, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec fstT hW hWK le_rfl, specMap_germ_comp_fromSpec hW y₁ hyW, ← hpG_fst]
    have h3 : Spec.map φ ≫ Spec.map eApp.inv ≫ hWK.fromSpec = pG.1 := by
      rw [← cancel_mono T.e.1]
      simp only [Category.assoc]
      rw [hSpecApp, ← hφ', hx₂]
    rw [← h3]
    simp only [Category.assoc]
  haveI : IsScalarTower Γ(T.Y, W) Γ(XK, U₂) F := IsScalarTower.of_algebraMap_eq' keyW.symm

  have hmain := hF F
  rw [← hmain]
  exact AlgebraicGeometry.Scheme.Hom.topFormMap_eq_topFormMap_of_specMap_comp_fromSpec_eq gK d ω F U hU hKU U₂ hU₂
    towKB'F (hx.trans hx₂.symm) ωU hωU ωU₂ hωU₂


end
end P2MW.S_NeronModelInfra_ComponentReading_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_specializes
end ZInQ.Contrib.CloudR2NeronExistence.Henselian

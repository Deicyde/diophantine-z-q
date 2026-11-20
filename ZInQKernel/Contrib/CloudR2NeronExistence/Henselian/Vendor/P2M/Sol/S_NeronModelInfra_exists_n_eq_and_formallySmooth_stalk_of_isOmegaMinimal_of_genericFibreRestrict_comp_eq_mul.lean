import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.lean
Original Git blob: d23292a5ef1bfb7b6a02aec23fb6a94d3f3c825e
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 2 old-version global performance-guard attribute lines (no proof or type).
* Explicitly closed 1 scopes originally left open at EOF.
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
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_ComponentReading_exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_TopFormOrder_eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_bijective_kaehlerDifferential_map_comp_mapBaseChange_stalk_pullback
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_Algebra_FormallyEtale_of_formallySmooth_of_bijective_mapBaseChange
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_mul_pointGenericFibre_eq_pointGenericFibre_comp_chart_of_genericFibreRestrict_comp_eq_mul
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_MinimalComponentData_exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_TopFormOrder_topFormMap_topFormMap
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_topToSections_bijective_of_isAffineOpen
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_KaehlerDifferential_bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.SeventhStalkConstruction.C1ClosedGeometryIndex
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.SeventhStalkConstruction.C2FieldTower
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.SeventhStalkConstruction.C2Translation
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.SeventhStalkConstruction.C3TargetReading
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.SeventhStalkConstruction.C4ComponentChart
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.SeventhStalkConstruction.C6OrderStalkAssembly

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

theorem solution    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
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
      Algebra.FormallySmooth ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := by
  classical
  let rBase : CommRing R := inferInstance
  have domainBase : IsDomain R := inferInstance
  have dvrBase : IsDiscreteValuationRing R := inferInstance
  let givenK : Field K := inferInstance
  let aRK : Algebra R K := inferInstance
  have fractionRK : IsFractionRing R K := inferInstance
  have smoothGeneric : Smooth gK := inferInstance
  have separatedGeneric : IsSeparated gK := inferInstance
  have finiteTypeGeneric : LocallyOfFiniteType gK := inferInstance
  have compactGeneric : QuasiCompact gK := inferInstance
  have dimensionGeneric : SmoothOfRelativeDimension d gK := inferInstance
  have smoothX : Smooth f := inferInstance
  have separatedX : IsSeparated f := inferInstance
  have finiteTypeX : LocallyOfFiniteType f := inferInstance
  have compactX : QuasiCompact f := inferInstance
  have isoGenericX : IsIso e.1 := inferInstance
  have smoothZ : Smooth z := inferInstance
  have compactZ : QuasiCompact z := inferInstance

  let ηU : ↥U₀ := ⟨η, hηU⟩
  let η' : ↥(pullback z T.f) := v.base ηU
  let ζ₀ : ↥Z := (pullback.fst z T.f).base η'
  let y₁ : ↥T.Y := (pullback.snd z T.f).base η'
  let ξ : ↥X := (pullback.snd z f).base (U₀.ι.base ηU)
  let OObj := ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  let SObj := Z.presheaf.stalk ζ₀
  let PObj := ((pullback z T.f).presheaf.stalk η')
  let AObj := T.Y.presheaf.stalk y₁
  let XObj := X.presheaf.stalk ξ
  let O : Type u := OObj
  let S : Type u := SObj
  let P : Type u := PObj
  let A : Type u := AObj
  let X₀ : Type u := XObj
  letI rOpen : CommRing O := _root_.CommRingCat.commRing OObj
  letI rPrime : CommRing S := _root_.CommRingCat.commRing SObj
  letI rPullback : CommRing P := _root_.CommRingCat.commRing PObj
  letI rAux : CommRing A := _root_.CommRingCat.commRing AObj
  letI rXStalk : CommRing X₀ := _root_.CommRingCat.commRing XObj
  let δP : P →+* O := (v.stalkMap ηU).hom
  let δS : S →+* P := ((pullback.fst z T.f).stalkMap η').hom
  let δA : A →+* P := ((pullback.snd z T.f).stalkMap η').hom
  let δX : X₀ →+* O := ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom
  letI algR'O' : Algebra S P :=
    δS.toAlgebra
  letI algO'O : Algebra P O :=
    δP.toAlgebra
  letI algR'O : Algebra S O :=
    (δP.comp δS).toAlgebra
  haveI originalPrimePullbackOpen : IsScalarTower S P
      O := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  letI algRR' : Algebra R S := stalkAlgebra z ζ₀
  have halgZ : Z.fromSpecStalk ζ₀ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R S)) :=
    fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra z ζ₀
  letI algRO' : Algebra R P := ((algebraMap S P).comp (algebraMap R S)).toAlgebra
  letI algRO : Algebra R O := ((algebraMap S O).comp (algebraMap R S)).toAlgebra
  haveI originalRPrimePullback : IsScalarTower R S P := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI originalRPrimeOpen : IsScalarTower R S O := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R P O := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have halgO : (U₀ : Scheme.{u}).fromSpecStalk ηU ≫ (U₀.ι ≫ pullback.fst z f ≫ z) =
      Spec.map (CommRingCat.ofHom (algebraMap R O)) := by
    have hmap : algebraMap R O = stalkAlgebraMap (U₀.ι ≫ pullback.fst z f ≫ z) ηU := by
      show (δP.comp δS).comp (stalkAlgebraMap z ζ₀) = _
      rw [RingHom.comp_assoc, stalkAlgebraMap_comp', stalkAlgebraMap_comp', ← Category.assoc, hv₁, Category.assoc]
    rw [hmap]
    exact fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra (U₀.ι ≫ pullback.fst z f ≫ z) ηU
  letI algRO₁ : Algebra R A := stalkAlgebra T.f y₁
  have halg₁ : T.Y.fromSpecStalk y₁ ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
    fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra T.f y₁
  letI algO₁O' : Algebra A P := δA.toAlgebra
  haveI originalRAuxPullback : IsScalarTower R A P := IsScalarTower.of_algebraMap_eq (fun r => by
    show δS (stalkAlgebraMap z ζ₀ r) =
      δA (stalkAlgebraMap T.f y₁ r)
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, stalkAlgebraMap_comp', stalkAlgebraMap_comp', pullback.condition])
  letI algO₁O : Algebra A O := ((algebraMap P O).comp (algebraMap A P)).toAlgebra
  haveI originalAuxPullbackOpen : IsScalarTower A P O := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI originalRAuxOpen : IsScalarTower R A O := IsScalarTower.of_algebraMap_eq (fun x => by
    show _ = algebraMap P O (algebraMap A P (algebraMap R A x))
    rw [← IsScalarTower.algebraMap_apply R A P, ← IsScalarTower.algebraMap_apply R P O])

  letI algRX : Algebra R X₀ := stalkAlgebra f ξ
  have halgX : X.fromSpecStalk ξ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R X₀)) :=
    fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra f ξ
  letI algXO : Algebra X₀ O := δX.toAlgebra
  have hpin1 : (δP.comp δS).comp (stalkAlgebraMap z ζ₀) =
      stalkAlgebraMap (U₀.ι ≫ pullback.fst z f ≫ z) ηU := by
    rw [RingHom.comp_assoc, stalkAlgebraMap_comp', stalkAlgebraMap_comp', ← Category.assoc, hv₁, Category.assoc]
  have hpin2 : δX.comp (stalkAlgebraMap f ξ) =
      stalkAlgebraMap (U₀.ι ≫ pullback.fst z f ≫ z) ηU := by
    have h := stalkAlgebraMap_comp' (U₀.ι ≫ pullback.snd z f) f ηU
    rw [Category.assoc, ← pullback.condition] at h
    exact h
  haveI originalRXOpen : IsScalarTower R X₀ O := IsScalarTower.of_algebraMap_eq (fun r =>
    (RingHom.congr_fun hpin1 r).trans (RingHom.congr_fun hpin2 r).symm)

  have hClosedGeometryIndex :=
    @closed_geometry_and_index_construction
      R rBase domainBase dvrBase K givenK aRK fractionRK XK gK
      smoothGeneric separatedGeneric finiteTypeGeneric compactGeneric
      LXK d dimensionGeneric ω hωframe X f e
      smoothX separatedX finiteTypeX compactX isoGenericX Z z smoothZ compactZ
      uK η hη hmax T U₀ hηU τ₀ hτ₀ v hv₁ hv₂ hgen algRR' algRO halgZ halgO
  obtain ⟨hgen₁, hmaxU, hy₁sp, hξsp, hξmax, hζ₀sp, hζ₀max,
      hdomO, hdomO', hfrac, hIndexO, hIndexZ⟩ := hClosedGeometryIndex
  haveI := hdomO; haveI := hdomO'
  obtain ⟨hdomO2, hdvrO, hlocO, hidxO⟩ := hIndexO
  haveI := hdvrO; haveI := hlocO
  obtain ⟨hdomR', hdvrR', hlocR', hidxR'⟩ := hIndexZ
  haveI := hdomR'; haveI := hdvrR'; haveI := hlocR'
  have hRR'_map := @ConstructionInterface.index_one_map_maximalIdeal_fixed R S
    rBase inferInstance rPrime inferInstance algRR' hlocR' hidxR'
  haveI originalPrimeOpenLocal : IsLocalHom (algebraMap S O) :=
    RingHom.isLocalHom_comp δP δS
  have hO : Ideal.map (algebraMap S O) (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ := by
    rw [← hidxR'.map_maximalIdeal, Ideal.map_map]
    exact hidxO.map_maximalIdeal

  have hUniformizerExists := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ϖ, hϖirr⟩ := hUniformizerExists
  have hUniformizerArithmetic :=
    ConstructionInterface.uniformizer_arithmetic_facts R S
      O
      (aRS := algRR') (aRO := algRO) (aSO := algR'O)
      ϖ hϖirr hidxR'.map_maximalIdeal hidxO.map_maximalIdeal
  obtain ⟨hϖ, hϖO, hϖR', hinjRO, hinjRR', hinjR'O⟩ := hUniformizerArithmetic
  have hinjXO : Function.Injective (algebraMap X₀ O) :=
    ConstructionInterface.closed_stalk_uniformizer_injective f ξ
      O
      (rBase := rBase) (domO := hdomO)
      (aRX := algRX) (aRO := algRO) (aXO := algXO)
      hξsp hξmax halgX ϖ hϖ hϖO
  let F := FractionRing O
  letI fieldOpen : Field F := @FractionRing.field O rOpen hdomO
  let canonicalAuxField : Algebra A F := inferInstance
  let canonicalBaseField : Algebra R F := inferInstance
  haveI originalPrimePullbackField : IsScalarTower S P F := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply P O F, IsScalarTower.algebraMap_apply S O F,
      ← IsScalarTower.algebraMap_apply S P O])
  haveI : IsScalarTower R S F := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply S O F, IsScalarTower.algebraMap_apply R O F,
      ← IsScalarTower.algebraMap_apply R S O])
  haveI originalRAuxField : IsScalarTower R A F := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply A O F, IsScalarTower.algebraMap_apply R O F,
      ← IsScalarTower.algebraMap_apply R A O])
  haveI originalRXFTower : IsScalarTower R X₀ F := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply X₀ O F, IsScalarTower.algebraMap_apply R O F,
      ← IsScalarTower.algebraMap_apply R X₀ O])

  have hNativeFractionLifts :=
    @native_fraction_lift_construction R K S O
      rBase domainBase dvrBase givenK aRK fractionRK rPrime hdomR' rOpen hdomO
      algRR' algRO algR'O originalRPrimeOpen ϖ hϖirr hinjRO hinjRR' hinjR'O
  obtain ⟨algKF, algKK', algK'F, faithfulRF, faithfulRKprime, faithfulSF,
      towerRSKprime, towerROF, towerSOF, towerRSF, towerRKF, towerRKKprime,
      towerSKprimeF, towerRKprimeF, towerKKprimeF⟩ := hNativeFractionLifts
  haveI : IsScalarTower R S (FractionRing S) := towerRSKprime
  haveI : IsScalarTower R O F := towerROF
  haveI : IsScalarTower S O F := towerSOF
  haveI : IsScalarTower R S F := towerRSF
  haveI : FaithfulSMul R F := faithfulRF
  letI := algKF
  haveI originalRKOpen : IsScalarTower R K F := towerRKF
  let K' := FractionRing S
  letI fieldPrime : Field K' := @FractionRing.field S rPrime hdomR'
  haveI : FaithfulSMul R K' := faithfulRKprime
  letI := algKK'
  haveI originalRKKprime : IsScalarTower R K K' := towerRKKprime
  haveI : FaithfulSMul S F := faithfulSF
  letI := algK'F
  haveI originalPrimeFractionField : IsScalarTower S K' F := towerSKprimeF
  haveI : IsScalarTower R K' F := towerRKprimeF
  haveI originalKKprimeOpen : IsScalarTower K K' F := towerKKprimeF

  have hDeltaTranslation :=
    @pullback_delta_translation_construction
      R rBase domainBase dvrBase K givenK aRK fractionRK XK gK
      smoothGeneric separatedGeneric finiteTypeGeneric compactGeneric
      LXK d dimensionGeneric ω X f e
      smoothX separatedX finiteTypeX compactX isoGenericX Z z smoothZ compactZ
      uK η T U₀ hηU τ₀ hτ₀ v hv₁ hv₂ algRO' hdomR' hdomO ϖ hϖirr
      algRR' halgZ algRO halgO algRO₁ halg₁ algKK' towerRSKprime originalRKKprime
      algKF algK'F towerROF originalRKOpen originalKKprimeOpen
      originalRPrimePullback originalRAuxPullback towerSKprimeF originalRAuxField
  obtain ⟨hbc', htrans⟩ := hDeltaTranslation

  have hC3 :=
    @chart_generic_field_witness_construction
      R rBase domainBase dvrBase K givenK aRK fractionRK XK gK d dimensionGeneric
      ω hωframe X f Z z η T U₀ hηU v ϖ hϖ hy₁sp hgen₁ algRO₁ halg₁ hdomO
      canonicalAuxField canonicalBaseField algKF originalRAuxField originalRKOpen
  obtain ⟨U'', hU'', algU'', hKU'', hx'', ωU'', hωU'', b₁, w₁, hread⟩ := hC3

  have hComponentChartWitness :=
    @exists_component_chart_reading_data
      R rBase domainBase dvrBase K givenK aRK fractionRK XK gK
      smoothGeneric separatedGeneric finiteTypeGeneric compactGeneric
      d dimensionGeneric ω D X f e V j smoothX separatedX finiteTypeX compactX isoGenericX
      hyV hVK hjopen hjchart hcover Z z T η U₀ hηU v
      hdomO algKF hξsp hξmax halgX originalRKOpen originalRXFTower hinjXO
  obtain ⟨c, φ, hc, hφbij, hφloc, hφR, algF₀F, hTowO₀, hTowK, hxX⟩ := hComponentChartWitness
  let C : ComponentReading R K gK d ω := D.C c
  let O₀Obj := C.Y.presheaf.stalk C.y
  let O₀ : Type u := O₀Obj
  letI rComponent : CommRing O₀ := _root_.CommRingCat.commRing O₀Obj
  letI domainComponent : IsDomain O₀ := C.isDomain
  let F₀ : Type u := FractionRing O₀
  letI fieldComponent : Field F₀ := @FractionRing.field O₀ rComponent domainComponent
  let BcObj := Γ(XK, C.U)
  let Bc : Type u := BcObj
  letI rSections : CommRing Bc := _root_.CommRingCat.commRing BcObj
  letI := C.algebra
  letI := C.algebraK
  haveI := C.isScalarTower
  letI := algF₀F
  letI algO₀O : Algebra O₀ O := ((algebraMap X₀ O).comp φ).toAlgebra
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) C.U
  letI := C.algebraU
  letI algUcF : Algebra Bc F := ((algebraMap F₀ F).comp (algebraMap Bc F₀)).toAlgebra
  have hComponentStalkData :=
    @component_chart_stalk_tower_index_data
      R rBase domainBase dvrBase K givenK aRK XK gK d ω D X f Z z T η U₀ hηU v
      hdomO originalRXOpen towerROF c φ hφloc hφR algF₀F hTowO₀
  obtain ⟨originalComponentFractionOpen, originalRComponentOpen, originalRComponentField,
      originalComponentOpenLocal, hdomO₀, hdvrO₀, hlocO₀, hidxO₀⟩ := hComponentStalkData
  haveI := originalComponentFractionOpen
  haveI := originalRComponentOpen
  haveI := originalRComponentField
  haveI := originalComponentOpenLocal
  haveI : IsScalarTower K F₀ F := hTowK
  haveI := hlocO₀
  have hbc :=
    @component_chart_delta_zero_bijective
      R rBase domainBase dvrBase K givenK aRK XK gK d ω D X f Z z T η U₀ hηU v hv₁
      c φ hφbij hφR halgZ halgX originalRPrimeOpen originalRComponentOpen
  let BuObj := Γ(XK, U'')
  let Bu : Type u := BuObj
  letI rUSections : CommRing Bu := _root_.CommRingCat.commRing BuObj
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''
  letI : Algebra Bu F := algU''
  haveI := hKU''
  have hComponentSectionTowers :=
    @component_chart_section_field_towers
      R rBase domainBase dvrBase K givenK aRK XK gK d ω D X f Z z η U₀ hηU
      hdomO algKF c algF₀F hTowK
  obtain ⟨hKUc, towUcF₀F⟩ := hComponentSectionTowers
  haveI := hKUc
  haveI : IsScalarTower Bc F₀ F := towUcF₀F
  have h23 :=
    @component_chart_reading_image
      R rBase domainBase dvrBase K givenK aRK XK gK d ω D X f Z z T η U₀ hηU v
      hdomO hdomR' algKF algKK' algK'F c algF₀F hTowK originalKKprimeOpen hKUc towUcF₀F

  haveI smoothPullbackFst : Smooth (pullback.fst z f) := inferInstance
  letI lfpPullbackFst : LocallyOfFinitePresentation (pullback.fst z f) := inferInstance
  letI lfpComparison : LocallyOfFinitePresentation (v ≫ pullback.fst z T.f) := by
    haveI : Smooth (v ≫ pullback.fst z T.f) := by rw [hv₁]; infer_instance
    infer_instance

  have hFront :=
    @paired_stalk_front_outputs
      R rBase domainBase dvrBase K givenK aRK fractionRK XK gK d ω LXK hleft D
      X f e Z z uK T η U₀ hηU v hv₁
      hdomO hdomR' hfrac algKF algKK' algK'F
      towerRSKprime towerROF originalRKOpen originalRKKprime originalKKprimeOpen
      originalRAuxField originalRXFTower halgZ halgO halg₁ halgX htrans
      c algF₀F hTowK hKUc U'' hU'' algU'' hKU'' hx'' ωU'' hωU'' hxX
  have hPair :=
    @paired_stalk_construction_outputs
      R rBase domainBase dvrBase K givenK aRK fractionRK XK gK d ω D hD X f Z z T η U₀ hηU v
      hdomO hdomR' hdomO' hdvrO hdvrR' hlocR' originalPrimeOpenLocal
      originalPrimePullbackOpen originalRPrimePullback originalRPrimeOpen
      originalRAuxPullback originalAuxPullbackOpen originalRAuxOpen originalRXOpen
      originalPrimePullbackField originalRAuxField hRR'_map hO ϖ hϖ
      algKF algKK' algK'F originalRKKprime originalPrimeFractionField originalRKOpen originalKKprimeOpen
      hbc' c φ algF₀F hTowK originalComponentFractionOpen originalRComponentOpen originalRComponentField
      originalComponentOpenLocal hdomO₀ hdvrO₀ hlocO₀ hidxO₀ hKUc towUcF₀F hbc
      U'' hU'' algU'' hKU'' ωU'' b₁ w₁ hread h23 hFront
  have hFinal :=
    @formal_smoothness_and_paired_outputs_construction
      R rBase domainBase dvrBase K givenK aRK XK gK d ω D X f smoothX Z z smoothZ
      T η U₀ hηU v hv₁ lfpPullbackFst lfpComparison hPair
  exact hFinal

end P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
end ZInQ.Contrib.CloudR2NeronExistence.Henselian

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

namespace G2Glue
h77_bridge_namespace

theorem pointGenericFibre_comp_genericFibreRestrict
    {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
    {X U : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (u : U ⟶ Spec (CommRingCat.of R))
    (q : U ⟶ X) (hq : q ≫ f = u) (η : U) (x : X)
    [Algebra R (U.presheaf.stalk η)]
    (halgU : U.fromSpecStalk η ≫ u = Spec.map (CommRingCat.ofHom (algebraMap R (U.presheaf.stalk η))))
    [Algebra R (X.presheaf.stalk x)]
    (halgX : X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk x))))
    (F : Type u) [CommRing F] [Algebra (U.presheaf.stalk η) F] [Algebra (X.presheaf.stalk x) F]
    [Algebra R F] [Algebra K F] [IsScalarTower R (U.presheaf.stalk η) F]
    [IsScalarTower R (X.presheaf.stalk x) F] [IsScalarTower R K F]
    (hF : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) F)) ≫ X.fromSpecStalk x =
      Spec.map (CommRingCat.ofHom (algebraMap (U.presheaf.stalk η) F)) ≫ U.fromSpecStalk η ≫ q) :
    (pointGenericFibre (K := K) (K' := F)
        (⟨U.fromSpecStalk η, halgU⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (U.presheaf.stalk η)))) u)).1 ≫
      (genericFibreRestrict R K f u ⟨q, hq⟩).1 =
    (pointGenericFibre (K := K) (K' := F)
        (⟨X.fromSpecStalk x, halgX⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk x)))) f)).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, pointGenericFibre_coe_comp_fst, hF]
    simp only [genericFibreRestrict, pullback.lift_fst]
    rw [← Category.assoc, pointGenericFibre_coe_comp_fst, Category.assoc]
  · rw [Category.assoc, pointGenericFibre_coe_comp_snd]
    simp only [genericFibreRestrict, pullback.lift_snd]
    rw [pointGenericFibre_coe_comp_snd]

end G2Glue

namespace T3Glue
h77_bridge_namespace

theorem exists_affine_chart_of_point
    {K : Type u} [Field K] {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤))
    (F : Type u) [Field F] [Algebra K F] (φ : Spec (CommRingCat.of F) ⟶ XK)
    (hφ : φ ≫ gK = Spec.map (CommRingCat.ofHom (algebraMap K F))) :
    ∃ (U'' : XK.Opens) (hU'' : IsAffineOpen U'') (algU'' : Algebra Γ(XK, U'') F)
      (_ : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''; IsScalarTower K Γ(XK, U'') F)
      (_ : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U'') F)) ≫ hU''.fromSpec = φ)
      (ωU'' : ⋀[Γ(XK, U'')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U''))),
      (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gK) d U'' ωU'' = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d).presheaf.map (homOfLE le_top).op ω := by
  classical

  let pt : ↥(Spec (CommRingCat.of F)) := (default : PrimeSpectrum F)
  have hpt : ∀ q : ↥(Spec (CommRingCat.of F)), q = pt := fun q => Subsingleton.elim (α := PrimeSpectrum F) q pt
  obtain ⟨_, ⟨(U'' : XK.Opens), (hU'' : IsAffineOpen U''), rfl⟩, hxU, -⟩ :=
    XK.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (φ.base pt)) isOpen_univ

  have hrange : Set.range φ.base ⊆ Set.range U''.ι.base := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι, hpt q]
    exact hxU
  have hl : IsOpenImmersion.lift U''.ι φ hrange ≫ U''.ι = φ := IsOpenImmersion.lift_fac _ _ _
  let ρ : Γ(XK, U'') ⟶ CommRingCat.of F := Spec.preimage (IsOpenImmersion.lift U''.ι φ hrange ≫ hU''.isoSpec.hom)
  have hρ : Spec.map ρ ≫ hU''.fromSpec = φ := by
    rw [Spec.map_preimage, Category.assoc, ← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc, hl]
  letI algU'' : Algebra Γ(XK, U'') F := ρ.hom.toAlgebra
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''

  have hK : CommRingCat.ofHom (algebraMap K F) =
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ gK.appLE ⊤ U'' le_top) ≫ ρ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
      IsAffineOpen.SpecMap_appLE_fromSpec gK (isAffineOpen_top _) hU'' le_top, reassoc_of% hρ, hφ]
  have htower : IsScalarTower K Γ(XK, U'') F :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hK)
  obtain ⟨ωU'', hω⟩ := (AlgebraicGeometry.Scheme.Hom.topToSections_bijective_of_isAffineOpen gK d hU'').2
    (((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d).presheaf.map (homOfLE le_top).op ω)
  exact ⟨U'', hU'', algU'', htower, hρ, ωU'', hω⟩

end T3Glue

namespace T3Glue
h77_bridge_namespace

theorem bijective_map_comp_mapBaseChange_stalk_of_isOpenImmersion
    {R : Type u} [CommRing R] {X Z U : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : Z ⟶ Spec (CommRingCat.of R))
    (ι : U ⟶ pullback z f) [IsOpenImmersion ι] (u : ↥U)
    (g : U ⟶ Z) (hg : g = ι ≫ pullback.fst z f) (ζ : ↥Z) (hζ : g.base u = ζ)
    [Algebra R (Z.presheaf.stalk ζ)]
    (halgZ : Z.fromSpecStalk ζ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ζ))))
    [Algebra R (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))]
    (halgX : X.fromSpecStalk ((pullback.snd z f).base (ι.base u)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base (ι.base u))))))
    (O₀ : Type u) [CommRing O₀] [Algebra R O₀] (φ : O₀ →+* (X.presheaf.stalk ((pullback.snd z f).base (ι.base u))))
    (hφ : Function.Bijective φ) (hφR : φ.comp (algebraMap R O₀) = algebraMap R (X.presheaf.stalk ((pullback.snd z f).base (ι.base u))))
    [Algebra R (U.presheaf.stalk u)] [Algebra (Z.presheaf.stalk ζ) (U.presheaf.stalk u)] [Algebra O₀ (U.presheaf.stalk u)]
    (hA : ∀ a, algebraMap (Z.presheaf.stalk ζ) (U.presheaf.stalk u) a =
      (g.stalkMap u).hom ((Z.presheaf.stalkCongr (.of_eq hζ.symm)).hom a))
    (hB : ∀ b, algebraMap O₀ (U.presheaf.stalk u) b = ((ι ≫ pullback.snd z f).stalkMap u).hom (φ b))
    [IsScalarTower R (Z.presheaf.stalk ζ) (U.presheaf.stalk u)] [IsScalarTower R O₀ (U.presheaf.stalk u)] :
    Function.Bijective
      ((KaehlerDifferential.map R (Z.presheaf.stalk ζ) (U.presheaf.stalk u) (U.presheaf.stalk u)).restrictScalars (U.presheaf.stalk u) ∘ₗ
        KaehlerDifferential.mapBaseChange R O₀ (U.presheaf.stalk u)) := by
  subst hζ
  subst hg
  have hpt : (ι ≫ pullback.fst z f).base u = (pullback.fst z f).base (ι.base u) := rfl

  have hA' : ∀ a, algebraMap (Z.presheaf.stalk ((ι ≫ pullback.fst z f).base u)) (U.presheaf.stalk u) a =
      (ι.stalkMap u).hom (((pullback.fst z f).stalkMap (ι.base u)).hom a) := by
    intro a
    rw [hA, Scheme.Hom.stalkMap_comp]
    simp [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]
  have hB' : ∀ b, algebraMap O₀ (U.presheaf.stalk u) b =
      (ι.stalkMap u).hom (((pullback.snd z f).stalkMap (ι.base u)).hom (φ b)) := by
    intro b
    rw [hB, Scheme.Hom.stalkMap_comp]
    rfl

  letI instZ : Algebra R (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) := ‹Algebra R (Z.presheaf.stalk ((ι ≫ pullback.fst z f).base u))›
  letI instZO : Algebra (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) (U.presheaf.stalk u) := ‹Algebra (Z.presheaf.stalk ((ι ≫ pullback.fst z f).base u)) (U.presheaf.stalk u)›
  haveI : IsScalarTower R (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) (U.presheaf.stalk u) := ‹IsScalarTower R (Z.presheaf.stalk ((ι ≫ pullback.fst z f).base u)) (U.presheaf.stalk u)›
  obtain ⟨𝔔, h𝔔, e, he₁, he₂⟩ := AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk f z (ι.base u) halgZ halgX
  haveI : 𝔔.IsPrime := h𝔔

  let ιu : ((pullback z f).presheaf.stalk (ι.base u)) ≃+* (U.presheaf.stalk u) := (asIso (ι.stalkMap u)).commRingCatIsoToRingEquiv
  have hιu : ∀ s, ιu s = (ι.stalkMap u).hom s := fun _ => rfl
  let eO : (U.presheaf.stalk u) ≃+* Localization.AtPrime 𝔔 := ιu.symm.trans e
  letI algT : Algebra ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (U.presheaf.stalk u) :=
    (eO.symm.toRingHom.comp (algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (Localization.AtPrime 𝔔))).toAlgebra
  have halgT : ∀ t, algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (U.presheaf.stalk u) t = ιu (e.symm (algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (Localization.AtPrime 𝔔) t)) :=
    fun _ => rfl
  let eT : Localization.AtPrime 𝔔 ≃ₐ[((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u))))] (U.presheaf.stalk u) := AlgEquiv.ofRingEquiv (f := eO.symm) (fun _ => rfl)
  haveI hlocT : IsLocalization 𝔔.primeCompl (U.presheaf.stalk u) := IsLocalization.isLocalization_of_algEquiv 𝔔.primeCompl eT

  let φₐ : O₀ ≃ₐ[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u))) :=
    AlgEquiv.ofBijective { toRingHom := φ, commutes' := fun r => RingHom.congr_fun hφR r } hφ
  have hφₐ : ∀ b, φₐ b = φ b := fun _ => rfl
  let Ψ : ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀) ≃ₐ[R] ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) := Algebra.TensorProduct.congr AlgEquiv.refl φₐ
  have hΨ : ∀ (a : (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))) (b : O₀), Ψ (a ⊗ₜ[R] b) = a ⊗ₜ[R] φ b := fun a b => by
    show Algebra.TensorProduct.map (AlgEquiv.refl : (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ≃ₐ[R] (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))).toAlgHom φₐ.toAlgHom (a ⊗ₜ[R] b) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  letI algT₀ : Algebra ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀) (U.presheaf.stalk u) :=
    ((algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (U.presheaf.stalk u)).comp (Ψ.symm.toRingEquiv).symm.toRingHom).toAlgebra
  haveI hloc₀ : IsLocalization (𝔔.primeCompl.map (Ψ.symm.toRingEquiv : ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) ≃* ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀))) (U.presheaf.stalk u) :=
    IsLocalization.isLocalization_of_base_ringEquiv 𝔔.primeCompl (U.presheaf.stalk u) Ψ.symm.toRingEquiv
  have halgT₀ : ∀ t, algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀) (U.presheaf.stalk u) t = algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (U.presheaf.stalk u) (Ψ t) := by
    intro t
    show algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (U.presheaf.stalk u) ((Ψ.symm.toRingEquiv).symm t) = _
    simp

  haveI : IsScalarTower (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀) (U.presheaf.stalk u) :=
    IsScalarTower.of_algebraMap_eq (R := (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))) (S := ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀)) (A := (U.presheaf.stalk u)) fun a => by
      rw [halgT₀, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hΨ, map_one,
        halgT, ← he₁, RingEquiv.symm_apply_apply, hιu]
      exact hA' a
  have hBT : (algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀) (U.presheaf.stalk u)).comp
      (Algebra.TensorProduct.includeRight (R := R) (A := (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))) (B := O₀)).toRingHom =
      algebraMap O₀ (U.presheaf.stalk u) := by
    refine RingHom.ext fun b => ?_
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply,
      halgT₀, hΨ, halgT, ← he₂, RingEquiv.symm_apply_apply, hιu, hB']
  haveI : IsLocalization (⊥ : Submonoid (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))) (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) := IsLocalization.self (by simp)
  exact KaehlerDifferential.bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct R (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) O₀ (U.presheaf.stalk u)
    (⊥ : Submonoid (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))) hBT (𝔔.primeCompl.map (Ψ.symm.toRingEquiv : ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) ≃* ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀)))

end T3Glue

private theorem pullback_stalk_delta_one_fixed
    {R : Type u} [CommRing R] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : Z ⟶ Spec (CommRingCat.of R))
    (p : ↥(pullback z f))
    [Algebra R (Z.presheaf.stalk ((pullback.fst z f).base p))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z f).base p) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z f).base p)))))
    [Algebra R (X.presheaf.stalk ((pullback.snd z f).base p))]
    (halgX : X.fromSpecStalk ((pullback.snd z f).base p) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base p)))))
    [Algebra R ((pullback z f).presheaf.stalk p)]
    (hZ : letI : Algebra (Z.presheaf.stalk ((pullback.fst z f).base p)) ((pullback z f).presheaf.stalk p) :=
      ((pullback.fst z f).stalkMap p).hom.toAlgebra;
      IsScalarTower R (Z.presheaf.stalk ((pullback.fst z f).base p)) ((pullback z f).presheaf.stalk p))
    (hX : letI : Algebra (X.presheaf.stalk ((pullback.snd z f).base p)) ((pullback z f).presheaf.stalk p) :=
      ((pullback.snd z f).stalkMap p).hom.toAlgebra;
      IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base p)) ((pullback z f).presheaf.stalk p)) :
    letI : Algebra (Z.presheaf.stalk ((pullback.fst z f).base p)) ((pullback z f).presheaf.stalk p) :=
      ((pullback.fst z f).stalkMap p).hom.toAlgebra
    letI : Algebra (X.presheaf.stalk ((pullback.snd z f).base p)) ((pullback z f).presheaf.stalk p) :=
      ((pullback.snd z f).stalkMap p).hom.toAlgebra
    Function.Bijective
      ((KaehlerDifferential.map R (Z.presheaf.stalk ((pullback.fst z f).base p))
        ((pullback z f).presheaf.stalk p) ((pullback z f).presheaf.stalk p)).restrictScalars
          ((pullback z f).presheaf.stalk p) ∘ₗ
        KaehlerDifferential.mapBaseChange R (X.presheaf.stalk ((pullback.snd z f).base p))
          ((pullback z f).presheaf.stalk p)) := by
  letI : Algebra (Z.presheaf.stalk ((pullback.fst z f).base p)) ((pullback z f).presheaf.stalk p) :=
    ((pullback.fst z f).stalkMap p).hom.toAlgebra
  letI : Algebra (X.presheaf.stalk ((pullback.snd z f).base p)) ((pullback z f).presheaf.stalk p) :=
    ((pullback.snd z f).stalkMap p).hom.toAlgebra
  exact @AlgebraicGeometry.bijective_kaehlerDifferential_map_comp_mapBaseChange_stalk_pullback
    R inferInstance X Z f z p inferInstance halgZ inferInstance halgX inferInstance hZ hX

theorem tfm_KK (K K' B F : Type u) [Field K] [Field K'] [Algebra K K'] [CommRing B] [Algebra K B] [Field F]
    [Algebra B F] [Algebra K F] [Algebra K' F] [IsScalarTower K B F] [IsScalarTower K K' F]
    (d : ℕ) (ω : ⋀[B]^d (Ω[B⁄K])) :
    TopFormOrder.topFormMap K K' F F d (TopFormOrder.topFormMap K K B F d ω) = TopFormOrder.topFormMap K K' B F d ω := by
  rw [NeronModelInfra.TopFormOrder.topFormMap_topFormMap K K K' B F F d ω]

theorem tfm_KE (K K' B E F : Type u) [Field K] [Field K'] [Algebra K K'] [CommRing B] [Algebra K B] [Field E] [Field F]
    [Algebra B E] [Algebra E F] [Algebra B F] [IsScalarTower B E F]
    [Algebra K E] [IsScalarTower K B E] [Algebra K F] [Algebra K' F] [IsScalarTower K E F] [IsScalarTower K K' F]
    [IsScalarTower K B F]
    (d : ℕ) (ω : ⋀[B]^d (Ω[B⁄K])) :
    TopFormOrder.topFormMap K K' E F d (TopFormOrder.topFormMap K K B E d ω) = TopFormOrder.topFormMap K K' B F d ω := by
  rw [NeronModelInfra.TopFormOrder.topFormMap_topFormMap K K K' B E F d ω]

theorem stalkAlgebraMap_comp' {R : Type u} [CommRing R] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (f : Y ⟶ Spec (CommRingCat.of R)) (x : X) :
    (g.stalkMap x).hom.comp (stalkAlgebraMap f (g.base x)) = stalkAlgebraMap (g ≫ f) x := by
  ext r
  simp only [RingHom.comp_apply, stalkAlgebraMap_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  erw [Scheme.Hom.germ_stalkMap_apply]
  rfl

namespace C7Glue
h77_bridge_namespace

theorem injective_of_map_irreducible_ne_zero {A B : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] (f : A →+* B) (ϖ : A) (hϖ : Irreducible ϖ) (h : f ϖ ≠ 0) :
    Function.Injective f := by
  refine (injective_iff_map_eq_zero f).mpr (fun a ha => ?_)
  by_contra ha0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  rw [map_mul, map_pow] at ha
  exact pow_ne_zero n h ((IsUnit.map f u.isUnit).mul_right_eq_zero.mp ha)

theorem map_uniformizer_ne_zero {A B : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] (f : A →+* B) (ϖ : A)
    (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (h : Ideal.map f (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B) : f ϖ ≠ 0 := by
  intro h0
  rw [hϖ, Ideal.map_span, Set.image_singleton, h0, Ideal.span_singleton_eq_bot.mpr rfl] at h
  exact IsDiscreteValuationRing.not_a_field B h.symm

theorem maximalIdeal_eq_span_map {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (f : A →+* B) (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (h : Ideal.map f (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B) :
    IsLocalRing.maximalIdeal B = Ideal.span {f ϖ} := by
  rw [← h, hϖ, Ideal.map_span, Set.image_singleton]

end C7Glue



private theorem top_form_two_chart_chain_fixed
    (K0 K1 B1 B2 E0 F0 : Type u) [Field K0] [Field K1] [Algebra K0 K1]
    [CommRing B1] [Algebra K0 B1] [CommRing B2] [Algebra K0 B2] [Field E0] [Field F0]
    [Algebra B1 F0] [Algebra K0 F0] [Algebra K1 F0] [IsScalarTower K0 B1 F0] [IsScalarTower K0 K1 F0]
    [Algebra B2 E0] [Algebra E0 F0] [Algebra B2 F0] [IsScalarTower B2 E0 F0]
    [Algebra K0 E0] [IsScalarTower K0 B2 E0] [IsScalarTower K0 E0 F0] [IsScalarTower K0 B2 F0]
    (d : ℕ) (ω1 : ⋀[B1]^d (Ω[B1⁄K0])) (ω2 : ⋀[B2]^d (Ω[B2⁄K0]))
    (θ : ⋀[E0]^d (Ω[E0⁄K0]))
    (hleft : TopFormOrder.topFormMap K0 K1 B1 F0 d ω1 = TopFormOrder.topFormMap K0 K1 B2 F0 d ω2)
    (hread : TopFormOrder.topFormMap K0 K0 B2 E0 d ω2 = θ) :
    TopFormOrder.topFormMap K0 K1 F0 F0 d (TopFormOrder.topFormMap K0 K0 B1 F0 d ω1) =
      TopFormOrder.topFormMap K0 K1 E0 F0 d θ := by
  exact (tfm_KK K0 K1 B1 F0 d ω1).trans
    (hleft.trans ((tfm_KE K0 K1 B2 E0 F0 d ω2).symm.trans
      (congrArg (TopFormOrder.topFormMap K0 K1 E0 F0 d) hread)))

private theorem atomic_order_and_differential_comparison_fixed
    (R K R' K' : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
    (hRR' : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    [Field K'] [Algebra R' K'] [IsFractionRing R' K'] [Algebra K K'] [Algebra R K']
    [IsScalarTower R K K'] [IsScalarTower R R' K']

    (O₀ F₀ : Type u)
    [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra R O₀] [IsLocalHom (algebraMap R O₀)]
    (hO₀ : Ideal.map (algebraMap R O₀) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal O₀)
    [Field F₀] [Algebra O₀ F₀] [IsFractionRing O₀ F₀] [Algebra K F₀] [Algebra R F₀]
    [IsScalarTower R O₀ F₀] [IsScalarTower R K F₀]
    (d : ℕ) (b₀ : Module.Basis (Fin d) O₀ (Ω[O₀⁄R])) (a : F₀) (ha : a ≠ 0)

    (O₁ O' : Type u)
    [CommRing O₁] [Algebra R O₁]
    [CommRing O'] [IsDomain O'] [Algebra R' O'] [Algebra O₁ O'] [Algebra R O']
    [IsScalarTower R O₁ O'] [IsScalarTower R R' O']
    (b₁ : Module.Basis (Fin d) O₁ (Ω[O₁⁄R])) (w₁ : O₁ˣ) (m : ℤ)
    (hbc' : Function.Bijective
      ((KaehlerDifferential.map R R' O' O').restrictScalars O' ∘ₗ KaehlerDifferential.mapBaseChange R O₁ O'))

    (O F : Type u)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O] [IsLocalHom (algebraMap R' O)]
    (hO : Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O)
    [Algebra R O] [IsScalarTower R R' O]
    [Algebra O₀ O] [IsLocalHom (algebraMap O₀ O)] [IsScalarTower R O₀ O]
    [Algebra O' O] [IsScalarTower R' O' O] [Algebra O₁ O] [IsScalarTower O₁ O' O] [IsScalarTower R O₁ O]
    (hbc : Function.Bijective
      ((KaehlerDifferential.map R R' O O).restrictScalars O ∘ₗ KaehlerDifferential.mapBaseChange R O₀ O))
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra O' F] [IsScalarTower O' O F] [IsFractionRing O' F]
    [Algebra K' F] [Algebra R' F] [IsScalarTower R' O F] [IsScalarTower R' O' F] [IsScalarTower R' K' F]
    [Algebra K F] [Algebra R F] [IsScalarTower R O F] [IsScalarTower R K F] [IsScalarTower K K' F]
    [Algebra F₀ F] [Algebra O₀ F] [IsScalarTower O₀ O F] [IsScalarTower O₀ F₀ F] [IsScalarTower K F₀ F]
    [Algebra O₁ F] [IsScalarTower O₁ O F] [IsScalarTower R O₁ F]

    (σ : ⋀[F]^d (Ω[F⁄K]))
    (hT : σ = (algebraMap O₁ F (w₁ : O₁) * algebraMap O₁ F (algebraMap R O₁ ϖ) ^ m) •
        TopFormOrder.topFormMap R K O₁ F d (exteriorPower.ιMulti O₁ d b₁))
    (hX : TopFormOrder.topFormMap K K' F F d σ =
        TopFormOrder.topFormMap K K' F₀ F d (a • TopFormOrder.topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b₀)))
    (hmin : TopFormOrder.addOrd O₀ F₀ a ≤ m) :
    m = TopFormOrder.addOrd O₀ F₀ a ∧ Function.Bijective (KaehlerDifferential.mapBaseChange R' O' O) :=
  NeronModelInfra.TopFormOrder.eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le
    R K R' K' ϖ hϖ hRR' O₀ F₀ hO₀ d b₀ a ha O₁ O' b₁ w₁ m hbc' O F hO hbc σ hT hX hmin

private theorem component_reading_order_fixed
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} {d : ℕ}
    {ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤)}
    (T : ComponentReading R K gK d ω) :
    T.n = TopFormOrder.addOrd (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) T.a :=
  rfl

private theorem minimality_order_bound_fixed
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} {d : ℕ}
    {ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤)}
    (D : MinimalComponentData R K gK d ω) (hD : D.IsOmegaMinimal) (c : D.ι)
    (T : ComponentReading R K gK d ω) :
    TopFormOrder.addOrd ((D.C c).Y.presheaf.stalk (D.C c).y)
      (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (D.C c).a ≤ T.n := by
  have h := hD.1 c T
  rw [component_reading_order_fixed (D.C c)] at h
  exact h

private theorem index_one_map_maximalIdeal_fixed
    {R0 S0 : Type u} [CommRing R0] [IsLocalRing R0] [CommRing S0] [IsLocalRing S0]
    [Algebra R0 S0] [IsLocalHom (algebraMap R0 S0)] (hidx : IsIndexOneExtension R0 S0) :
    Ideal.map (algebraMap R0 S0) (IsLocalRing.maximalIdeal R0) = IsLocalRing.maximalIdeal S0 :=
  hidx.map_maximalIdeal

private theorem atomic_map_evidence_last_fixed
    (R K R' K' : Type u)
    [rBase : CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    [Field K] [Algebra R K] [IsFractionRing R K]
    [rPrimeBase : CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [algBasePrime : Algebra R R'] [IsLocalHom (algebraMap R R')]
    [Field K'] [Algebra R' K'] [IsFractionRing R' K'] [Algebra K K'] [Algebra R K']
    [IsScalarTower R K K'] [IsScalarTower R R' K']

    (O₀ F₀ : Type u)
    [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra R O₀] [IsLocalHom (algebraMap R O₀)]
    (hO₀ : Ideal.map (algebraMap R O₀) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal O₀)
    [Field F₀] [Algebra O₀ F₀] [IsFractionRing O₀ F₀] [Algebra K F₀] [Algebra R F₀]
    [IsScalarTower R O₀ F₀] [IsScalarTower R K F₀]
    (d : ℕ) (b₀ : Module.Basis (Fin d) O₀ (Ω[O₀⁄R])) (a : F₀) (ha : a ≠ 0)

    (O₁ O' : Type u)
    [CommRing O₁] [Algebra R O₁]
    [CommRing O'] [IsDomain O'] [Algebra R' O'] [Algebra O₁ O'] [Algebra R O']
    [IsScalarTower R O₁ O'] [IsScalarTower R R' O']
    (b₁ : Module.Basis (Fin d) O₁ (Ω[O₁⁄R])) (w₁ : O₁ˣ) (m : ℤ)
    (hbc' : Function.Bijective
      ((KaehlerDifferential.map R R' O' O').restrictScalars O' ∘ₗ KaehlerDifferential.mapBaseChange R O₁ O'))

    (O F : Type u)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O] [IsLocalHom (algebraMap R' O)]
    (hO : Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O)
    [Algebra R O] [IsScalarTower R R' O]
    [Algebra O₀ O] [IsLocalHom (algebraMap O₀ O)] [IsScalarTower R O₀ O]
    [Algebra O' O] [IsScalarTower R' O' O] [Algebra O₁ O] [IsScalarTower O₁ O' O] [IsScalarTower R O₁ O]
    (hbc : Function.Bijective
      ((KaehlerDifferential.map R R' O O).restrictScalars O ∘ₗ KaehlerDifferential.mapBaseChange R O₀ O))
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra O' F] [IsScalarTower O' O F] [IsFractionRing O' F]
    [Algebra K' F] [Algebra R' F] [IsScalarTower R' O F] [IsScalarTower R' O' F] [IsScalarTower R' K' F]
    [Algebra K F] [Algebra R F] [IsScalarTower R O F] [IsScalarTower R K F] [IsScalarTower K K' F]
    [Algebra F₀ F] [Algebra O₀ F] [IsScalarTower O₀ O F] [IsScalarTower O₀ F₀ F] [IsScalarTower K F₀ F]
    [Algebra O₁ F] [IsScalarTower O₁ O F] [IsScalarTower R O₁ F]

    (σ : ⋀[F]^d (Ω[F⁄K]))
    (hT : σ = (algebraMap O₁ F (w₁ : O₁) * algebraMap O₁ F (algebraMap R O₁ ϖ) ^ m) •
        TopFormOrder.topFormMap R K O₁ F d (exteriorPower.ιMulti O₁ d b₁))
    (hX : TopFormOrder.topFormMap K K' F F d σ =
        TopFormOrder.topFormMap K K' F₀ F d (a • TopFormOrder.topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b₀)))
    (hmin : TopFormOrder.addOrd O₀ F₀ a ≤ m)
    (hRR' : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R') :
    m = TopFormOrder.addOrd O₀ F₀ a ∧ Function.Bijective (KaehlerDifferential.mapBaseChange R' O' O) :=
  atomic_order_and_differential_comparison_fixed R K R' K' ϖ hϖ hRR' O₀ F₀ hO₀
    d b₀ a ha O₁ O' b₁ w₁ m hbc' O F hO hbc σ hT hX hmin

private theorem component_stored_reading_fixed
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} {d : ℕ}
    {ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤)}
    (C : ComponentReading R K gK d ω) :
    letI : Algebra R (C.Y.presheaf.stalk C.y) := C.algebra;
    letI : Algebra K (FractionRing (C.Y.presheaf.stalk C.y)) := C.algebraK;
    letI : Algebra Γ(XK, C.U) (FractionRing (C.Y.presheaf.stalk C.y)) := C.algebraU;
    letI : Algebra K Γ(XK, C.U) :=
      (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) C.U;
    letI : IsScalarTower R K (FractionRing (C.Y.presheaf.stalk C.y)) := C.isScalarTower;
    letI : IsScalarTower K Γ(XK, C.U) (FractionRing (C.Y.presheaf.stalk C.y)) := C.isScalarTowerU;
    TopFormOrder.topFormMap K K Γ(XK, C.U) (FractionRing (C.Y.presheaf.stalk C.y)) d C.ωU =
      C.a • TopFormOrder.topFormMap R K (C.Y.presheaf.stalk C.y) (FractionRing (C.Y.presheaf.stalk C.y)) d
        (exteriorPower.ιMulti (C.Y.presheaf.stalk C.y) d C.b) := by
  letI : Algebra R (C.Y.presheaf.stalk C.y) := C.algebra
  letI : Algebra K (FractionRing (C.Y.presheaf.stalk C.y)) := C.algebraK
  letI : Algebra Γ(XK, C.U) (FractionRing (C.Y.presheaf.stalk C.y)) := C.algebraU
  letI : Algebra K Γ(XK, C.U) :=
    (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) C.U
  haveI : IsScalarTower R K (FractionRing (C.Y.presheaf.stalk C.y)) := C.isScalarTower
  haveI : IsScalarTower K Γ(XK, C.U) (FractionRing (C.Y.presheaf.stalk C.y)) := C.isScalarTowerU
  exact C.ha

private theorem top_form_component_image_fixed
    (K0 K1 B0 E0 F0 : Type u) [Field K0] [Field K1] [Algebra K0 K1]
    [CommRing B0] [Algebra K0 B0] [Field E0] [Field F0]
    [Algebra B0 E0] [Algebra E0 F0] [Algebra B0 F0] [IsScalarTower B0 E0 F0]
    [Algebra K0 E0] [IsScalarTower K0 B0 E0] [Algebra K0 F0] [Algebra K1 F0]
    [IsScalarTower K0 E0 F0] [IsScalarTower K0 K1 F0] [IsScalarTower K0 B0 F0]
    (d : ℕ) (ω0 : ⋀[B0]^d (Ω[B0⁄K0])) (θ0 : ⋀[E0]^d (Ω[E0⁄K0]))
    (hread : TopFormOrder.topFormMap K0 K0 B0 E0 d ω0 = θ0) :
    TopFormOrder.topFormMap K0 K1 B0 F0 d ω0 = TopFormOrder.topFormMap K0 K1 E0 F0 d θ0 :=
  (tfm_KE K0 K1 B0 E0 F0 d ω0).symm.trans
    (congrArg (TopFormOrder.topFormMap K0 K1 E0 F0 d) hread)

private theorem four_endpoint_equality_fixed
    (W : Type u) (x0 x1 x2 x3 : W)
    (h01 : x0 = x1) (h12 : x1 = x2) (h23 : x2 = x3) :
    x0 = x3 :=
  Eq.trans h01 (Eq.trans h12 h23)

private theorem section_kaehler_tfm_KK_fixed
    (K0 K1 F0 : Type u) [Field K0] [Field K1] [Field F0]
    [a01 : Algebra K0 K1] [a0F : Algebra K0 F0] [a1F : Algebra K1 F0]
    [IsScalarTower K0 K1 F0]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K0)) (U : XK.Opens) (d : ℕ)
    (aUF : Algebra Γ(XK, U) F0)
    (hKU : letI : Algebra K0 Γ(XK, U) :=
      (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U;
      letI : Algebra Γ(XK, U) F0 := aUF;
      IsScalarTower K0 Γ(XK, U) F0)
    (ωU : ⋀[Γ(XK, U)]^d
      ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U))) :
    letI : Algebra K0 Γ(XK, U) :=
      (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U;
    letI : Algebra Γ(XK, U) F0 := aUF;
    letI : IsScalarTower K0 Γ(XK, U) F0 := hKU;
    TopFormOrder.topFormMap K0 K1 F0 F0 d (TopFormOrder.topFormMap K0 K0 Γ(XK, U) F0 d ωU) =
      TopFormOrder.topFormMap K0 K1 Γ(XK, U) F0 d ωU := by
  letI : Algebra K0 Γ(XK, U) :=
    (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U
  letI : Algebra Γ(XK, U) F0 := aUF
  haveI : IsScalarTower K0 Γ(XK, U) F0 := hKU
  exact tfm_KK K0 K1 Γ(XK, U) F0 d ωU

private theorem section_kaehler_operator_fixed
    (K0 K1 F0 : Type u) [Field K0] [Field K1] [Field F0]
    [a01 : Algebra K0 K1] [a0F : Algebra K0 F0] [a1F : Algebra K1 F0]
    [IsScalarTower K0 K1 F0]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K0)) (U : XK.Opens) (d : ℕ)
    (aUF : Algebra Γ(XK, U) F0)
    (hKU : letI : Algebra K0 Γ(XK, U) :=
      (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U;
      letI : Algebra Γ(XK, U) F0 := aUF;
      IsScalarTower K0 Γ(XK, U) F0) :
    letI : Algebra K0 Γ(XK, U) :=
      (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U;
    letI : Algebra Γ(XK, U) F0 := aUF;
    letI : IsScalarTower K0 Γ(XK, U) F0 := hKU;
    (fun s : ⋀[Γ(XK, U)]^d
      ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U)) =>
      TopFormOrder.topFormMap K0 K1 F0 F0 d (TopFormOrder.topFormMap K0 K0 Γ(XK, U) F0 d s)) =
    (fun s : ⋀[Γ(XK, U)]^d
      ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U)) =>
      TopFormOrder.topFormMap K0 K1 Γ(XK, U) F0 d s) := by
  letI : Algebra K0 Γ(XK, U) :=
    (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U
  letI : Algebra Γ(XK, U) F0 := aUF
  haveI : IsScalarTower K0 Γ(XK, U) F0 := hKU
  funext s
  exact tfm_KK K0 K1 Γ(XK, U) F0 d s

private theorem fixed_function_evaluation
    (V W : Type u) (f g : V → W) (h : f = g) (v : V) : f v = g v :=
  congrFun h v

private theorem closed_fibre_point_facts
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} {d : ℕ}
    {ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤)}
    {X Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (z : Z ⟶ Spec (CommRingCat.of R))
    [Smooth f] [Smooth z] (T : ComponentReading R K gK d ω)
    (U₀ : (pullback z f).Opens) (η : ↥(pullback z f)) (hηU : η ∈ U₀)
    (hη : (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R)
    (hmax : ∀ y : ↥(pullback z f), y ⤳ η →
      (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η)
    (τ₀ : SchemeHomOver (U₀.ι ≫ pullback.fst z f ≫ z) T.f)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f)
    (hv₁ : v ≫ pullback.fst z T.f = U₀.ι ≫ pullback.fst z f)
    (hv₂ : v ≫ pullback.snd z T.f = τ₀.1)
    (hgen : T.y ⤳ τ₀.1.base ⟨η, hηU⟩) :
    let ηU : ↥U₀ := ⟨η, hηU⟩;
    let η' : ↥(pullback z T.f) := v.base ηU;
    let ζ₀ : ↥Z := (pullback.fst z T.f).base η';
    let y₁ : ↥T.Y := (pullback.snd z T.f).base η';
    (T.y ⤳ y₁) ∧
    (∀ y : ↥U₀, y ⤳ ηU → (U₀.ι ≫ pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = ηU) ∧
    (T.f.base y₁ = IsLocalRing.closedPoint R) ∧
    (f.base ((pullback.snd z f).base (U₀.ι.base ηU)) = IsLocalRing.closedPoint R) ∧
    (∀ y : ↥X, y ⤳ ((pullback.snd z f).base (U₀.ι.base ηU)) →
      f.base y = IsLocalRing.closedPoint R → y = ((pullback.snd z f).base (U₀.ι.base ηU))) ∧
    (z.base ζ₀ = IsLocalRing.closedPoint R) ∧
    (∀ y : ↥Z, y ⤳ ζ₀ → z.base y = IsLocalRing.closedPoint R → y = ζ₀) := by
  let ηU : ↥U₀ := ⟨η, hηU⟩
  let η' : ↥(pullback z T.f) := v.base ηU
  let ζ₀ : ↥Z := (pullback.fst z T.f).base η'
  have hζ₀ : (U₀.ι ≫ pullback.fst z f).base ηU = ζ₀ := by
    show (U₀.ι ≫ pullback.fst z f).base ηU = (v ≫ pullback.fst z T.f).base ηU
    rw [hv₁]
  let y₁ : ↥T.Y := (pullback.snd z T.f).base η'
  have hy₁ : τ₀.1.base ηU = y₁ := by
    show τ₀.1.base ηU = (v ≫ pullback.snd z T.f).base ηU
    rw [hv₂]
  have hgen₁ : T.y ⤳ y₁ := hy₁ ▸ hgen
  have hmaxU : ∀ y : ↥U₀, y ⤳ ηU → (U₀.ι ≫ pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = ηU := by
    intro y hy hsp
    apply Subtype.ext
    exact hmax (U₀.ι.base y) (hy.map U₀.ι.base.hom.continuous) hsp
  have e₁ : v ≫ pullback.snd z T.f ≫ T.f = U₀.ι ≫ pullback.fst z f ≫ z := by
    rw [← pullback.condition, ← Category.assoc, hv₁, Category.assoc]
  have e₂ : (U₀.ι ≫ pullback.snd z f) ≫ f = U₀.ι ≫ pullback.fst z f ≫ z := by
    rw [Category.assoc, ← pullback.condition]
  have e₃ : (v ≫ pullback.fst z T.f) ≫ z = U₀.ι ≫ pullback.fst z f ≫ z := by
    rw [hv₁, Category.assoc]
  have hηsp : (U₀.ι ≫ pullback.fst z f ≫ z).base ηU = IsLocalRing.closedPoint R := hη
  have hy₁sp : T.f.base y₁ = IsLocalRing.closedPoint R := by
    have h := congrArg (fun φ => φ.base ηU) e₁
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [← hηsp]; exact h
  have hξsp : f.base ((pullback.snd z f).base (U₀.ι.base ηU)) = IsLocalRing.closedPoint R := by
    have h := congrArg (fun φ => φ.base ηU) e₂
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [← hηsp]; exact h
  have hζ₀sp : z.base ζ₀ = IsLocalRing.closedPoint R := by
    have h := congrArg (fun φ => φ.base ηU) e₃
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [← hηsp]; exact h
  have hξmax : ∀ y : ↥X, y ⤳ ((pullback.snd z f).base (U₀.ι.base ηU)) → f.base y = IsLocalRing.closedPoint R → y = ((pullback.snd z f).base (U₀.ι.base ηU)) := by
    intro y hy hysp
    have hy2 : y ⤳ (U₀.ι ≫ pullback.snd z f).base ηU := hy
    obtain ⟨y', hy', rfl⟩ := Flat.generalizingMap (U₀.ι ≫ pullback.snd z f) hy2
    have hsp' : (U₀.ι ≫ pullback.fst z f ≫ z).base y' = IsLocalRing.closedPoint R := by
      rw [← e₂, Scheme.Hom.comp_apply]; exact hysp
    rw [hmaxU y' hy' hsp']
    rfl
  have hζ₀max : ∀ y : ↥Z, y ⤳ ζ₀ → z.base y = IsLocalRing.closedPoint R → y = ζ₀ := by
    intro y hy hysp
    have hy2 : y ⤳ (U₀.ι ≫ pullback.fst z f).base ηU := by rw [hζ₀]; exact hy
    obtain ⟨y', hy', rfl⟩ := Flat.generalizingMap (U₀.ι ≫ pullback.fst z f) hy2
    have hsp' : (U₀.ι ≫ pullback.fst z f ≫ z).base y' = IsLocalRing.closedPoint R := by
      rw [← Category.assoc, Scheme.Hom.comp_apply]; exact hysp
    rw [hmaxU y' hy' hsp']
    exact hζ₀
  exact ⟨hgen₁, hmaxU, hy₁sp, hξsp, hξmax, hζ₀sp, hζ₀max⟩

private theorem paired_closed_stalk_index_facts
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Z U : Scheme.{u}}
    (z : Z ⟶ Spec (CommRingCat.of R)) (u : U ⟶ Spec (CommRingCat.of R))
    [Smooth z] [Smooth u]
    (ζ : ↥Z) (η : ↥U)
    (hζ : z.base ζ = IsLocalRing.closedPoint R)
    (hη : u.base η = IsLocalRing.closedPoint R)
    (hmaxZ : ∀ y : ↥Z, y ⤳ ζ → z.base y = IsLocalRing.closedPoint R → y = ζ)
    (hmaxU : ∀ y : ↥U, y ⤳ η → u.base y = IsLocalRing.closedPoint R → y = η)
    [aRZ : Algebra R (Z.presheaf.stalk ζ)] [aRU : Algebra R (U.presheaf.stalk η)]
    (halgZ : Z.fromSpecStalk ζ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ζ))))
    (halgU : U.fromSpecStalk η ≫ u = Spec.map (CommRingCat.ofHom (algebraMap R (U.presheaf.stalk η)))) :
    (∃ (_ : IsDomain (U.presheaf.stalk η)) (_ : IsDiscreteValuationRing (U.presheaf.stalk η))
      (_ : IsLocalHom (algebraMap R (U.presheaf.stalk η))), IsIndexOneExtension R (U.presheaf.stalk η)) ∧
    (∃ (_ : IsDomain (Z.presheaf.stalk ζ)) (_ : IsDiscreteValuationRing (Z.presheaf.stalk ζ))
      (_ : IsLocalHom (algebraMap R (Z.presheaf.stalk ζ))), IsIndexOneExtension R (Z.presheaf.stalk ζ)) := by
  constructor
  · exact NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes u η hη hmaxU halgU
  · exact NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes z ζ hζ hmaxZ halgZ

private theorem uniformizer_arithmetic_facts
    (R S O : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [aRS : Algebra R S] [IsLocalHom (algebraMap R S)]
    [aRO : Algebra R O] [IsLocalHom (algebraMap R O)]
    [aSO : Algebra S O] [IsScalarTower R S O]
    (ϖ : R) (hϖirr : Irreducible ϖ)
    (hR : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    (hO : Ideal.map (algebraMap R O) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal O) :
    (IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) ∧
    (algebraMap R O ϖ ≠ 0) ∧ (algebraMap R S ϖ ≠ 0) ∧
    Function.Injective (algebraMap R O) ∧ Function.Injective (algebraMap R S) ∧
    Function.Injective (algebraMap S O) := by
  have hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr
  have hϖO : algebraMap R O ϖ ≠ 0 := C7Glue.map_uniformizer_ne_zero _ ϖ hϖ hO
  have hϖS : algebraMap R S ϖ ≠ 0 := C7Glue.map_uniformizer_ne_zero _ ϖ hϖ hR
  have hinjRO : Function.Injective (algebraMap R O) :=
    C7Glue.injective_of_map_irreducible_ne_zero _ ϖ hϖirr hϖO
  have hinjRS : Function.Injective (algebraMap R S) :=
    C7Glue.injective_of_map_irreducible_ne_zero _ ϖ hϖirr hϖS
  have hinjSO : Function.Injective (algebraMap S O) :=
    C7Glue.injective_of_map_irreducible_ne_zero _ (algebraMap R S ϖ)
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
        (C7Glue.maximalIdeal_eq_span_map _ ϖ hϖ hR))
      (by rw [← IsScalarTower.algebraMap_apply R S O]; exact hϖO)
  exact ⟨hϖ, hϖO, hϖS, hinjRO, hinjRS, hinjSO⟩

private theorem closed_stalk_uniformizer_injective
    {R : Type u} [rBase : CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f] (x : ↥X)
    (O : Type u) [CommRing O] [domO : IsDomain O]
    [aRX : Algebra R (X.presheaf.stalk x)] [aRO : Algebra R O]
    [aXO : Algebra (X.presheaf.stalk x) O] [tower : IsScalarTower R (X.presheaf.stalk x) O]
    (hx : f.base x = IsLocalRing.closedPoint R)
    (hmax : ∀ y : ↥X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x)
    (halg : X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk x))))
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (hϖO : algebraMap R O ϖ ≠ 0) :
    Function.Injective (algebraMap (X.presheaf.stalk x) O) := by
  obtain ⟨hdomX, hdvrX, hlocX, hidxX⟩ :=
    NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes f x hx hmax halg
  haveI := hdomX; haveI := hdvrX
  exact C7Glue.injective_of_map_irreducible_ne_zero _ (algebraMap R (X.presheaf.stalk x) ϖ)
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
      (C7Glue.maximalIdeal_eq_span_map _ ϖ hϖ hidxX.map_maximalIdeal))
    (by rw [← IsScalarTower.algebraMap_apply R (X.presheaf.stalk x) O]; exact hϖO)

private theorem generic_fibre_stalk_chart_point_fixed
    {R : Type u} [rBase : CommRing R] (K : Type u) [Field K] [Algebra R K]
    {X U XK : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (u : U ⟶ Spec (CommRingCat.of R))
    (q : U ⟶ X) (hq : q ≫ f = u) (ηU : ↥U)
    (gK : XK ⟶ Spec (CommRingCat.of K))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    [aRU : Algebra R (U.presheaf.stalk ηU)]
    (halgU : U.fromSpecStalk ηU ≫ u =
      Spec.map (CommRingCat.ofHom (algebraMap R (U.presheaf.stalk ηU))))
    [aRX : Algebra R (X.presheaf.stalk (q.base ηU))]
    (halgX : X.fromSpecStalk (q.base ηU) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk (q.base ηU)))))
    (F : Type u) [CommRing F]
    [Algebra (U.presheaf.stalk ηU) F] [aXF : Algebra (X.presheaf.stalk (q.base ηU)) F]
    [Algebra R F] [aKF : Algebra K F]
    [IsScalarTower R (U.presheaf.stalk ηU) F]
    [towerRXF : IsScalarTower R (X.presheaf.stalk (q.base ηU)) F] [IsScalarTower R K F]
    (hTower : letI : Algebra (X.presheaf.stalk (q.base ηU)) (U.presheaf.stalk ηU) :=
      (q.stalkMap ηU).hom.toAlgebra;
      IsScalarTower (X.presheaf.stalk (q.base ηU)) (U.presheaf.stalk ηU) F) :
    (NeronModelInfra.schemeHomOverComp
      (pointGenericFibre (K := K) (K' := F)
        (⟨U.fromSpecStalk ηU, halgU⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (U.presheaf.stalk ηU)))) u))
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f u ⟨q, hq⟩) e)).1 =
    (NeronModelInfra.schemeHomOverComp
      (pointGenericFibre (K := K) (K' := F)
        (⟨X.fromSpecStalk (q.base ηU), halgX⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk (q.base ηU))))) f))
      e).1 := by
  letI : Algebra (X.presheaf.stalk (q.base ηU)) (U.presheaf.stalk ηU) :=
    (q.stalkMap ηU).hom.toAlgebra
  haveI : IsScalarTower (X.presheaf.stalk (q.base ηU)) (U.presheaf.stalk ηU) F := hTower
  have hFpt : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (q.base ηU)) F)) ≫
      X.fromSpecStalk (q.base ηU) =
      Spec.map (CommRingCat.ofHom (algebraMap (U.presheaf.stalk ηU) F)) ≫
        U.fromSpecStalk ηU ≫ q := by
    rw [IsScalarTower.algebraMap_eq (X.presheaf.stalk (q.base ηU)) (U.presheaf.stalk ηU) F,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    erw [← Scheme.SpecMap_stalkMap_fromSpecStalk q (x := ηU)]
    rfl
  simp only [NeronModelInfra.schemeHomOverComp_coe]
  rw [← Category.assoc, G2Glue.pointGenericFibre_comp_genericFibreRestrict K f u q hq ηU
    (q.base ηU) halgU halgX F hFpt]

private theorem generic_fibre_translation_point_fixed
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

    [aRS : Algebra R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))))))
    [aRO : Algebra R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)]
    (halgO : (U₀ : Scheme.{u}).fromSpecStalk ⟨η, hηU⟩ ≫ (U₀.ι ≫ pullback.fst z f ≫ z) =
      Spec.map (CommRingCat.ofHom (algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))))
    [aR1 : Algebra R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))]
    (halg₁ : T.Y.fromSpecStalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)) ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))))))

    (K' F : Type u) [Field K'] [Algebra (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) K'] [IsFractionRing (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) K'] [Algebra R K'] [aKKprime : Algebra K K']
    [IsScalarTower R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) K'] [IsScalarTower R K K']
    [Field F] [Algebra ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F] [Algebra R F] [aKF : Algebra K F] [aKprimeF : Algebra K' F] [Algebra (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) F]
    [IsScalarTower R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F] [IsScalarTower R K F] [IsScalarTower K K' F] [IsScalarTower (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) K' F]
    (hBase : letI : Algebra (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) :=
      ((v.stalkMap ⟨η, hηU⟩).hom.comp ((pullback.fst z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom).toAlgebra;
      IsScalarTower (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F)
    [Algebra (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) F] [IsScalarTower R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) F]
    (hAux : letI : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := (v.stalkMap ⟨η, hηU⟩).hom.toAlgebra;
      letI : Algebra (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) := ((pullback.snd z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom.toAlgebra;
      letI : Algebra (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := ((algebraMap ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)).comp (algebraMap (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)))).toAlgebra;
      IsScalarTower (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F) :
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
        T.e).1 := by
  letI : Algebra (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := ((v.stalkMap ⟨η, hηU⟩).hom.comp ((pullback.fst z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom).toAlgebra
  haveI : IsScalarTower (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F := hBase
  letI : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := (v.stalkMap ⟨η, hηU⟩).hom.toAlgebra
  letI : Algebra (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) := ((pullback.snd z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom.toAlgebra
  letI : Algebra (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := ((algebraMap ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)).comp (algebraMap (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)))).toAlgebra
  haveI : IsScalarTower (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F := hAux
  have hRO : (algebraMap (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) F) =
    (algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F).comp ((v.stalkMap ⟨η, hηU⟩).hom.comp
      ((pullback.fst z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom) := by
    rw [IsScalarTower.algebraMap_eq (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F]; rfl
  have hτF : (algebraMap (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) F) =
    (algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F).comp ((v.stalkMap ⟨η, hηU⟩).hom.comp
      ((pullback.snd z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom) := by
    rw [IsScalarTower.algebraMap_eq (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F]; rfl
  exact NeronModelInfra.mul_pointGenericFibre_eq_pointGenericFibre_comp_chart_of_genericFibreRestrict_comp_eq_mul K LXK d ω X f e Z z uK η T U₀ hηU τ₀ hτ₀
    v hv₁ hv₂ halgZ halgO halg₁ K' F hRO hτF

private theorem component_reading_image_fixed
    {R K : Type u} [rBase : CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} {d : ℕ}
    {ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤)}
    (C : ComponentReading R K gK d ω) (K' F : Type u) [Field K'] [Field F]
    [aKKprime : Algebra K K'] [aKF : Algebra K F] [aKprimeF : Algebra K' F]
    [IsScalarTower K K' F]
    [aComponentF : Algebra (FractionRing (C.Y.presheaf.stalk C.y)) F]
    [aSectionF : Algebra Γ(XK, C.U) F]
    (hComponentF : letI : Algebra K (FractionRing (C.Y.presheaf.stalk C.y)) := C.algebraK;
      IsScalarTower K (FractionRing (C.Y.presheaf.stalk C.y)) F)
    (hSectionComponentF : letI : Algebra Γ(XK, C.U) (FractionRing (C.Y.presheaf.stalk C.y)) := C.algebraU;
      IsScalarTower Γ(XK, C.U) (FractionRing (C.Y.presheaf.stalk C.y)) F)
    (hSectionF : letI : Algebra K Γ(XK, C.U) :=
      (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) C.U;
      IsScalarTower K Γ(XK, C.U) F) :
    letI : Algebra R (C.Y.presheaf.stalk C.y) := C.algebra;
    letI : Algebra K (FractionRing (C.Y.presheaf.stalk C.y)) := C.algebraK;
    letI : Algebra Γ(XK, C.U) (FractionRing (C.Y.presheaf.stalk C.y)) := C.algebraU;
    letI : Algebra K Γ(XK, C.U) :=
      (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) C.U;
    letI : IsScalarTower R K (FractionRing (C.Y.presheaf.stalk C.y)) := C.isScalarTower;
    letI : IsScalarTower K Γ(XK, C.U) (FractionRing (C.Y.presheaf.stalk C.y)) := C.isScalarTowerU;
    letI : IsScalarTower K (FractionRing (C.Y.presheaf.stalk C.y)) F := hComponentF;
    letI : IsScalarTower Γ(XK, C.U) (FractionRing (C.Y.presheaf.stalk C.y)) F := hSectionComponentF;
    letI : IsScalarTower K Γ(XK, C.U) F := hSectionF;
    TopFormOrder.topFormMap K K' Γ(XK, C.U) F d C.ωU =
      TopFormOrder.topFormMap K K' (FractionRing (C.Y.presheaf.stalk C.y)) F d
        (C.a • TopFormOrder.topFormMap R K (C.Y.presheaf.stalk C.y)
          (FractionRing (C.Y.presheaf.stalk C.y)) d
            (exteriorPower.ιMulti (C.Y.presheaf.stalk C.y) d C.b)) := by
  letI : Algebra R (C.Y.presheaf.stalk C.y) := C.algebra
  letI : Algebra K (FractionRing (C.Y.presheaf.stalk C.y)) := C.algebraK
  letI : Algebra Γ(XK, C.U) (FractionRing (C.Y.presheaf.stalk C.y)) := C.algebraU
  letI : Algebra K Γ(XK, C.U) :=
    (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) C.U
  haveI : IsScalarTower R K (FractionRing (C.Y.presheaf.stalk C.y)) := C.isScalarTower
  haveI : IsScalarTower K Γ(XK, C.U) (FractionRing (C.Y.presheaf.stalk C.y)) := C.isScalarTowerU
  haveI : IsScalarTower K (FractionRing (C.Y.presheaf.stalk C.y)) F := hComponentF
  haveI : IsScalarTower Γ(XK, C.U) (FractionRing (C.Y.presheaf.stalk C.y)) F := hSectionComponentF
  haveI : IsScalarTower K Γ(XK, C.U) F := hSectionF
  have hread := component_stored_reading_fixed C
  exact (tfm_KE K K' Γ(XK, C.U) (FractionRing (C.Y.presheaf.stalk C.y)) F d C.ωU).symm.trans
    (congrArg (TopFormOrder.topFormMap K K' (FractionRing (C.Y.presheaf.stalk C.y)) F d) hread)

private theorem component_image_from_reading_data_fixed
    (K0 K1 B0 E0 F0 : Type u)
    [k0 : Field K0] [k1 : Field K1] [a01 : Algebra K0 K1]
    [rB : CommRing B0] [a0B : Algebra K0 B0] [e0 : Field E0] [f0 : Field F0]
    [aBE : Algebra B0 E0] [aEF : Algebra E0 F0] [aBF : Algebra B0 F0]
    [a0E : Algebra K0 E0] [a0F : Algebra K0 F0] [a1F : Algebra K1 F0]
    (hBEF : IsScalarTower B0 E0 F0) (h0BE : IsScalarTower K0 B0 E0)
    (h0EF : IsScalarTower K0 E0 F0) (h01F : IsScalarTower K0 K1 F0)
    (h0BF : IsScalarTower K0 B0 F0)
    (d : ℕ) (ω0 : ⋀[B0]^d (Ω[B0⁄K0])) (θ0 : ⋀[E0]^d (Ω[E0⁄K0]))
    (hread : letI : IsScalarTower K0 B0 E0 := h0BE;
      TopFormOrder.topFormMap K0 K0 B0 E0 d ω0 = θ0) :
    letI : IsScalarTower B0 E0 F0 := hBEF;
    letI : IsScalarTower K0 B0 E0 := h0BE;
    letI : IsScalarTower K0 E0 F0 := h0EF;
    letI : IsScalarTower K0 K1 F0 := h01F;
    letI : IsScalarTower K0 B0 F0 := h0BF;
    TopFormOrder.topFormMap K0 K1 B0 F0 d ω0 =
      TopFormOrder.topFormMap K0 K1 E0 F0 d θ0 := by
  letI : IsScalarTower B0 E0 F0 := hBEF
  letI : IsScalarTower K0 B0 E0 := h0BE
  letI : IsScalarTower K0 E0 F0 := h0EF
  letI : IsScalarTower K0 K1 F0 := h01F
  letI : IsScalarTower K0 B0 F0 := h0BF
  exact top_form_component_image_fixed K0 K1 B0 E0 F0 d ω0 θ0 hread

private theorem canonical_fraction_prefix_fixed
    (R K R' : Type u)
    [rBase : CommRing R] [domainR : IsDomain R] [dvrR : IsDiscreteValuationRing R] (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    [givenK : Field K] [aRK : Algebra R K] [fractionRK : IsFractionRing R K]
    [rPrimeBase : CommRing R'] [domainPrime : IsDomain R'] [dvrPrime : IsDiscreteValuationRing R'] [algBasePrime : Algebra R R'] [localBasePrime : IsLocalHom (algebraMap R R')]
       [aKKprime : Algebra K (FractionRing R')] 
    (towerRKKprime : IsScalarTower R K (FractionRing R')) 

    (O₀ : Type u)
    [rComponent : CommRing O₀] [domainComponent : IsDomain O₀] [dvrComponent : IsDiscreteValuationRing O₀] [aRComponent : Algebra R O₀] [localBaseComponent : IsLocalHom (algebraMap R O₀)]
    (hO₀ : Ideal.map (algebraMap R O₀) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal O₀)
       [aKComponent : Algebra K (FractionRing O₀)] 
     (towerRKComponent : IsScalarTower R K (FractionRing O₀))
    (d : ℕ) (b₀ : Module.Basis (Fin d) O₀ (Ω[O₀⁄R])) (a : (FractionRing O₀)) (ha : a ≠ 0)

    (O₁ O' : Type u)
    [rAux : CommRing O₁] [aRAux : Algebra R O₁]
    [rPullback : CommRing O'] [domainPullback : IsDomain O'] [aPrimePullback : Algebra R' O'] [aAuxPullback : Algebra O₁ O'] [aRPullback : Algebra R O']
    (towerRAuxPullback : IsScalarTower R O₁ O') (towerRPrimePullback : IsScalarTower R R' O')
    (b₁ : Module.Basis (Fin d) O₁ (Ω[O₁⁄R])) (w₁ : O₁ˣ) (m : ℤ)
    (hbc' : letI : IsScalarTower R O₁ O' := towerRAuxPullback;
      letI : IsScalarTower R R' O' := towerRPrimePullback;
      Function.Bijective
      ((KaehlerDifferential.map R R' O' O').restrictScalars O' ∘ₗ KaehlerDifferential.mapBaseChange R O₁ O'))

    (O : Type u)
    [rOpen : CommRing O] [domainOpen : IsDomain O] [dvrOpen : IsDiscreteValuationRing O] [aPrimeOpen : Algebra R' O] [localPrimeOpen : IsLocalHom (algebraMap R' O)]
    (hO : Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O)
    [aROpen : Algebra R O] (towerRPrimeOpen : IsScalarTower R R' O)
    [aComponentOpen : Algebra O₀ O] [localComponentOpen : IsLocalHom (algebraMap O₀ O)] (towerRComponentOpen : IsScalarTower R O₀ O)
    [aPullbackOpen : Algebra O' O] (towerPrimePullbackOpen : IsScalarTower R' O' O) [aAuxOpen : Algebra O₁ O] (towerAuxPullbackOpen : IsScalarTower O₁ O' O) (towerRAuxOpen : IsScalarTower R O₁ O)
    (hbc : letI : IsScalarTower R R' O := towerRPrimeOpen;
      letI : IsScalarTower R O₀ O := towerRComponentOpen;
      Function.Bijective
      ((KaehlerDifferential.map R R' O O).restrictScalars O ∘ₗ KaehlerDifferential.mapBaseChange R O₀ O))
         [fractionPullback : IsFractionRing O' (FractionRing O)]
    [aPrimeFieldOpen : Algebra (FractionRing R') (FractionRing O)]   (towerPrimePullbackField : IsScalarTower R' O' (FractionRing O)) (towerPrimeFractionField : IsScalarTower R' (FractionRing R') (FractionRing O))
    [aKOpen : Algebra K (FractionRing O)]   (towerRKOpen : IsScalarTower R K (FractionRing O)) (towerKKprimeOpen : IsScalarTower K (FractionRing R') (FractionRing O))
    [aComponentFieldOpen : Algebra (FractionRing O₀) (FractionRing O)]   (towerComponentFractionOpen : IsScalarTower O₀ (FractionRing O₀) (FractionRing O)) (towerKComponentOpen : IsScalarTower K (FractionRing O₀) (FractionRing O))
      (towerRAuxField : IsScalarTower R O₁ (FractionRing O))

 :
    letI : IsScalarTower R K (FractionRing R') := towerRKKprime;
    letI : IsScalarTower R K (FractionRing O₀) := towerRKComponent;
    letI : IsScalarTower R O₁ O' := towerRAuxPullback;
    letI : IsScalarTower R R' O' := towerRPrimePullback;
    letI : IsScalarTower R R' O := towerRPrimeOpen;
    letI : IsScalarTower R O₀ O := towerRComponentOpen;
    letI : IsScalarTower R' O' O := towerPrimePullbackOpen;
    letI : IsScalarTower O₁ O' O := towerAuxPullbackOpen;
    letI : IsScalarTower R O₁ O := towerRAuxOpen;
    letI : IsScalarTower R' O' (FractionRing O) := towerPrimePullbackField;
    letI : IsScalarTower R' (FractionRing R') (FractionRing O) := towerPrimeFractionField;
    letI : IsScalarTower R K (FractionRing O) := towerRKOpen;
    letI : IsScalarTower K (FractionRing R') (FractionRing O) := towerKKprimeOpen;
    letI : IsScalarTower O₀ (FractionRing O₀) (FractionRing O) := towerComponentFractionOpen;
    letI : IsScalarTower K (FractionRing O₀) (FractionRing O) := towerKComponentOpen;
    letI : IsScalarTower R O₁ (FractionRing O) := towerRAuxField;
    letI : IsScalarTower R R' (FractionRing R') := IsScalarTower.of_algebraMap_eq (fun _ => rfl);
    letI : IsScalarTower R O₀ (FractionRing O₀) := IsScalarTower.of_algebraMap_eq (fun _ => rfl);
    letI : IsScalarTower O' O (FractionRing O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl);
    letI : IsScalarTower R' O (FractionRing O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl);
    letI : IsScalarTower R O (FractionRing O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl);
    letI : IsScalarTower O₀ O (FractionRing O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl);
    letI : IsScalarTower O₁ O (FractionRing O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl);
    ∀ (σ : ⋀[(FractionRing O)]^d (Ω[(FractionRing O)⁄K]))
    (hT : σ = (algebraMap O₁ (FractionRing O) (w₁ : O₁) * algebraMap O₁ (FractionRing O) (algebraMap R O₁ ϖ) ^ m) •
        TopFormOrder.topFormMap R K O₁ (FractionRing O) d (exteriorPower.ιMulti O₁ d b₁))
    (hX : TopFormOrder.topFormMap K (FractionRing R') (FractionRing O) (FractionRing O) d σ =
        TopFormOrder.topFormMap K (FractionRing R') (FractionRing O₀) (FractionRing O) d (a • TopFormOrder.topFormMap R K O₀ (FractionRing O₀) d (exteriorPower.ιMulti O₀ d b₀)))
    (hmin : TopFormOrder.addOrd O₀ (FractionRing O₀) a ≤ m)
    (hRR' : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R'),
    m = TopFormOrder.addOrd O₀ (FractionRing O₀) a ∧ Function.Bijective (KaehlerDifferential.mapBaseChange R' O' O) := by
  letI : IsScalarTower R K (FractionRing R') := towerRKKprime
  letI : IsScalarTower R K (FractionRing O₀) := towerRKComponent
  letI : IsScalarTower R O₁ O' := towerRAuxPullback
  letI : IsScalarTower R R' O' := towerRPrimePullback
  letI : IsScalarTower R R' O := towerRPrimeOpen
  letI : IsScalarTower R O₀ O := towerRComponentOpen
  letI : IsScalarTower R' O' O := towerPrimePullbackOpen
  letI : IsScalarTower O₁ O' O := towerAuxPullbackOpen
  letI : IsScalarTower R O₁ O := towerRAuxOpen
  letI : IsScalarTower R' O' (FractionRing O) := towerPrimePullbackField
  letI : IsScalarTower R' (FractionRing R') (FractionRing O) := towerPrimeFractionField
  letI : IsScalarTower R K (FractionRing O) := towerRKOpen
  letI : IsScalarTower K (FractionRing R') (FractionRing O) := towerKKprimeOpen
  letI : IsScalarTower O₀ (FractionRing O₀) (FractionRing O) := towerComponentFractionOpen
  letI : IsScalarTower K (FractionRing O₀) (FractionRing O) := towerKComponentOpen
  letI : IsScalarTower R O₁ (FractionRing O) := towerRAuxField
  letI : IsScalarTower R R' (FractionRing R') := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower R O₀ (FractionRing O₀) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower O' O (FractionRing O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower R' O (FractionRing O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower R O (FractionRing O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower O₀ O (FractionRing O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower O₁ O (FractionRing O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  intro σ hT hX hmin hRR'
  exact atomic_map_evidence_last_fixed R K R' (FractionRing R') ϖ hϖ
    O₀ (FractionRing O₀) hO₀ d b₀ a ha O₁ O' b₁ w₁ m hbc'
    O (FractionRing O) hO hbc σ hT hX hmin hRR'

theorem ConstructionInterface.closed_fibre_point_facts
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} {d : ℕ}
    {ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤)}
    {X Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (z : Z ⟶ Spec (CommRingCat.of R))
    [Smooth f] [Smooth z] (T : ComponentReading R K gK d ω)
    (U₀ : (pullback z f).Opens) (η : ↥(pullback z f)) (hηU : η ∈ U₀)
    (hη : (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R)
    (hmax : ∀ y : ↥(pullback z f), y ⤳ η →
      (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η)
    (τ₀ : SchemeHomOver (U₀.ι ≫ pullback.fst z f ≫ z) T.f)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f)
    (hv₁ : v ≫ pullback.fst z T.f = U₀.ι ≫ pullback.fst z f)
    (hv₂ : v ≫ pullback.snd z T.f = τ₀.1)
    (hgen : T.y ⤳ τ₀.1.base ⟨η, hηU⟩) :
    let ηU : ↥U₀ := ⟨η, hηU⟩;
    let η' : ↥(pullback z T.f) := v.base ηU;
    let ζ₀ : ↥Z := (pullback.fst z T.f).base η';
    let y₁ : ↥T.Y := (pullback.snd z T.f).base η';
    (T.y ⤳ y₁) ∧
    (∀ y : ↥U₀, y ⤳ ηU → (U₀.ι ≫ pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = ηU) ∧
    (T.f.base y₁ = IsLocalRing.closedPoint R) ∧
    (f.base ((pullback.snd z f).base (U₀.ι.base ηU)) = IsLocalRing.closedPoint R) ∧
    (∀ y : ↥X, y ⤳ ((pullback.snd z f).base (U₀.ι.base ηU)) →
      f.base y = IsLocalRing.closedPoint R → y = ((pullback.snd z f).base (U₀.ι.base ηU))) ∧
    (z.base ζ₀ = IsLocalRing.closedPoint R) ∧
    (∀ y : ↥Z, y ⤳ ζ₀ → z.base y = IsLocalRing.closedPoint R → y = ζ₀) := by
  exact _root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.closed_fibre_point_facts f z T U₀ η hηU hη hmax τ₀ v hv₁ hv₂ hgen

theorem ConstructionInterface.paired_closed_stalk_index_facts
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Z U : Scheme.{u}}
    (z : Z ⟶ Spec (CommRingCat.of R)) (u : U ⟶ Spec (CommRingCat.of R))
    [Smooth z] [Smooth u]
    (ζ : ↥Z) (η : ↥U)
    (hζ : z.base ζ = IsLocalRing.closedPoint R)
    (hη : u.base η = IsLocalRing.closedPoint R)
    (hmaxZ : ∀ y : ↥Z, y ⤳ ζ → z.base y = IsLocalRing.closedPoint R → y = ζ)
    (hmaxU : ∀ y : ↥U, y ⤳ η → u.base y = IsLocalRing.closedPoint R → y = η)
    [aRZ : Algebra R (Z.presheaf.stalk ζ)] [aRU : Algebra R (U.presheaf.stalk η)]
    (halgZ : Z.fromSpecStalk ζ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ζ))))
    (halgU : U.fromSpecStalk η ≫ u = Spec.map (CommRingCat.ofHom (algebraMap R (U.presheaf.stalk η)))) :
    (∃ (_ : IsDomain (U.presheaf.stalk η)) (_ : IsDiscreteValuationRing (U.presheaf.stalk η))
      (_ : IsLocalHom (algebraMap R (U.presheaf.stalk η))), IsIndexOneExtension R (U.presheaf.stalk η)) ∧
    (∃ (_ : IsDomain (Z.presheaf.stalk ζ)) (_ : IsDiscreteValuationRing (Z.presheaf.stalk ζ))
      (_ : IsLocalHom (algebraMap R (Z.presheaf.stalk ζ))), IsIndexOneExtension R (Z.presheaf.stalk ζ)) := by
  exact _root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.paired_closed_stalk_index_facts z u ζ η hζ hη hmaxZ hmaxU
    (aRZ := aRZ) (aRU := aRU) halgZ halgU

theorem ConstructionInterface.index_one_map_maximalIdeal_fixed
    {R0 S0 : Type u} [CommRing R0] [IsLocalRing R0] [CommRing S0] [IsLocalRing S0]
    [Algebra R0 S0] [IsLocalHom (algebraMap R0 S0)] (hidx : IsIndexOneExtension R0 S0) :
    Ideal.map (algebraMap R0 S0) (IsLocalRing.maximalIdeal R0) = IsLocalRing.maximalIdeal S0 := by
  exact _root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.index_one_map_maximalIdeal_fixed hidx

theorem ConstructionInterface.uniformizer_arithmetic_facts
    (R S O : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [aRS : Algebra R S] [IsLocalHom (algebraMap R S)]
    [aRO : Algebra R O] [IsLocalHom (algebraMap R O)]
    [aSO : Algebra S O] [IsScalarTower R S O]
    (ϖ : R) (hϖirr : Irreducible ϖ)
    (hR : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    (hO : Ideal.map (algebraMap R O) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal O) :
    (IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) ∧
    (algebraMap R O ϖ ≠ 0) ∧ (algebraMap R S ϖ ≠ 0) ∧
    Function.Injective (algebraMap R O) ∧ Function.Injective (algebraMap R S) ∧
    Function.Injective (algebraMap S O) := by
  exact _root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.uniformizer_arithmetic_facts R S O
    (aRS := aRS) (aRO := aRO) (aSO := aSO) ϖ hϖirr hR hO

theorem ConstructionInterface.closed_stalk_uniformizer_injective
    {R : Type u} [rBase : CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f] (x : ↥X)
    (O : Type u) [CommRing O] [domO : IsDomain O]
    [aRX : Algebra R (X.presheaf.stalk x)] [aRO : Algebra R O]
    [aXO : Algebra (X.presheaf.stalk x) O] [tower : IsScalarTower R (X.presheaf.stalk x) O]
    (hx : f.base x = IsLocalRing.closedPoint R)
    (hmax : ∀ y : ↥X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x)
    (halg : X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk x))))
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (hϖO : algebraMap R O ϖ ≠ 0) :
    Function.Injective (algebraMap (X.presheaf.stalk x) O) := by
  exact _root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.closed_stalk_uniformizer_injective f x O
    (rBase := rBase) (domO := domO) (aRX := aRX) (aRO := aRO)
    (aXO := aXO) (tower := tower) hx hmax halg ϖ hϖ hϖO

theorem ConstructionInterface.pullback_stalk_delta_one_fixed
    {R : Type u} [CommRing R] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : Z ⟶ Spec (CommRingCat.of R))
    (p : ↥(pullback z f))
    [Algebra R (Z.presheaf.stalk ((pullback.fst z f).base p))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z f).base p) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z f).base p)))))
    [Algebra R (X.presheaf.stalk ((pullback.snd z f).base p))]
    (halgX : X.fromSpecStalk ((pullback.snd z f).base p) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base p)))))
    [Algebra R ((pullback z f).presheaf.stalk p)]
    (hZ : letI : Algebra (Z.presheaf.stalk ((pullback.fst z f).base p)) ((pullback z f).presheaf.stalk p) :=
      ((pullback.fst z f).stalkMap p).hom.toAlgebra;
      IsScalarTower R (Z.presheaf.stalk ((pullback.fst z f).base p)) ((pullback z f).presheaf.stalk p))
    (hX : letI : Algebra (X.presheaf.stalk ((pullback.snd z f).base p)) ((pullback z f).presheaf.stalk p) :=
      ((pullback.snd z f).stalkMap p).hom.toAlgebra;
      IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base p)) ((pullback z f).presheaf.stalk p)) :
    letI : Algebra (Z.presheaf.stalk ((pullback.fst z f).base p)) ((pullback z f).presheaf.stalk p) :=
      ((pullback.fst z f).stalkMap p).hom.toAlgebra
    letI : Algebra (X.presheaf.stalk ((pullback.snd z f).base p)) ((pullback z f).presheaf.stalk p) :=
      ((pullback.snd z f).stalkMap p).hom.toAlgebra
    Function.Bijective
      ((KaehlerDifferential.map R (Z.presheaf.stalk ((pullback.fst z f).base p))
        ((pullback z f).presheaf.stalk p) ((pullback z f).presheaf.stalk p)).restrictScalars
          ((pullback z f).presheaf.stalk p) ∘ₗ
        KaehlerDifferential.mapBaseChange R (X.presheaf.stalk ((pullback.snd z f).base p))
          ((pullback z f).presheaf.stalk p)) := by
  exact _root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.pullback_stalk_delta_one_fixed f z p halgZ halgX hZ hX

theorem ConstructionInterface.generic_fibre_translation_point_fixed
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

    [aRS : Algebra R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))))))
    [aRO : Algebra R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)]
    (halgO : (U₀ : Scheme.{u}).fromSpecStalk ⟨η, hηU⟩ ≫ (U₀.ι ≫ pullback.fst z f ≫ z) =
      Spec.map (CommRingCat.ofHom (algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))))
    [aR1 : Algebra R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))]
    (halg₁ : T.Y.fromSpecStalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)) ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))))))

    (K' F : Type u) [Field K'] [Algebra (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) K'] [IsFractionRing (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) K'] [Algebra R K'] [aKKprime : Algebra K K']
    [IsScalarTower R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) K'] [IsScalarTower R K K']
    [Field F] [Algebra ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F] [Algebra R F] [aKF : Algebra K F] [aKprimeF : Algebra K' F] [Algebra (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) F]
    [IsScalarTower R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F] [IsScalarTower R K F] [IsScalarTower K K' F] [IsScalarTower (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) K' F]
    (hBase : letI : Algebra (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) :=
      ((v.stalkMap ⟨η, hηU⟩).hom.comp ((pullback.fst z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom).toAlgebra;
      IsScalarTower (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F)
    [Algebra (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) F] [IsScalarTower R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) F]
    (hAux : letI : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := (v.stalkMap ⟨η, hηU⟩).hom.toAlgebra;
      letI : Algebra (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) := ((pullback.snd z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom.toAlgebra;
      letI : Algebra (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := ((algebraMap ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)).comp (algebraMap (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)))).toAlgebra;
      IsScalarTower (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F) :
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
        T.e).1 := by
  exact _root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.generic_fibre_translation_point_fixed K LXK d ω X f e Z z uK η T U₀ hηU τ₀ hτ₀
    v hv₁ hv₂ (rBase := rBase) (aRS := aRS) (aRO := aRO) (aR1 := aR1)
    (aKKprime := aKKprime) (aKF := aKF) (aKprimeF := aKprimeF)
    halgZ halgO halg₁ K' F hBase hAux

theorem ConstructionInterface.generic_fibre_stalk_chart_point_fixed
    {R : Type u} [rBase : CommRing R] (K : Type u) [Field K] [Algebra R K]
    {X U XK : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (u : U ⟶ Spec (CommRingCat.of R))
    (q : U ⟶ X) (hq : q ≫ f = u) (ηU : ↥U)
    (gK : XK ⟶ Spec (CommRingCat.of K))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    [aRU : Algebra R (U.presheaf.stalk ηU)]
    (halgU : U.fromSpecStalk ηU ≫ u =
      Spec.map (CommRingCat.ofHom (algebraMap R (U.presheaf.stalk ηU))))
    [aRX : Algebra R (X.presheaf.stalk (q.base ηU))]
    (halgX : X.fromSpecStalk (q.base ηU) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk (q.base ηU)))))
    (F : Type u) [CommRing F]
    [Algebra (U.presheaf.stalk ηU) F] [aXF : Algebra (X.presheaf.stalk (q.base ηU)) F]
    [Algebra R F] [aKF : Algebra K F]
    [IsScalarTower R (U.presheaf.stalk ηU) F]
    [towerRXF : IsScalarTower R (X.presheaf.stalk (q.base ηU)) F] [IsScalarTower R K F]
    (hTower : letI : Algebra (X.presheaf.stalk (q.base ηU)) (U.presheaf.stalk ηU) :=
      (q.stalkMap ηU).hom.toAlgebra;
      IsScalarTower (X.presheaf.stalk (q.base ηU)) (U.presheaf.stalk ηU) F) :
    (NeronModelInfra.schemeHomOverComp
      (pointGenericFibre (K := K) (K' := F)
        (⟨U.fromSpecStalk ηU, halgU⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (U.presheaf.stalk ηU)))) u))
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f u ⟨q, hq⟩) e)).1 =
    (NeronModelInfra.schemeHomOverComp
      (pointGenericFibre (K := K) (K' := F)
        (⟨X.fromSpecStalk (q.base ηU), halgX⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk (q.base ηU))))) f))
      e).1 := by
  exact _root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.generic_fibre_stalk_chart_point_fixed K f u q hq ηU gK e
    (rBase := rBase) (aRU := aRU) (aRX := aRX) (aKF := aKF)
    (aXF := aXF) (towerRXF := towerRXF) halgU halgX F hTower

theorem ConstructionInterface.section_kaehler_operator_fixed
    (K0 K1 F0 : Type u) [Field K0] [Field K1] [Field F0]
    [a01 : Algebra K0 K1] [a0F : Algebra K0 F0] [a1F : Algebra K1 F0]
    [IsScalarTower K0 K1 F0]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K0)) (U : XK.Opens) (d : ℕ)
    (aUF : Algebra Γ(XK, U) F0)
    (hKU : letI : Algebra K0 Γ(XK, U) :=
      (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U;
      letI : Algebra Γ(XK, U) F0 := aUF;
      IsScalarTower K0 Γ(XK, U) F0) :
    letI : Algebra K0 Γ(XK, U) :=
      (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U;
    letI : Algebra Γ(XK, U) F0 := aUF;
    letI : IsScalarTower K0 Γ(XK, U) F0 := hKU;
    (fun s : ⋀[Γ(XK, U)]^d
      ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U)) =>
      TopFormOrder.topFormMap K0 K1 F0 F0 d (TopFormOrder.topFormMap K0 K0 Γ(XK, U) F0 d s)) =
    (fun s : ⋀[Γ(XK, U)]^d
      ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U)) =>
      TopFormOrder.topFormMap K0 K1 Γ(XK, U) F0 d s) := by
  exact _root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.section_kaehler_operator_fixed K0 K1 F0
    (a01 := a01) (a0F := a0F) (a1F := a1F) gK U d aUF hKU

theorem ConstructionInterface.fixed_function_evaluation
    (V W : Type u) (f g : V → W) (h : f = g) (v : V) : f v = g v := by
  exact _root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.fixed_function_evaluation V W f g h v

theorem ConstructionInterface.component_image_from_reading_data_fixed
    (K0 K1 B0 E0 F0 : Type u)
    [k0 : Field K0] [k1 : Field K1] [a01 : Algebra K0 K1]
    [rB : CommRing B0] [a0B : Algebra K0 B0] [e0 : Field E0] [f0 : Field F0]
    [aBE : Algebra B0 E0] [aEF : Algebra E0 F0] [aBF : Algebra B0 F0]
    [a0E : Algebra K0 E0] [a0F : Algebra K0 F0] [a1F : Algebra K1 F0]
    (hBEF : IsScalarTower B0 E0 F0) (h0BE : IsScalarTower K0 B0 E0)
    (h0EF : IsScalarTower K0 E0 F0) (h01F : IsScalarTower K0 K1 F0)
    (h0BF : IsScalarTower K0 B0 F0)
    (d : ℕ) (ω0 : ⋀[B0]^d (Ω[B0⁄K0])) (θ0 : ⋀[E0]^d (Ω[E0⁄K0]))
    (hread : letI : IsScalarTower K0 B0 E0 := h0BE;
      TopFormOrder.topFormMap K0 K0 B0 E0 d ω0 = θ0) :
    letI : IsScalarTower B0 E0 F0 := hBEF;
    letI : IsScalarTower K0 B0 E0 := h0BE;
    letI : IsScalarTower K0 E0 F0 := h0EF;
    letI : IsScalarTower K0 K1 F0 := h01F;
    letI : IsScalarTower K0 B0 F0 := h0BF;
    TopFormOrder.topFormMap K0 K1 B0 F0 d ω0 =
      TopFormOrder.topFormMap K0 K1 E0 F0 d θ0 := by
  exact _root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.component_image_from_reading_data_fixed K0 K1 B0 E0 F0
    (k0 := k0) (k1 := k1) (rB := rB) (e0 := e0) (f0 := f0)
    (a01 := a01) (a0B := a0B) (aBE := aBE) (aEF := aEF) (aBF := aBF)
    (a0E := a0E) (a0F := a0F) (a1F := a1F)
    hBEF h0BE h0EF h01F h0BF d ω0 θ0 hread

theorem ConstructionInterface.four_endpoint_equality_fixed
    (W : Type u) (x0 x1 x2 x3 : W)
    (h01 : x0 = x1) (h12 : x1 = x2) (h23 : x2 = x3) :
    x0 = x3 := by
  exact _root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.four_endpoint_equality_fixed W x0 x1 x2 x3 h01 h12 h23

theorem ConstructionInterface.minimality_order_bound_fixed
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} {d : ℕ}
    {ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤)}
    (D : MinimalComponentData R K gK d ω) (hD : D.IsOmegaMinimal) (c : D.ι)
    (T : ComponentReading R K gK d ω) :
    TopFormOrder.addOrd ((D.C c).Y.presheaf.stalk (D.C c).y)
      (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (D.C c).a ≤ T.n := by
  exact _root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.minimality_order_bound_fixed D hD c T

theorem ConstructionInterface.canonical_fraction_prefix_fixed
    (R K R' : Type u)
    [rBase : CommRing R] [domainR : IsDomain R] [dvrR : IsDiscreteValuationRing R] (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    [givenK : Field K] [aRK : Algebra R K] [fractionRK : IsFractionRing R K]
    [rPrimeBase : CommRing R'] [domainPrime : IsDomain R'] [dvrPrime : IsDiscreteValuationRing R'] [algBasePrime : Algebra R R'] [localBasePrime : IsLocalHom (algebraMap R R')]
       [aKKprime : Algebra K (FractionRing R')] 
    (towerRKKprime : IsScalarTower R K (FractionRing R')) 

    (O₀ : Type u)
    [rComponent : CommRing O₀] [domainComponent : IsDomain O₀] [dvrComponent : IsDiscreteValuationRing O₀] [aRComponent : Algebra R O₀] [localBaseComponent : IsLocalHom (algebraMap R O₀)]
    (hO₀ : Ideal.map (algebraMap R O₀) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal O₀)
       [aKComponent : Algebra K (FractionRing O₀)] 
     (towerRKComponent : IsScalarTower R K (FractionRing O₀))
    (d : ℕ) (b₀ : Module.Basis (Fin d) O₀ (Ω[O₀⁄R])) (a : (FractionRing O₀)) (ha : a ≠ 0)

    (O₁ O' : Type u)
    [rAux : CommRing O₁] [aRAux : Algebra R O₁]
    [rPullback : CommRing O'] [domainPullback : IsDomain O'] [aPrimePullback : Algebra R' O'] [aAuxPullback : Algebra O₁ O'] [aRPullback : Algebra R O']
    (towerRAuxPullback : IsScalarTower R O₁ O') (towerRPrimePullback : IsScalarTower R R' O')
    (b₁ : Module.Basis (Fin d) O₁ (Ω[O₁⁄R])) (w₁ : O₁ˣ) (m : ℤ)
    (hbc' : letI : IsScalarTower R O₁ O' := towerRAuxPullback;
      letI : IsScalarTower R R' O' := towerRPrimePullback;
      Function.Bijective
      ((KaehlerDifferential.map R R' O' O').restrictScalars O' ∘ₗ KaehlerDifferential.mapBaseChange R O₁ O'))

    (O : Type u)
    [rOpen : CommRing O] [domainOpen : IsDomain O] [dvrOpen : IsDiscreteValuationRing O] [aPrimeOpen : Algebra R' O] [localPrimeOpen : IsLocalHom (algebraMap R' O)]
    (hO : Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O)
    [aROpen : Algebra R O] (towerRPrimeOpen : IsScalarTower R R' O)
    [aComponentOpen : Algebra O₀ O] [localComponentOpen : IsLocalHom (algebraMap O₀ O)] (towerRComponentOpen : IsScalarTower R O₀ O)
    [aPullbackOpen : Algebra O' O] (towerPrimePullbackOpen : IsScalarTower R' O' O) [aAuxOpen : Algebra O₁ O] (towerAuxPullbackOpen : IsScalarTower O₁ O' O) (towerRAuxOpen : IsScalarTower R O₁ O)
    (hbc : letI : IsScalarTower R R' O := towerRPrimeOpen;
      letI : IsScalarTower R O₀ O := towerRComponentOpen;
      Function.Bijective
      ((KaehlerDifferential.map R R' O O).restrictScalars O ∘ₗ KaehlerDifferential.mapBaseChange R O₀ O))
         [fractionPullback : IsFractionRing O' (FractionRing O)]
    [aPrimeFieldOpen : Algebra (FractionRing R') (FractionRing O)]   (towerPrimePullbackField : IsScalarTower R' O' (FractionRing O)) (towerPrimeFractionField : IsScalarTower R' (FractionRing R') (FractionRing O))
    [aKOpen : Algebra K (FractionRing O)]   (towerRKOpen : IsScalarTower R K (FractionRing O)) (towerKKprimeOpen : IsScalarTower K (FractionRing R') (FractionRing O))
    [aComponentFieldOpen : Algebra (FractionRing O₀) (FractionRing O)]   (towerComponentFractionOpen : IsScalarTower O₀ (FractionRing O₀) (FractionRing O)) (towerKComponentOpen : IsScalarTower K (FractionRing O₀) (FractionRing O))
      (towerRAuxField : IsScalarTower R O₁ (FractionRing O))

 :
    letI : IsScalarTower R K (FractionRing R') := towerRKKprime;
    letI : IsScalarTower R K (FractionRing O₀) := towerRKComponent;
    letI : IsScalarTower R O₁ O' := towerRAuxPullback;
    letI : IsScalarTower R R' O' := towerRPrimePullback;
    letI : IsScalarTower R R' O := towerRPrimeOpen;
    letI : IsScalarTower R O₀ O := towerRComponentOpen;
    letI : IsScalarTower R' O' O := towerPrimePullbackOpen;
    letI : IsScalarTower O₁ O' O := towerAuxPullbackOpen;
    letI : IsScalarTower R O₁ O := towerRAuxOpen;
    letI : IsScalarTower R' O' (FractionRing O) := towerPrimePullbackField;
    letI : IsScalarTower R' (FractionRing R') (FractionRing O) := towerPrimeFractionField;
    letI : IsScalarTower R K (FractionRing O) := towerRKOpen;
    letI : IsScalarTower K (FractionRing R') (FractionRing O) := towerKKprimeOpen;
    letI : IsScalarTower O₀ (FractionRing O₀) (FractionRing O) := towerComponentFractionOpen;
    letI : IsScalarTower K (FractionRing O₀) (FractionRing O) := towerKComponentOpen;
    letI : IsScalarTower R O₁ (FractionRing O) := towerRAuxField;
    letI : IsScalarTower R R' (FractionRing R') := IsScalarTower.of_algebraMap_eq (fun _ => rfl);
    letI : IsScalarTower R O₀ (FractionRing O₀) := IsScalarTower.of_algebraMap_eq (fun _ => rfl);
    letI : IsScalarTower O' O (FractionRing O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl);
    letI : IsScalarTower R' O (FractionRing O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl);
    letI : IsScalarTower R O (FractionRing O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl);
    letI : IsScalarTower O₀ O (FractionRing O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl);
    letI : IsScalarTower O₁ O (FractionRing O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl);
    ∀ (σ : ⋀[(FractionRing O)]^d (Ω[(FractionRing O)⁄K]))
    (hT : σ = (algebraMap O₁ (FractionRing O) (w₁ : O₁) * algebraMap O₁ (FractionRing O) (algebraMap R O₁ ϖ) ^ m) •
        TopFormOrder.topFormMap R K O₁ (FractionRing O) d (exteriorPower.ιMulti O₁ d b₁))
    (hX : TopFormOrder.topFormMap K (FractionRing R') (FractionRing O) (FractionRing O) d σ =
        TopFormOrder.topFormMap K (FractionRing R') (FractionRing O₀) (FractionRing O) d (a • TopFormOrder.topFormMap R K O₀ (FractionRing O₀) d (exteriorPower.ιMulti O₀ d b₀)))
    (hmin : TopFormOrder.addOrd O₀ (FractionRing O₀) a ≤ m)
    (hRR' : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R'),
    m = TopFormOrder.addOrd O₀ (FractionRing O₀) a ∧ Function.Bijective (KaehlerDifferential.mapBaseChange R' O' O) := by
  exact _root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.canonical_fraction_prefix_fixed R K R'
    (rBase := rBase) (givenK := givenK) (aRK := aRK) (fractionRK := fractionRK)
    (rPrimeBase := rPrimeBase) (algBasePrime := algBasePrime)
    (aKKprime := aKKprime) (rComponent := rComponent)
    (aRComponent := aRComponent) (aKComponent := aKComponent)
    (rAux := rAux) (aRAux := aRAux) (rPullback := rPullback)
    (aPrimePullback := aPrimePullback) (aAuxPullback := aAuxPullback)
    (aRPullback := aRPullback) (rOpen := rOpen) (aPrimeOpen := aPrimeOpen)
    (aROpen := aROpen) (aComponentOpen := aComponentOpen)
    (aPullbackOpen := aPullbackOpen) (aAuxOpen := aAuxOpen)
    (fractionPullback := fractionPullback) (aPrimeFieldOpen := aPrimeFieldOpen)
    (aKOpen := aKOpen) (aComponentFieldOpen := aComponentFieldOpen)
    ϖ hϖ towerRKKprime O₀ hO₀ towerRKComponent d b₀ a ha
    O₁ O' towerRAuxPullback towerRPrimePullback b₁ w₁ m hbc'
    O hO towerRPrimeOpen towerRComponentOpen towerPrimePullbackOpen
    towerAuxPullbackOpen towerRAuxOpen hbc towerPrimePullbackField
    towerPrimeFractionField towerRKOpen towerKKprimeOpen
    towerComponentFractionOpen towerKComponentOpen towerRAuxField

end P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
end ZInQ.Contrib.CloudR2NeronExistence.Henselian

/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NeronModelInfra_ComponentReading_exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_OmegaMinimalComponentData
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_NeronModelInfra_ComponentReading_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_specializes
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_NeronModelInfra_ComponentReading_eq_n_of_forall_topFormMap_eq_mul_zpow_smul
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NeronModelInfra_ComponentReading_exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes
attribute [-instance] NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    {d : ℕ} [SmoothOfRelativeDimension d gK]
    {ω : Γ(gK.topDifferentials d, ⊤)} (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (T : ComponentReading R K gK d ω)
    (y₁ : ↥T.Y) (hy₁ : T.f.base y₁ = IsLocalRing.closedPoint R) (hgen : T.y ⤳ y₁)
    [Algebra R (T.Y.presheaf.stalk y₁)]
    (halg₁ : T.Y.fromSpecStalk y₁ ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁))))
    (F : Type u) [Field F] [Algebra (T.Y.presheaf.stalk y₁) F] [Algebra R F] [Algebra K F]
    [IsScalarTower R (T.Y.presheaf.stalk y₁) F] [IsScalarTower R K F]
    (U : XK.Opens) (hU : IsAffineOpen U) [Algebra Γ(XK, U) F]
    (hKU : letI := gK.sectionsAlgebra U; IsScalarTower K Γ(XK, U) F)
    (hx : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) F)) ≫ hU.fromSpec =
      (schemeHomOverComp
        (pointGenericFibre (K := K) (K' := F)
          (⟨T.Y.fromSpecStalk y₁, halg₁⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁)))) T.f))
        T.e).1)
    (ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U)))
    (hωU : gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω) :
    ∃ (b' : Module.Basis (Fin d) (T.Y.presheaf.stalk y₁) (Ω[(T.Y.presheaf.stalk y₁)⁄R]))
      (w : (T.Y.presheaf.stalk y₁)ˣ),
      letI := gK.sectionsAlgebra U
      TopFormOrder.topFormMap K K Γ(XK, U) F d ωU =
        (algebraMap (T.Y.presheaf.stalk y₁) F (w : (T.Y.presheaf.stalk y₁)) *
            algebraMap (T.Y.presheaf.stalk y₁) F (algebraMap R (T.Y.presheaf.stalk y₁) ϖ) ^ T.n) •
          TopFormOrder.topFormMap R K (T.Y.presheaf.stalk y₁) F d
            (exteriorPower.ιMulti (T.Y.presheaf.stalk y₁) d b') := by
  obtain ⟨b', w, m, h⟩ :=
    NeronModelInfra.ComponentReading.exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_specializes
      ϖ hϖ K hω T y₁ hy₁ hgen halg₁
  have hm : m = T.n :=
    NeronModelInfra.ComponentReading.eq_n_of_forall_topFormMap_eq_mul_zpow_smul ϖ hϖ K hω T y₁ hy₁ hgen halg₁ b' w m h
  exact ⟨b', w, hm ▸ h F U hU hKU hx ωU hωU⟩

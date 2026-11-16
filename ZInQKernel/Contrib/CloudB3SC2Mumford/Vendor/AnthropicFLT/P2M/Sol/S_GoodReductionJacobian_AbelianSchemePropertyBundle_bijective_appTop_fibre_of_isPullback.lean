/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_appTop_fibre_of_isPullback
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`; 1 `#print axioms` audit command(s) (with their `#guard_msgs` expectations) are removed (diagnostics only, no declaration).
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_algebraMap_appTop_of_isProper_of_isIntegral
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_appTop_fibre_of_isPullback
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd
attribute [-simp] AlgebraicGeometry.schemeFibreEndo_fst

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {T : Type u} [CommRing T] {A₀ : Scheme.{u}} {f₀ : A₀ ⟶ Spec (CommRingCat.of T)}
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {k : Type u} [Field k] (ρ : T →+* k)
    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of k)) (i₀ : Ak ⟶ A₀)
    (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ))) :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fk.appTop).hom := by
  have hk : AbelianSchemePropertyBundle k fk := h₀.of_isPullback hi₀
  haveI : IsProper fk := hk.proper
  haveI : GeometricallyIntegral fk := hk.geometricallyIntegral
  haveI : CompactSpace ↥Ak := QuasiCompact.compactSpace_of_compactSpace fk
  haveI : QuasiSeparatedSpace ↥Ak := (quasiSeparated_iff_quasiSeparatedSpace fk).mp inferInstance
  apply AlgebraicGeometry.bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat fk (AlgebraicClosure k)
  haveI : IsIntegral (pullback fk (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (pullback.snd fk _)
  exact AlgebraicGeometry.bijective_algebraMap_appTop_of_isProper_of_isIntegral (AlgebraicClosure k) (pullback.snd fk _)

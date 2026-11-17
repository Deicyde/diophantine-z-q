/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NeronModelInfra_exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_NeronModelInfra_exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-instance] NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (q : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion q.1] :
    ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ Spec (CommRingCat.of R)) (j : Y ⟶ Y') (hj : j ≫ f' = f)
      (e : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K)) gK),
      IsOpenImmersion j ∧ IsSeparated f' ∧ LocallyOfFiniteType f' ∧ QuasiCompact f' ∧ IsIso e.1 ∧
      (∀ y' : Y', f'.base y' = IsLocalRing.closedPoint R → y' ∈ Set.range j.base) ∧
      schemeHomOverComp (genericFibreRestrict R K f' f ⟨j, hj⟩) e = q ∧
      (Smooth gK → Smooth f → Smooth f') := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart.solution

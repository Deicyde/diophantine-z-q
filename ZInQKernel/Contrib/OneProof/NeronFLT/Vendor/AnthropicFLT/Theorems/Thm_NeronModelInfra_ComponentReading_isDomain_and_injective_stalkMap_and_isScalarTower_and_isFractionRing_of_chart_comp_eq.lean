/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NeronModelInfra_ComponentReading_isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_OmegaMinimalComponentData
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_NeronModelInfra_ComponentReading_isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite open AlgebraicGeometry hiding isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict open NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.ComponentReading.isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    {d : ℕ} [SmoothOfRelativeDimension d gK]
    {ω : Γ(gK.topDifferentials d, ⊤)}
    (T T' : ComponentReading R K gK d ω)
    (W : T.Y.Opens) (hyW : T.y ∈ W) (u : SchemeHomOver (W.ι ≫ T.f) T'.f)
    (hu : (genericFibreRestrict R K T'.f (W.ι ≫ T.f) u).1 ≫ T'.e.1 =
      (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1) :
    letI := T.algebra
    letI φ : T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩) ⟶ T.Y.presheaf.stalk T.y :=
      u.1.stalkMap ⟨T.y, hyW⟩ ≫ (W.stalkIso ⟨T.y, hyW⟩).hom
    letI : Algebra (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (T.Y.presheaf.stalk T.y) := φ.hom.toAlgebra
    letI : Algebra (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (FractionRing (T.Y.presheaf.stalk T.y)) :=
      ((algebraMap (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y))).comp φ.hom).toAlgebra
    letI : Algebra R (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) := stalkAlgebra T'.f (u.1.base ⟨T.y, hyW⟩)
    IsDomain (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) ∧
      Function.Injective φ.hom ∧
      IsScalarTower R (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (T.Y.presheaf.stalk T.y) ∧
      IsFractionRing (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (FractionRing (T.Y.presheaf.stalk T.y)) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_ComponentReading_isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq.solution

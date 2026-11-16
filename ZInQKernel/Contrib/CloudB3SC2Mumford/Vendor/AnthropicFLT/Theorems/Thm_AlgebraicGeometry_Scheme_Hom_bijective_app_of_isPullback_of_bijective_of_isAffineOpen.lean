/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_Hom_bijective_app_of_isPullback_of_bijective_of_isAffineOpen
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_bijective_app_of_isPullback_of_bijective_of_isAffineOpen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.bijective_app_of_isPullback_of_bijective_of_isAffineOpen
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fY] [IsSeparated fY]
    (hY : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fY.appTop).hom)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Bijective (p₁.app U).hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_bijective_app_of_isPullback_of_bijective_of_isAffineOpen.solution

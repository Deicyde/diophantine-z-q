/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : IsPullback φ gX gY (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (U : Y.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (φ ⁻¹ᵁ U) ∧
      letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra (φ ⁻¹ᵁ U)
      letI : Algebra Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := (φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom.toAlgebra
      ∀ [Algebra A Γ(X, φ ⁻¹ᵁ U)] [IsScalarTower A B Γ(X, φ ⁻¹ᵁ U)]
        [IsScalarTower A Γ(Y, U) Γ(X, φ ⁻¹ᵁ U)],
        Algebra.IsPushout A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback.solution

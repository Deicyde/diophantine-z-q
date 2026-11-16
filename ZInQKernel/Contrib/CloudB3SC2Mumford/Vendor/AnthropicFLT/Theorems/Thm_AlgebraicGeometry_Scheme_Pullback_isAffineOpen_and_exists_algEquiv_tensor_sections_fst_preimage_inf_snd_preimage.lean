/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem AlgebraicGeometry.Scheme.Pullback.isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R))
    (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst f g ≫ f)
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) ∧
    ∃ e : Γ(X, U) ⊗[R] Γ(Y, V) ≃ₐ[R]
        Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V),
      ∀ (a : Γ(X, U)) (b : Γ(Y, V)), e (a ⊗ₜ[R] b) =
        (pullback.fst f g).appLE U (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) inf_le_left a *
          (pullback.snd f g).appLE V (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) inf_le_right b := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage.solution

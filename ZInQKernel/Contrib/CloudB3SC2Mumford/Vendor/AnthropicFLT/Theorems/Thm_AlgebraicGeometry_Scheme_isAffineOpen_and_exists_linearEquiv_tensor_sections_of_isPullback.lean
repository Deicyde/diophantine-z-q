/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback
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
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem AlgebraicGeometry.Scheme.isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback
    {R : Type u} [CommRing R] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of R)) (fY : Y ⟶ Spec (CommRingCat.of R))
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom fX U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom fY V
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (p₁ ≫ fX) (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V)
    IsAffineOpen (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) ∧
    ∃ Φ : Γ(X, U) ⊗[R] Γ(Y, V) ≃ₗ[R] Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V),
      ∀ (a : Γ(X, U)) (b : Γ(Y, V)), Φ (a ⊗ₜ[R] b) =
        (p₁.appLE U (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) inf_le_left).hom a *
          (p₂.appLE V (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) inf_le_right).hom b := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback.solution

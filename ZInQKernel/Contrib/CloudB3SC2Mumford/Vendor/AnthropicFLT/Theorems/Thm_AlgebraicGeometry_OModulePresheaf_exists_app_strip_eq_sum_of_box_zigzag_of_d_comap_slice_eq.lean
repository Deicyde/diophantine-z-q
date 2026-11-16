/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq
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
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    (x₀ : Spec (CommRingCat.of k) ⟶ X)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y)
    (iY : Y ⟶ P) [IsClosedImmersion iY] (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒲 : P.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (hcY : ∃ b : (OModulePresheaf.unit fY).cochain (𝒲.comap iY) 0,
      (OModulePresheaf.unit fY).d (𝒲.comap iY) 0 b = fun s =>
        (Y.presheaf.map (homOfLE (𝒲.comap_inter_le iY s)).op).hom ((iY.app (𝒲.inter s)).hom (c s)))
    (U : X.Opens) (hU₀ : x₀ ⁻¹ᵁ U = ⊤)
    (γ : ∀ (σ : (𝒲.comap iY).Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ))
    (e : ∀ σ : (𝒲.comap iY).Idx 1, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ))
    (hV : ∀ (σ : (𝒲.comap iY).Idx 0) (t : 𝒲.Idx (0 + 1)),
      (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ ≤ 𝒲.inter t)).op).hom (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ)
              (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))).op).hom (γ σ (𝒲.face t j)))
    (hH : ∀ (σ : (𝒲.comap iY).Idx (0 + 1)) (t : 𝒲.Idx 0),
      (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ)).op).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone ((𝒲.comap iY).inter_le_inter_face σ j)))).op).hom (γ ((𝒲.comap iY).face σ j) t)) :
    ∃ g : ∀ i : (𝒲.comap iY).Idx 0, Γ(Y, iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter i)),
      ∀ σ : (𝒲.comap iY).Idx (0 + 1), (iY.app (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ)).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (Y.presheaf.map (homOfLE ((TopologicalSpace.Opens.map iY.base).monotone (inf_le_inf_left (p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone ((𝒲.comap iY).inter_le_inter_face σ j))))).op).hom (g ((𝒲.comap iY).face σ j)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq.solution

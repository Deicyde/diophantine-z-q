/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.OModulePresheaf.IsQuasicoherent.exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom
    {A : Type u} [CommRing A]
    {P V' : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) (p : V' ⟶ P)
    (G : OModulePresheaf q) (hq : G.IsQuasicoherent) :
    ∃ (G' : OModulePresheaf (p ≫ q))
      (η : ∀ (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → (G.obj U.1 →ₗ[A] G'.obj V.1)),
      G'.IsQuasicoherent ∧ (G.IsCoherent → G'.IsCoherent) ∧

      (∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (a : Γ(P, U.1)) (x : G.obj U.1),
        η U V h (a • x) = (p.appLE U.1 V.1 h).hom a • η U V h x) ∧

      (∀ (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
        (hV : V₁.1 ≤ V₂.1) (x : G.obj U.1), G'.res hV (η U V₂ h₂ x) = η U V₁ h₁ x) ∧

      (∀ (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
        (hU : U₁.1 ≤ U₂.1) (x : G.obj U₂.1), η U₂ V h₂ x = η U₁ V h₁ (G.res hU x)) ∧

      (∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1),
        letI := (p.appLE U.1 V.1 h).hom.toAlgebra
        ∃ β : Γ(V', V.1) ⊗[Γ(P, U.1)] G.obj U.1 ≃ₗ[Γ(V', V.1)] G'.obj V.1,
          ∀ x : G.obj U.1, β (1 ⊗ₜ x) = η U V h x) ∧

      (∀ (W : P.affineOpens) (W' : V'.affineOpens) (hW : W'.1 = p ⁻¹ᵁ W.1),
        IsIso (p ∣_ W.1) → Function.Bijective (η W W' hW.le)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.solution

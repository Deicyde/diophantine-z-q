/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct
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
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct
    {A : Type u} [CommRing A]
    {P V' : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) (p : V' ⟶ P)
    (G₁ G₂ : OModulePresheaf q) (hq₁ : G₁.IsQuasicoherent) (hq₂ : G₂.IsQuasicoherent)
    (G'₁ : OModulePresheaf (p ≫ q)) (hq'₁ : G'₁.IsQuasicoherent)
    (η₁ : ∀ (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → (G₁.obj U.1 →ₗ[A] G'₁.obj V.1))
    (hη₁s : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (a : Γ(P, U.1)) (x : G₁.obj U.1),
      η₁ U V h (a • x) = (p.appLE U.1 V.1 h).hom a • η₁ U V h x)
    (hη₁V : ∀ (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
      (hV : V₁.1 ≤ V₂.1) (x : G₁.obj U.1), G'₁.res hV (η₁ U V₂ h₂ x) = η₁ U V₁ h₁ x)
    (hη₁U : ∀ (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
      (hU : U₁.1 ≤ U₂.1) (x : G₁.obj U₂.1), η₁ U₂ V h₂ x = η₁ U₁ V h₁ (G₁.res hU x))
    (hβ₁ : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1),
      letI := (p.appLE U.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U.1)] G₁.obj U.1 ≃ₗ[Γ(V', V.1)] G'₁.obj V.1,
        ∀ x : G₁.obj U.1, β (1 ⊗ₜ x) = η₁ U V h x)
    (G'₂ : OModulePresheaf (p ≫ q)) (hq'₂ : G'₂.IsQuasicoherent)
    (η₂ : ∀ (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → (G₂.obj U.1 →ₗ[A] G'₂.obj V.1))
    (hη₂s : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (a : Γ(P, U.1)) (x : G₂.obj U.1),
      η₂ U V h (a • x) = (p.appLE U.1 V.1 h).hom a • η₂ U V h x)
    (hη₂V : ∀ (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
      (hV : V₁.1 ≤ V₂.1) (x : G₂.obj U.1), G'₂.res hV (η₂ U V₂ h₂ x) = η₂ U V₁ h₁ x)
    (hη₂U : ∀ (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
      (hU : U₁.1 ≤ U₂.1) (x : G₂.obj U₂.1), η₂ U₂ V h₂ x = η₂ U₁ V h₁ (G₂.res hU x))
    (hβ₂ : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1),
      letI := (p.appLE U.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U.1)] G₂.obj U.1 ≃ₗ[Γ(V', V.1)] G'₂.obj V.1,
        ∀ x : G₂.obj U.1, β (1 ⊗ₜ x) = η₂ U V h x)
    (ψ : OModulePresheaf.AffHom G₁ G₂) :
    ∃ ψ' : OModulePresheaf.AffHom G'₁ G'₂,
      (∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (x : G₁.obj U.1),
        ψ'.app V (η₁ U V h x) = η₂ U V h (ψ.app U x)) ∧
      ((∀ U : P.affineOpens, Function.Surjective (ψ.app U)) →
        ∀ V : V'.affineOpens, Function.Surjective (ψ'.app V)) ∧
      (∀ J : Ideal A, (∀ U : P.affineOpens, Function.Surjective (ψ.app U)) →
        (∀ U : P.affineOpens, LinearMap.ker (ψ.app U) = J • (⊤ : Submodule A (G₁.obj U.1))) →
        ∀ V : V'.affineOpens, LinearMap.ker (ψ'.app V) = J • (⊤ : Submodule A (G'₁.obj V.1))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.solution

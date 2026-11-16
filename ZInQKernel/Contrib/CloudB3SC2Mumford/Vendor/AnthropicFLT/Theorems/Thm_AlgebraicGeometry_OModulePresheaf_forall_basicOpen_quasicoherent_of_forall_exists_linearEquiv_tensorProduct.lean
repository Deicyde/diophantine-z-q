/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct
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
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.OModulePresheaf.forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct
    {A : Type u} [CommRing A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))
    {V' : Scheme.{u}} (p : V' ⟶ P)
    (F : ℕ → OModulePresheaf q) (F' : ℕ → OModulePresheaf (p ≫ q))
    (η : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U₀.1 →
      ((F k).obj U₀.1 →ₗ[A] (F' k).obj V.1))
    (hηs : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U₀.1) (a : Γ(P, U₀.1))
      (x : (F k).obj U₀.1), η k U₀ V h (a • x) = (p.appLE U₀.1 V.1 h).hom a • η k U₀ V h x)
    (hηV : ∀ (k : ℕ) (U₀ : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U₀.1)
      (h₂ : V₂.1 ≤ p ⁻¹ᵁ U₀.1) (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U₀.1),
      (F' k).res hV (η k U₀ V₂ h₂ x) = η k U₀ V₁ h₁ x)
    (hβ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U₀.1),
      letI := (p.appLE U₀.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U₀.1)] (F k).obj U₀.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
        ∀ x : (F k).obj U₀.1, β (1 ⊗ₜ x) = η k U₀ V h x)
    (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U₀.1) (f : Γ(V', V.1)) :
    (∀ x : (F' k).obj (V'.basicOpen f), ∃ (n : ℕ) (y : (F' k).obj V.1),
        (F' k).res (V'.basicOpen_le f) y = (V'.presheaf.map (homOfLE (V'.basicOpen_le f)).op).hom (f ^ n) • x) ∧
    (∀ y : (F' k).obj V.1, (F' k).res (V'.basicOpen_le f) y = 0 → ∃ n : ℕ, (f ^ n : Γ(V', V.1)) • y = 0) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct.solution

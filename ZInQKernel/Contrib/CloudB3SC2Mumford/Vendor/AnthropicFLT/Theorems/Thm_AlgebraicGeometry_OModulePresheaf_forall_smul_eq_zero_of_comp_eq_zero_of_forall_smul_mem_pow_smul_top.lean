/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_comp_eq_zero_of_forall_smul_mem_pow_smul_top
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_comp_eq_zero_of_forall_smul_mem_pow_smul_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_of_comp_eq_zero_of_forall_smul_mem_pow_smul_top
    {A : Type u} [CommRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    (F : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (K : ℕ → OModulePresheaf q) (κ : ∀ k, OModulePresheaf.AffHom (K (k + 1)) (K k))
    (hκs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((κ k).app U))
    (hκk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((κ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((K (k + 1)).obj U.1)))
    (j : ∀ k, OModulePresheaf.AffHom (K k) (F k))
    (hjc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (j (k + 1)).app U = (j k).app U ∘ₗ (κ k).app U)
    (hji : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((j (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((K (k + c)).obj U.1)))
    (Ps : ℕ → OModulePresheaf q) (u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k))
    (huj : ∀ (k : ℕ) (U : P.affineOpens), (u k).app U ∘ₗ (j k).app U = 0)
    (𝓙 : P.IdealSheafData) (N : ℕ)
    (hker : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ (k : ℕ) (x : (F (k + c)).obj U.1), (u (k + c)).app U x = 0 →
      ∀ a : Γ(P, U.1), a ∈ 𝓙.ideal U ^ N → a • x ∈ I ^ (k + 1) • (⊤ : Submodule A ((F (k + c)).obj U.1))) :
    ∀ (k : ℕ) (U : P.affineOpens), ∀ a ∈ 𝓙.ideal U ^ N, ∀ y : (K k).obj U.1, a • y = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_comp_eq_zero_of_forall_smul_mem_pow_smul_top.solution

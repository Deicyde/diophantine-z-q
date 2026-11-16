/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top
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
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top
    {A : Type u} [CommRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (K : ℕ → OModulePresheaf q) (hKq : ∀ k, (K k).IsQuasicoherent)
    (κ : ∀ k, OModulePresheaf.AffHom (K (k + 1)) (K k))
    (hκs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((κ k).app U))
    (j : ∀ k, OModulePresheaf.AffHom (K k) (F k))
    (hjc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (j (k + 1)).app U = (j k).app U ∘ₗ (κ k).app U)
    (Ps : ℕ → OModulePresheaf q) (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
    (u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k))
    (huc : ∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (u (k + 1)).app U = (u k).app U ∘ₗ (φ k).app U)
    (huj : ∀ (k : ℕ) (U : P.affineOpens), (u k).app U ∘ₗ (j k).app U = 0)
    (hAR : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((u (k + c)).app U)
        ≤ LinearMap.range ((j (k + c)).app U) ⊔ I ^ (k + 1) • (⊤ : Submodule A ((F (k + c)).obj U.1))) :
    ∃ (E : ℕ → OModulePresheaf q) (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k)),
      (∀ k, (E k).IsCoherent) ∧ (∀ k, (E k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1))) ∧
      ∃ ε : ∀ k, OModulePresheaf.AffHom (F k) (E k),
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), LinearMap.ker ((ε k).app U) = LinearMap.range ((j k).app U)) ∧
      ∃ uE : ∀ k, OModulePresheaf.AffHom (E k) (Ps k),
      (∀ (k : ℕ) (U : P.affineOpens), (uE k).app U ∘ₗ (ε k).app U = (u k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (uE (k + 1)).app U = (uE k).app U ∘ₗ (τ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), LinearMap.range ((uE k).app U) = LinearMap.range ((u k).app U)) ∧
      (∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
        LinearMap.ker ((uE (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((E (k + c)).obj U.1))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top.solution

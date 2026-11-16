/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup
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
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup
    {A : Type u} [CommRing A] (I : Ideal A) {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    {H G : OModulePresheaf q} (hHq : H.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (h : OModulePresheaf.AffHom H G)
    (F : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (ψ : ∀ k, OModulePresheaf.AffHom G (F k))
    (hψs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U))
    (hψk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψ k).app U)
        = LinearMap.range (h.app U) ⊔ I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1)))
    (hψc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) :
    ∃ (G' : OModulePresheaf q) (ρ : OModulePresheaf.AffHom G G')
      (ψ' : ∀ k, OModulePresheaf.AffHom G' (F k)),
      G'.IsCoherent ∧ G'.IsQuasicoherent ∧
      (∀ U : P.affineOpens, Function.Surjective (ρ.app U)) ∧
      (∀ U : P.affineOpens, LinearMap.ker (ρ.app U) = LinearMap.range (h.app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ψ' k).app U ∘ₗ ρ.app U = (ψ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ' k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ' k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ' (k + 1)).app U = (ψ' k).app U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup.solution

/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top
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
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [LocallyOfFiniteType q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (Ps : ℕ → OModulePresheaf q) (hPsc : ∀ k, (Ps k).IsCoherent) (hPsq : ∀ k, (Ps k).IsQuasicoherent)
    (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
    (hπs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((π k).app U))
    (hπk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((π k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + 1)).obj U.1)))
    (u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k))
    (huc : ∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (u (k + 1)).app U = (u k).app U ∘ₗ (φ k).app U) :
    ∃ (L : ℕ → OModulePresheaf q) (ι : ∀ n, OModulePresheaf.AffHom (L n) (F n))
      (lam : ∀ n, OModulePresheaf.AffHom (L (n + 1)) (L n)),
      (∀ n, (L n).IsCoherent) ∧ (∀ n, (L n).IsQuasicoherent) ∧
      (∀ (n : ℕ) (U : P.affineOpens), Function.Injective ((ι n).app U)) ∧
      (∀ (n : ℕ) (U : P.affineOpens), Function.Surjective ((lam n).app U)) ∧
      (∀ (n : ℕ) (U : P.affineOpens), (ι n).app U ∘ₗ (lam n).app U = (φ n).app U ∘ₗ (ι (n + 1)).app U) ∧
      (∀ (n : ℕ) (U : P.affineOpens), (u n).app U ∘ₗ (ι n).app U = 0) ∧
      (∀ U : P.affineOpens, ∃ c : ℕ, ∀ k n : ℕ, k + c ≤ n →
        LinearMap.ker ((u n).app U) ≤ LinearMap.range ((ι n).app U) ⊔ I ^ (k + 1) • (⊤ : Submodule A ((F n).obj U.1)) ∧
        I ^ n • (⊤ : Submodule A ((F n).obj U.1)) ⊓ LinearMap.range ((ι n).app U) ≤ I ^ k • LinearMap.range ((ι n).app U)) ∧
      ((∀ (n : ℕ) (U : P.affineOpens), Function.Surjective ((u n).app U)) →
        ∀ (n : ℕ) (U : P.affineOpens), LinearMap.range ((ι n).app U) = LinearMap.ker ((u n).app U)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.solution

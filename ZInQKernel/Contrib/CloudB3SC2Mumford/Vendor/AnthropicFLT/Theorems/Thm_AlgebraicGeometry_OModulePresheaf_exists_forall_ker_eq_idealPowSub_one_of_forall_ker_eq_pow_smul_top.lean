/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top
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
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [LocallyOfFiniteType q] (𝓙 : P.IdealSheafData)
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) :
    ∃ (Q : ℕ → OModulePresheaf q) (τ : ∀ k, OModulePresheaf.AffHom (Q (k + 1)) (Q k))
      (ε : ∀ k, OModulePresheaf.AffHom (F k) (Q k)),
      (∀ k, (Q k).IsCoherent) ∧ (∀ k, (Q k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Q (k + 1)).obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ε k).app U) = OModulePresheaf.idealPowSub q 𝓙 (F k) 1 U.1) ∧
      (∀ k, OModulePresheaf.IdealAnnihilates q 𝓙 (Q k)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.solution

/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DeligneSerre_exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen (git blob 6863829069026bff405f18c82656f7906a481c53, sha256 ad1e17cc067e9fa9d180bb6888f2389347040965c8419da3c882a27f230e0d82).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DeligneSerre_exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ∃ R : Subalgebra ℤ ℂ, Module.Finite ℤ R ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N → ModularFormClass.qCoeff f p ∈ R) ∧
      ∀ η : ℝ, 0 < η → ∃ (Y : Finset ℂ) (X : Set ℕ),
        (∀ δ : ℝ, 0 < δ → ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
          ∑' p : {p : ℕ // p.Prime ∧ p ∈ X}, ((p : ℕ) : ℝ) ^ (-s) ≤
            (η + δ) * Real.log (1 / (s - 1))) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N → p ∉ X → ModularFormClass.qCoeff f p ∈ Y := by
  revert N ε f hf₁ hT
  exact @_root_.P2MW.S_DeligneSerre_exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen.solution
